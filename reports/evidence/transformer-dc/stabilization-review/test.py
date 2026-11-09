"""Independent numerical checks of paired backward shifts and their schedule.

This diagnostic does not certify floating-point error bounds or the ViT runner.
"""

from __future__ import annotations

import hashlib
import json
import platform
import sys
from pathlib import Path

import torch


torch.set_default_dtype(torch.float64)
torch.set_num_threads(1)
ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
CHECKS: list[dict] = []


def record(name: str, actual: torch.Tensor, expected: torch.Tensor,
           tolerance: float = 2e-12) -> None:
    error = float((actual - expected).abs().max().detach())
    assert torch.isfinite(actual).all(), name
    assert error <= tolerance, (name, error)
    CHECKS.append({"name": name, "max_absolute_error": error,
                   "tolerance": tolerance, "passed": True})


def shift(s: torch.Tensor, alpha: float) -> torch.Tensor:
    """The literal shiftPair in formalization/StabilizedBackward.lean."""
    n = s.numel() // 2
    common = s[:n] + s[n:]
    return torch.cat((s[:n] - alpha * common, s[n:] - alpha * common))


def unified(s: torch.Tensor) -> torch.Tensor:
    n = s.numel() // 2
    return (s[:n] - s[n:]) / 2


def affine_pair_matrix(weight: torch.Tensor) -> torch.Tensor:
    positive, negative = weight.clamp_min(0), (-weight).clamp_min(0)
    return torch.cat((torch.cat((positive, negative), 1),
                      torch.cat((negative, positive), 1)), 0)


def gate_pair_matrix(active: torch.Tensor) -> torch.Tensor:
    yes = torch.diag(active.to(torch.float64))
    no = torch.eye(len(active)) - yes
    return torch.cat((torch.cat((yes, no), 1),
                      torch.cat((torch.zeros_like(yes), torch.eye(len(active))), 1)), 0)


def mlp_case(depth: int, alphas: list[float], seed: int) -> dict:
    gen = torch.Generator().manual_seed(seed)
    widths = [3] + [4 + (i % 2) for i in range(depth)]
    x = torch.tensor([0.2, -0.7, 1.3])
    ordinary = x
    original_jacobian = torch.eye(3)
    matrices, affine, gates = [], [], []
    for layer in range(depth):
        w = torch.randn(widths[layer + 1], widths[layer], generator=gen) / 2
        b = torch.randn(widths[layer + 1], generator=gen)
        z = w @ ordinary + b
        assert (z.abs() > 1e-5).all()
        active = z > 0
        ordinary = z.clamp_min(0)
        a, g = affine_pair_matrix(w), gate_pair_matrix(active)
        matrices.append(g @ a)
        affine.append(a)
        gates.append(g)
        original_jacobian = torch.diag(active.to(torch.float64)) @ w @ original_jacobian
    row = torch.linspace(-0.6, 1.1, widths[-1])
    formal_results, wrong_results = [], []
    for positive_head in (True, False):
        zeros = torch.zeros_like(row)
        source = torch.cat((row, zeros) if positive_head else (zeros, row))

        # Exact recursion: shift output seed; pull then shift every input boundary.
        formal = shift(source, alphas[-1])
        for l in reversed(range(depth)):
            formal = shift(matrices[l].T @ formal, alphas[l])

        # Equivalent placement: shift once at each logical block's output before pull.
        before_pull = source
        for l in reversed(range(depth)):
            before_pull = matrices[l].T @ shift(before_pull, alphas[l + 1])
        before_pull = shift(before_pull, alphas[0])

        # Affine + gate lowered to two nodes, but alpha remains at the block boundary.
        lowered = source
        for l in reversed(range(depth)):
            lowered = gates[l].T @ shift(lowered, alphas[l + 1])
            lowered = affine[l].T @ lowered
        lowered = shift(lowered, alphas[0])

        # Deliberately different schedule: an extra shift at every affine node.
        wrong = source
        for l in reversed(range(depth)):
            wrong = gates[l].T @ shift(wrong, alphas[l + 1])
            wrong = affine[l].T @ shift(wrong, alphas[l + 1])
        wrong = shift(wrong, alphas[0])

        prefix = f"depth{depth}_seed{seed}_head{int(positive_head)}"
        record(prefix + "_output_adjoint_schedule", before_pull, formal)
        record(prefix + "_lowered_affine_relu_schedule", lowered, formal)
        formal_results.append(formal)
        wrong_results.append(wrong)
    recovered = unified(formal_results[0]) - unified(formal_results[1])
    record(f"depth{depth}_seed{seed}_gradient_recovery",
           recovered, row @ original_jacobian)
    if all(alpha == 0.5 for alpha in alphas):
        record(f"depth{depth}_seed{seed}_half_shift_positive_control",
               unified(formal_results[0]), (row @ original_jacobian) / 2)
        record(f"depth{depth}_seed{seed}_half_shift_negative_control",
               unified(formal_results[1]), -(row @ original_jacobian) / 2)
    return {"depth": depth, "seed": seed, "alphas": alphas,
            "wrong_extra_affine_shift_changes_positive_unified_by": float(
                (unified(wrong_results[0]) - unified(formal_results[0])).abs().max())}


def zero_lift() -> dict:
    x = torch.tensor([-1.0, 0.0, 2.0], requires_grad=True)
    clamp_diff = x.clamp_min(0) - (-x).clamp_min(0)
    relu_diff = torch.relu(x) - torch.relu(-x)
    p = x / 2 + x.detach().abs() / 2
    n = -x / 2 + x.detach().abs() / 2
    grad = torch.autograd.grad((p - n).sum(), x, retain_graph=True)[0]
    record("balanced_lift_forward_including_zero", p - n, x)
    record("balanced_lift_gradient_including_zero", grad, torch.ones_like(x))
    return {"clamp_selected_gradient": torch.autograd.grad(
                clamp_diff.sum(), x, retain_graph=True)[0].tolist(),
            "relu_selected_gradient": torch.autograd.grad(relu_diff.sum(), x)[0].tolist(),
            "balanced_straight_through_gradient": grad.tolist()}


def product_shift() -> dict:
    v = torch.tensor([0.3, 0.1, 0.7, 0.2], requires_grad=True)
    def positive(v: torch.Tensor) -> torch.Tensor:
        a, b, c, d = v
        return ((a + c).square() + (b + d).square()) / 2
    def negative(v: torch.Tensor) -> torch.Tensor:
        a, b, c, d = v
        return ((a + d).square() + (b + c).square()) / 2
    translated = v + torch.tensor([0.4, 0.4, 0.0, 0.0])
    gp = torch.autograd.grad(positive(v), v, retain_graph=True)[0]
    gps = torch.autograd.grad(positive(translated), v, retain_graph=True)[0]
    record("product_common_shift_preserves_difference",
           positive(translated) - negative(translated), positive(v) - negative(v))
    assert float((gp - gps).abs().max()) > 0.1
    return {"unshifted_positive_gradient": gp.tolist(),
            "shifted_positive_gradient": gps.tolist(),
            "meaning": "A fixed common stream shift changes product head derivatives."}


def relu_tie() -> dict:
    x = torch.tensor(0.0, requires_grad=True)
    p = x / 2 + x.detach().abs() / 2
    n = -x / 2 + x.detach().abs() / 2
    maximum_difference = torch.maximum(p, n) - n
    native = torch.relu(x)
    raw_grad = torch.autograd.grad(maximum_difference, x, retain_graph=True)[0]
    native_grad = torch.autograd.grad(native, x, retain_graph=True)[0]
    selected_positive = torch.where(p - n > 0, p, n)
    selected_grad = torch.autograd.grad(selected_positive - n, x)[0]
    record("relu_selected_gate_tie_matches_native", selected_grad, native_grad)
    assert float((raw_grad - native_grad).abs()) == 0.5
    return {"maximum_minus_negative_selected_gradient": float(raw_grad),
            "native_relu_selected_gradient": float(native_grad),
            "explicit_inactive_tie_selected_gradient": float(selected_grad),
            "meaning": "Equivalent nonsmooth formulas need matched backward tie conventions."}


def nonlinear_chain() -> list[dict]:
    results = []
    for lam in (1.0, 0.8, 0.2, 0.0):
        x = torch.tensor([0.3, -0.7], requires_grad=True)
        a = x / 2 + x.detach().abs() / 2
        b = -x / 2 + x.detach().abs() / 2
        P = ((a[0] + a[1]).square() + (b[0] + b[1]).square()) / 2
        Q = ((a[0] + b[1]).square() + (b[0] + a[1]).square()) / 2
        d = (a[0] - b[0]) * (a[1] - b[1])
        common = (P + Q) / 2
        proxy = lam * (common - common.detach()) + d.detach().abs() / 2
        u, v = proxy + d / 2, proxy - d / 2
        z = u - v
        d = z * torch.sigmoid(z)
        common = 2 * torch.nn.functional.softplus(z) + 2 * v - d / 2
        proxy = lam * (common - common.detach()) + d.detach().abs() / 2
        p, n = proxy + d / 2, proxy - d / 2
        gp = torch.autograd.grad(p, x, retain_graph=True)[0]
        gn = torch.autograd.grad(n, x, retain_graph=True)[0]
        ref = x.prod() * torch.sigmoid(x.prod())
        gr = torch.autograd.grad(ref, x)[0]
        record(f"product_swish_lambda{lam}_forward", p - n, ref)
        record(f"product_swish_lambda{lam}_gradient", gp - gn, gr)
        if lam == 0:
            record("product_swish_half_shift_control", gp, gr / 2)
        results.append({"lambda": lam, "positive_gradient": gp.tolist(),
                        "negative_gradient": gn.tolist()})
    return results


def unequal_seed_damping() -> dict:
    # P is an exact lift of the scalar derivative J=1.
    P = torch.tensor([[3.0, 1.0], [2.0, 2.0]])
    plus = P.T @ shift(torch.tensor([1.0, 0.0]), (1 - 1 / 3) / 2)
    minus = P.T @ shift(torch.tensor([0.0, 1.0]), (1 - 1 / 2) / 2)
    actual = float((unified(plus) - unified(minus)).item())
    assert abs(actual - 1.0) > 1e-3
    return {"true_derivative": 1.0, "recovered_with_different_seed_damping": actual,
            "meaning": "Separate head passes must use the same forward-fixed shift schedule."}


def main() -> None:
    cases = []
    for depth in (0, 1, 2, 4):
        for index, base in enumerate((0.0, 0.2, 0.4, 0.5)):
            alpha = [base] * (depth + 1)
            cases.append(mlp_case(depth, alpha, 37 + index))
    cases.append(mlp_case(3, [0.05, 0.15, 0.3, 0.45], 47))
    assert any(case["wrong_extra_affine_shift_changes_positive_unified_by"] > 1e-4
               for case in cases)
    zero = zero_lift()
    product = product_shift()
    tie = relu_tie()
    nonlinear = nonlinear_chain()
    unequal = unequal_seed_damping()
    bound = ROOT / 'formalization/HiddenMonotonicity/StabilizedBackward.lean'
    result = {"status": "passed", "scope": "Independent mathematical audit and finite float64 diagnostics; no ViT or numerical error-bound certificate.",
              "environment": {"python": platform.python_version(), "torch": torch.__version__,
                              "device": "cpu", "dtype": "float64"},
              "test_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "formal_schedule_source": str(bound.relative_to(ROOT)),
              "formal_schedule_sha256": hashlib.sha256(bound.read_bytes()).hexdigest(),
              "checks_passed": len(CHECKS), "checks": CHECKS, "mlp_schedules": cases,
              "zero_lift": zero, "product_translation_counterexample": product,
              "relu_tie_convention": tie,
              "product_swish_chain": nonlinear, "seed_dependent_counterexample": unequal,
              "interpretation": "Matched boundary schedules recover the formal MLP recurrence. Extra shifts at affine/layout nodes define a different attribution. Detached recentering and backward shifts preserve the signed model derivative but do not preserve the original globally convex head functions or their gradients."}
    (OUT / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({"status": "passed", "checks": len(CHECKS), "output": str(OUT / 'results.json')}))


if __name__ == '__main__':
    main()
