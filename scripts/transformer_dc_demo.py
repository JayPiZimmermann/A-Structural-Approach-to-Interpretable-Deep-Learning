#!/usr/bin/env python3
"""CPU diagnostics for the constructive convex-stream Transformer decomposition.

Run with a Python environment containing PyTorch:
    python scripts/transformer_dc_demo.py --output reports/evidence/transformer-dc/numeric.json

The mathematical identities are exact over the reals. These diagnostics deliberately
evaluate the unrecentered stream formulas in float64, including ill-conditioned
cases. They do not certify convexity, reproduce an attribution experiment, or
establish a numerically stable Transformer implementation.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
import platform
import sys
from typing import Callable

import torch
from torch import Tensor
from torch.nn import functional as F


DTYPE = torch.float64


@dataclass(frozen=True)
class Pair:
    positive: Tensor
    negative: Tensor

    @property
    def difference(self) -> Tensor:
        return self.positive - self.negative

    def mean(self, dim: int, keepdim: bool = False) -> Pair:
        return Pair(self.positive.mean(dim, keepdim=keepdim),
                    self.negative.mean(dim, keepdim=keepdim))

    def transpose(self, first: int, second: int) -> Pair:
        return Pair(self.positive.transpose(first, second),
                    self.negative.transpose(first, second))


def lift(value: Tensor, common_offset: float = 0.0) -> Pair:
    if common_offset < 0:
        raise ValueError("The common offset must be nonnegative.")
    return Pair(value.clamp_min(0) + common_offset,
                (-value).clamp_min(0) + common_offset)


def add(left: Pair, right: Pair) -> Pair:
    return Pair(left.positive + right.positive, left.negative + right.negative)


def scale(value: Pair, coefficient: float) -> Pair:
    if coefficient >= 0:
        return Pair(coefficient * value.positive, coefficient * value.negative)
    return Pair(-coefficient * value.negative, -coefficient * value.positive)


def affine(value: Pair, weight: Tensor, bias: Tensor | None = None) -> Pair:
    """A last-axis affine map using the PyTorch [out, in] weight convention."""
    positive_weight, negative_weight = weight.clamp_min(0), (-weight).clamp_min(0)
    positive = F.linear(value.positive, positive_weight) + F.linear(value.negative, negative_weight)
    negative = F.linear(value.positive, negative_weight) + F.linear(value.negative, positive_weight)
    if bias is not None:
        positive = positive + bias.clamp_min(0)
        negative = negative + (-bias).clamp_min(0)
    return Pair(positive, negative)


def product(left: Pair, right: Pair) -> Pair:
    """Polarization; every squared sum is nonnegative before squaring."""
    a, b, c, d = left.positive, left.negative, right.positive, right.negative
    return Pair(((a + c).square() + (b + d).square()) / 2,
                ((a + d).square() + (b + c).square()) / 2)


def matrix_product(left: Pair, right: Pair) -> Pair:
    terms = product(Pair(left.positive.unsqueeze(-1), left.negative.unsqueeze(-1)),
                    Pair(right.positive.unsqueeze(-3), right.negative.unsqueeze(-3)))
    return Pair(terms.positive.sum(-2), terms.negative.sum(-2))


def masked_softmax(value: Pair, allowed: Tensor) -> Pair:
    """Row-wise softmax on a fixed nonempty support, with zero masked outputs."""
    if allowed.dtype != torch.bool or allowed.shape != value.positive.shape:
        raise ValueError("The fixed mask must be boolean and match the logits.")
    if value.positive.ndim != 2 or not bool(allowed.any(-1).all()):
        raise ValueError("Every softmax row must have a nonempty allowed support.")
    positive_rows, negative_rows = [], []
    for x, y, support in zip(value.positive, value.negative, allowed):
        z = x[support] - y[support]
        dimension = z.numel()
        probability = torch.softmax(z, -1)
        common = (torch.logsumexp(z, -1) + y[support].sum()
                  - math.log(dimension) + 1.0 / dimension) / 2
        positive_rows.append(torch.zeros_like(x).masked_scatter(support, common + probability / 2))
        negative_rows.append(torch.zeros_like(y).masked_scatter(support, common - probability / 2))
    return Pair(torch.stack(positive_rows), torch.stack(negative_rows))


def gelu(value: Pair) -> Pair:
    z = value.difference
    cdf = (1 + torch.erf(z / math.sqrt(2))) / 2
    density = torch.exp(-z.square() / 2) / math.sqrt(2 * math.pi)
    return Pair(2 * (z * cdf + density) + 2 * value.negative,
                z * cdf + 2 * density + 2 * value.negative)


def reciprocal_sqrt(value: Pair, epsilon: float) -> Pair:
    if epsilon <= 0:
        raise ValueError("LayerNorm epsilon must be strictly positive.")
    slope = 1 / (2 * epsilon ** 1.5)
    z = value.difference
    extension = torch.where(z >= 0, torch.rsqrt(epsilon + z.clamp_min(0)),
                            epsilon ** -0.5 - slope * z)
    return Pair(extension + slope * value.positive, slope * value.positive)


def scalar(value: Tensor | float) -> float | str:
    result = float(value)
    return result if math.isfinite(result) else str(result)


def observation(value: Pair, reference: Tensor) -> dict:
    error = (value.difference - reference).abs()
    magnitude = torch.maximum(value.positive.abs(), value.negative.abs()).max()
    reference_scale = reference.abs().max()
    return {
        "max_absolute_error": scalar(error.max()),
        "max_relative_error_scale_floor_1": scalar(error.max() / reference_scale.clamp_min(1)),
        "max_stream_magnitude": scalar(magnitude),
        "stream_to_output_scale_floor_1": scalar(magnitude / reference_scale.clamp_min(1)),
        "min_stream_value": scalar(torch.minimum(value.positive, value.negative).min()),
        "min_recovered_value": scalar(value.difference.min()),
        "all_finite": bool(torch.isfinite(value.positive).all() and
                           torch.isfinite(value.negative).all() and torch.isfinite(error).all()),
    }


def layer_norm(value: Pair, reference: Tensor, gamma: Tensor, beta: Tensor,
               epsilon: float, trace: dict, name: str) -> tuple[Pair, Tensor]:
    width = value.positive.shape[-1]
    centering = torch.eye(width, dtype=DTYPE) - torch.ones((width, width), dtype=DTYPE) / width
    centered = affine(value, centering)
    reference_centered = reference - reference.mean(-1, keepdim=True)
    trace[name + ".centered"] = observation(centered, reference_centered)
    variance = product(centered, centered).mean(-1, keepdim=True)
    reference_variance = reference_centered.square().mean(-1, keepdim=True)
    trace[name + ".variance"] = observation(variance, reference_variance)
    inverse = reciprocal_sqrt(variance, epsilon)
    reference_inverse = torch.rsqrt(reference_variance + epsilon)
    trace[name + ".inverse_sqrt"] = observation(inverse, reference_inverse)
    normalized = product(centered, inverse)
    result = affine(normalized, torch.diag(gamma), beta)
    reference_result = F.layer_norm(reference, (width,), gamma, beta, epsilon)
    trace[name] = observation(result, reference_result)
    return result, reference_result


def parameters(generator: torch.Generator, width: int, hidden: int,
               weight_scale: float) -> dict[str, Tensor]:
    def random(*shape: int) -> Tensor:
        return torch.randn(*shape, dtype=DTYPE, generator=generator) * weight_scale

    result = {name: random(width, width) for name in ("q", "k", "v", "o")}
    result.update({name + "b": random(width) for name in ("q", "k", "v", "o")})
    result.update({"w1": random(hidden, width), "b1": random(hidden),
                   "w2": random(width, hidden), "b2": random(width),
                   "head": random(2, width), "head_bias": torch.tensor([-0.1, 0.2], dtype=DTYPE)})
    result.update({"gamma1": torch.tensor([1.0, -0.75, 0.5], dtype=DTYPE),
                   "beta1": random(width), "gamma2": torch.tensor([-0.8, 1.1, 0.6], dtype=DTYPE),
                   "beta2": random(width)})
    return result


def transformer_case(epsilon: float, weight_scale: float, input_scale: float,
                     common_offset: float = 0, seed: int = 23) -> dict:
    generator = torch.Generator().manual_seed(seed)
    tokens, width, hidden = 3, 3, 4
    x = torch.randn(tokens, width, dtype=DTYPE, generator=generator) * input_scale
    weights = parameters(generator, width, hidden, weight_scale)
    value = lift(x, common_offset)
    trace = {"input": observation(value, x)}
    q, k, v = [affine(value, weights[name], weights[name + "b"]) for name in ("q", "k", "v")]
    qr, kr, vr = [F.linear(x, weights[name], weights[name + "b"]) for name in ("q", "k", "v")]
    for name, split, reference in zip(("query", "key", "value"), (q, k, v), (qr, kr, vr)):
        trace[name] = observation(split, reference)
    logits = scale(matrix_product(q, k.transpose(-1, -2)), width ** -0.5)
    reference_logits = qr @ kr.T / math.sqrt(width)
    trace["attention_logits"] = observation(logits, reference_logits)
    allowed = torch.ones((tokens, tokens), dtype=torch.bool).tril()
    probability = masked_softmax(logits, allowed)
    reference_probability = torch.softmax(reference_logits.masked_fill(~allowed, -torch.inf), -1)
    trace["attention_probability"] = observation(probability, reference_probability)
    attended = matrix_product(probability, v)
    reference_attended = reference_probability @ vr
    trace["attention_values"] = observation(attended, reference_attended)
    residual = add(value, affine(attended, weights["o"], weights["ob"]))
    reference_residual = x + F.linear(reference_attended, weights["o"], weights["ob"])
    trace["attention_residual"] = observation(residual, reference_residual)
    norm1, norm1r = layer_norm(residual, reference_residual, weights["gamma1"], weights["beta1"],
                              epsilon, trace, "norm1")
    hidden_pair = affine(norm1, weights["w1"], weights["b1"])
    hidden_reference = F.linear(norm1r, weights["w1"], weights["b1"])
    activated = gelu(hidden_pair)
    activated_reference = F.gelu(hidden_reference, approximate="none")
    trace["gelu"] = observation(activated, activated_reference)
    residual2 = add(norm1, affine(activated, weights["w2"], weights["b2"]))
    residual2r = norm1r + F.linear(activated_reference, weights["w2"], weights["b2"])
    trace["mlp_residual"] = observation(residual2, residual2r)
    norm2, norm2r = layer_norm(residual2, residual2r, weights["gamma2"], weights["beta2"],
                              epsilon, trace, "norm2")
    output = affine(norm2.mean(0), weights["head"], weights["head_bias"])
    reference_output = F.linear(norm2r.mean(0), weights["head"], weights["head_bias"])
    trace["signed_logits"] = observation(output, reference_output)
    return {"epsilon": epsilon, "weight_scale": weight_scale, "input_scale": input_scale,
            "common_input_offset": common_offset, "seed": seed, "stages": trace,
            "reference_logits": [scalar(x) for x in reference_output],
            "recovered_logits": [scalar(x) for x in output.difference]}


def primitive_checks() -> dict:
    generator = torch.Generator().manual_seed(91)
    maximum_errors: dict[str, float] = {}
    diagnostics: dict[str, dict] = {}

    def check(name: str, dimension: int, build: Callable[[Tensor], Pair],
              reference: Callable[[Tensor], Tensor], samples: int = 32) -> None:
        errors, convex_excess, monotone_deficit, minima, finite = [], [], [], [], []
        for _ in range(samples):
            a = torch.rand(dimension, dtype=DTYPE, generator=generator)
            b = torch.rand(dimension, dtype=DTYPE, generator=generator)
            increase = torch.rand(dimension, dtype=DTYPE, generator=generator) / 4
            t = torch.rand((), dtype=DTYPE, generator=generator)
            pa, pb, pc, pm = build(a), build(b), build(t * a + (1 - t) * b), build(a + increase)
            expected = reference(a)
            finite.append(bool(torch.isfinite(expected).all()))
            errors.append(float((pa.difference - expected).abs().max()))
            for av, bv, cv, mv in zip((pa.positive, pa.negative), (pb.positive, pb.negative),
                                      (pc.positive, pc.negative), (pm.positive, pm.negative)):
                finite.append(all(bool(torch.isfinite(x).all()) for x in (av, bv, cv, mv)))
                convex_excess.append(float((cv - t * av - (1 - t) * bv).max()))
                monotone_deficit.append(float((av - mv).max()))
                minima.append(float(av.min()))
        maximum_errors[name] = max(errors)
        diagnostics[name] = {"samples": samples, "all_finite": all(finite), "max_identity_error": max(errors),
                             "max_positive_jensen_violation": max(0.0, max(convex_excess)),
                             "max_positive_monotonicity_violation": max(0.0, max(monotone_deficit)),
                             "minimum_stream_value": min(minima)}

    check("product", 4, lambda a: product(Pair(a[0], a[1]), Pair(a[2], a[3])),
          lambda a: (a[0] - a[1]) * (a[2] - a[3]))
    for dimension in (1, 2, 4):
        mask = torch.ones((1, dimension), dtype=torch.bool)
        check(f"softmax_{dimension}", 2 * dimension,
              lambda a, d=dimension, m=mask: masked_softmax(Pair(a[:d][None], a[d:][None]), m),
              lambda a, d=dimension: torch.softmax(a[:d] - a[d:], -1)[None])
    check("gelu", 2, lambda a: gelu(Pair(a[0], a[1])),
          lambda a: F.gelu(a[0] - a[1], approximate="none"))
    epsilon = 0.25
    slope = 1 / (2 * epsilon ** 1.5)
    check("inverse_sqrt_extension", 2, lambda a: reciprocal_sqrt(Pair(a[0], a[1]), epsilon),
          lambda a: torch.where(a[0] >= a[1], torch.rsqrt(epsilon + (a[0] - a[1]).clamp_min(0)),
                                 epsilon ** -0.5 - slope * (a[0] - a[1])))
    rejected = {}
    for name, operation in {
        "empty_softmax_support": lambda: masked_softmax(lift(torch.zeros((1, 2), dtype=DTYPE)),
                                                        torch.zeros((1, 2), dtype=torch.bool)),
        "zero_epsilon": lambda: reciprocal_sqrt(lift(torch.zeros((), dtype=DTYPE)), 0),
        "negative_epsilon": lambda: reciprocal_sqrt(lift(torch.zeros((), dtype=DTYPE)), -1),
        "negative_input_offset": lambda: lift(torch.zeros((), dtype=DTYPE), -1),
    }.items():
        try:
            operation()
        except ValueError:
            rejected[name] = True
        else:
            rejected[name] = False
    passed = all(v < 1e-12 for v in maximum_errors.values()) and all(rejected.values())
    passed = passed and all(v["all_finite"] and v["max_positive_jensen_violation"] < 1e-12 and
                            v["max_positive_monotonicity_violation"] < 1e-12 and
                            v["minimum_stream_value"] > -1e-12 for v in diagnostics.values())
    return {"passed": passed, "diagnostics": diagnostics, "domain_errors_rejected": rejected,
            "scope": "Finite numerical samples; these checks do not prove convexity or monotonicity."}


def zero_variance_checks() -> list[dict]:
    results = []
    value = torch.zeros((2, 3), dtype=DTYPE)
    gamma = torch.tensor([1.0, -0.5, 1.5], dtype=DTYPE)
    beta = torch.tensor([0.25, -0.25, 0.5], dtype=DTYPE)
    for epsilon in (1.0, 1e-5):
        trace = {}
        layer_norm(lift(value), value, gamma, beta, epsilon, trace, "zero_variance_layer_norm")
        results.append({"epsilon": epsilon, "stages": trace})
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    torch.set_num_threads(1)
    primitive = primitive_checks()
    cases = [transformer_case(epsilon, weight, input_scale)
             for epsilon in (1.0, 1e-2, 1e-5)
             for weight in (0.01, 0.1, 0.5)
             for input_scale in (0.1, 1.0)]
    cases.extend(transformer_case(1.0, 0.01, 0.1, offset) for offset in (1.0, 10.0))
    failure_threshold = 1e-8
    for case in cases:
        case["first_stage_exceeding_absolute_error_threshold"] = next(
            (name for name, stage in case["stages"].items()
             if not stage["all_finite"] or stage["max_absolute_error"] > failure_threshold), None)
    failures = sum(not case["stages"]["signed_logits"]["all_finite"] or
                   case["stages"]["signed_logits"]["max_absolute_error"] > failure_threshold
                   for case in cases)
    benign = cases[0]["stages"]["signed_logits"]
    benign_passed = (benign["all_finite"] and
                     isinstance(benign["max_absolute_error"], float) and
                     benign["max_absolute_error"] < 1e-8)
    report = {
        "scope": "Unstabilized arithmetic demonstration, not an attribution benchmark or formal proof.",
        "architecture": "3 tokens, width3, 1 causal attention head, two post-residual LayerNorms, exact Gaussian GELU MLP width4, mean pooling, signed affine 2-logit head",
        "reference": "Independent ordinary PyTorch operations with identical frozen parameters and population-variance LayerNorm.",
        "stream_policy": "No stream recentering, clipping, or reference-score substitution. Negative numerically recovered variances use the stated tangent extension.",
        "environment": {"python": platform.python_version(), "torch": torch.__version__,
                        "device": "cpu", "dtype": str(DTYPE), "threads": torch.get_num_threads()},
        "command": sys.argv,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "primitive_checks": primitive,
        "zero_variance_checks": zero_variance_checks(),
        "benign_transformer_fixture_passed": benign_passed,
        "sweep_summary": {"absolute_error_threshold": failure_threshold, "cases": len(cases),
                          "final_output_failures_at_threshold": failures,
                          "nonfinite_cases": sum(not c["stages"]["signed_logits"]["all_finite"] for c in cases)},
        "cases": cases,
        "interpretation": "Exact real-arithmetic identities do not control floating-point cancellation. All sweep cases are retained, including failures and nonfinite values; a zero exit status checks only the declared primitive and benign fixtures.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False) + "\n")
    print(json.dumps({"primitive_checks_passed": primitive["passed"],
                      "benign_transformer_fixture_passed": benign_passed,
                      "cases": len(cases), "output": str(args.output)}))
    return 0 if primitive["passed"] and benign_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
