#!/usr/bin/env python3
"""Audit the direct LayerNorm DC formula using SymPy and CPU float64 diagnostics.

Run with a Python environment containing SymPy and PyTorch:
    python directLNcheck.py --output directLN-results.json

The polynomial check is exact symbolic arithmetic. Finite derivative samples
diagnose the implementation and do not prove global convexity or monotonicity.
Raw subtraction errors are reported without replacing either stream.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import platform
import sys

import sympy
import torch
from torch.func import hessian, jacrev


def exact_polynomial_check() -> dict:
    radius_squared, perpendicular_squared = sympy.symbols("R v", nonnegative=True)
    r, v = radius_squared, perpendicular_squared
    denominator = 4 * (1 + r) ** 2 * (1 + r * v) ** 2
    numerator = 4 * r * ((3 + (r - 2) * v) ** 2 + 4 * v * (1 - v) * (1 + r) ** 2)
    certificate = (
        9 * (r - 1) ** 2
        + 2 * r * (r - 5) ** 2 * v
        + 3 * r ** 2 * (3 * r ** 2 + 10 * r + 19) * v ** 2
    )
    difference = sympy.expand(sympy.Rational(9, 4) * denominator - numerator - certificate)
    return {
        "passed": difference == 0,
        "exact_expansion_difference": str(difference),
        "certificate": str(certificate),
        "domain": "R >= 0, 0 <= v <= 1; denominator strictly positive",
        "interpretation": (
            "The exact identity certifies that the squared normalized-norm Hessian ratio is at most 9/4. "
            "Nonnegativity of each displayed certificate term gives the analytic bound."
        ),
    }


def components(pair: torch.Tensor, epsilon: float) -> tuple[torch.Tensor, torch.Tensor]:
    dimension = pair.numel() // 2
    value = pair[:dimension] - pair[dimension:]
    centered = value - value.mean()
    denominator = torch.sqrt(epsilon + centered.square().mean())
    return denominator, centered / denominator


def head(pair: torch.Tensor, epsilon: float, coordinate: int, sign: int) -> torch.Tensor:
    dimension = pair.numel() // 2
    a = 3 * math.sqrt(dimension) / (2 * math.sqrt(epsilon))
    k = 5 / (4 * math.sqrt(epsilon))
    denominator, normalized = components(pair, epsilon)
    return (
        (a * (denominator - math.sqrt(epsilon)) + sign * normalized[coordinate]) / 2
        + k * pair.sum()
    )


def sampled_check(dimension: int, epsilon: float, scale: float, seed: int) -> dict:
    generator = torch.Generator(device="cpu").manual_seed(seed)
    pair = torch.randn(2 * dimension, generator=generator, dtype=torch.float64) * scale
    coordinate = seed % dimension
    records = []
    all_finite = True
    for sign in (-1, 1):
        objective = lambda argument: head(argument, epsilon, coordinate, sign)
        gradient = jacrev(objective)(pair)
        curvature = hessian(objective)(pair)
        eigenvalues = torch.linalg.eigvalsh(curvature)
        all_finite &= bool(torch.isfinite(gradient).all() and torch.isfinite(curvature).all())
        gradient_scale = max(1.0, float(gradient.abs().max()))
        curvature_scale = max(1.0, float(eigenvalues.abs().max()))
        records.append({
            "sign": sign,
            "minimum_coordinate_derivative": float(gradient.min()),
            "normalized_monotonicity_violation": max(0.0, -float(gradient.min())) / gradient_scale,
            "minimum_hessian_eigenvalue": float(eigenvalues.min()),
            "hessian_spectral_scale_floor_one": curvature_scale,
            "normalized_psd_violation": max(0.0, -float(eigenvalues.min())) / curvature_scale,
        })
    first, second = (head(pair, epsilon, coordinate, sign) for sign in (1, -1))
    _, normalized = components(pair, epsilon)
    raw_error = float(abs((first - second) - normalized[coordinate]))
    nonnegative_pair = pair.abs()
    quadrant_values = torch.stack([head(nonnegative_pair, epsilon, coordinate, sign) for sign in (-1, 1)])
    all_finite &= bool(torch.isfinite(torch.stack([first, second])).all()
                       and torch.isfinite(quadrant_values).all())
    quadrant_scale = max(1.0, float(quadrant_values.abs().max()))
    return {
        "dimension": dimension,
        "epsilon": epsilon,
        "input_scale": scale,
        "seed": seed,
        "coordinate": coordinate,
        "all_finite": all_finite,
        "heads": records,
        "raw_identity_absolute_error": raw_error,
        "raw_stream_maximum_magnitude": float(torch.stack([first, second]).abs().max()),
        "reference_normalized_component": float(normalized[coordinate]),
        "minimum_nonnegative_orthant_head_value": float(quadrant_values.min()),
        "normalized_nonnegativity_violation": max(0.0, -float(quadrant_values.min())) / quadrant_scale,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    torch.set_num_threads(1)
    polynomial = exact_polynomial_check()
    cases = [
        sampled_check(dimension, epsilon, scale, seed)
        for dimension in (1, 2, 3, 8)
        for epsilon in (1e-5, 0.01, 1.0)
        for scale in (0.0, 1e-4, 1.0, 100.0)
        for seed in (128, 129)
    ]
    tolerance = 1e-10
    derivative_records = [record for case in cases for record in case["heads"]]
    summary = {
        "cases": len(cases),
        "all_finite": all(case["all_finite"] for case in cases),
        "maximum_normalized_psd_violation": max(record["normalized_psd_violation"] for record in derivative_records),
        "maximum_normalized_monotonicity_violation": max(record["normalized_monotonicity_violation"] for record in derivative_records),
        "maximum_normalized_nonnegativity_violation": max(case["normalized_nonnegativity_violation"] for case in cases),
        "maximum_raw_identity_absolute_error": max(case["raw_identity_absolute_error"] for case in cases),
        "maximum_raw_stream_magnitude": max(case["raw_stream_maximum_magnitude"] for case in cases),
        "sampled_structural_tolerance": tolerance,
        "identity_error_is_reported_without_a_pass_threshold": True,
    }
    passed = bool(polynomial["passed"] and summary["all_finite"] and all(
        summary[key] <= tolerance for key in (
            "maximum_normalized_psd_violation",
            "maximum_normalized_monotonicity_violation",
            "maximum_normalized_nonnegativity_violation",
        )
    ))
    report = {
        "status": "pass" if passed else "fail",
        "scope": "Exact polynomial expansion plus finite CPU float64 diagnostics; no Lean proof or numerical-stability certificate.",
        "formula": {
            "domain": "d >= 1, epsilon > 0, globally real doubled inputs; nonnegativity only on the nonnegative orthant",
            "h": "sqrt(epsilon + mean((z - mean(z))^2))",
            "f_i": "(z_i - mean(z)) / h(z)",
            "A": "3 * sqrt(d) / (2 * sqrt(epsilon))",
            "K": "5 / (4 * sqrt(epsilon))",
            "F_i_pm": "(A * (h(p-n) - sqrt(epsilon)) +/- f_i(p-n)) / 2 + K * sum(p+n)",
        },
        "environment": {"python": platform.python_version(), "torch": torch.__version__,
                        "sympy": sympy.__version__, "dtype": "torch.float64", "device": "cpu", "threads": 1},
        "command": sys.argv,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "analytic_certificate": polynomial,
        "summary": summary,
        "cases": cases,
        "limitations": [
            "Finite samples do not establish global convexity or monotonicity; those follow from the analytic argument.",
            "The raw identity subtraction is not stabilized or replaced by a reference value, and its error is retained.",
            "The common-mode row sum still contains 2*d*K; improving epsilon scaling does not guarantee stable repeated composition.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False) + "\n")
    print(json.dumps({"status": report["status"], "polynomial_passed": polynomial["passed"], **summary}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
