#!/usr/bin/env python3
"""Verify campaign CIs against score arrays using the canonical bootstrap.

This helper imports no model code and never changes campaign files. The caller
may persist the returned report and pass its path as ``cache_path`` later; a
cached verification is reused only when every input and implementation hash
still matches. Cache writes belong to the caller, outside the campaign.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
PAPER_CODE = ROOT / "code/playing_backward"
METRICS = {
    "AL": "attribution_localisation", "PG": "pointing_game",
    "TK": "top_k_intersection", "PF5": "pixel_flipping_abs_5pct",
    "PF20": "pixel_flipping_abs_20pct", "Sel": "selectivity",
    "MaxS": "max_sensitivity", "AvgS": "avg_sensitivity",
}


def _need(condition, message):
    if not condition:
        raise ValueError(message)


def _sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _canonical_bootstrap():
    # reproduce.common deliberately imports torch only inside model functions.
    sys.path.insert(0, str(PAPER_CODE))
    from reproduce import bootstrap_ci, common
    _need(Path(bootstrap_ci.__file__).resolve() == PAPER_CODE / "reproduce/bootstrap_ci.py",
          "A different bootstrap implementation is already imported")
    _need(Path(common.__file__).resolve() == PAPER_CODE / "reproduce/common.py",
          "A different common implementation is already imported")
    return bootstrap_ci.BootstrapPlan


def verify_ci_campaign(path: Path, cache_path: Path | None = None) -> dict:
    """Verify all selected-row CI cells, or reuse an input-hash-bound report.

    ``path`` is a campaign directory containing ``test/ci.csv``, its bootstrap
    metadata, and ``test/per_image/*.npz``. Raise ValueError on mismatches.
    Compare mean/lower/upper to the canonical writer's six-significant-digit
    representation, rather than accepting a tolerance broad enough to hide
    stale or fabricated endpoints. No files are written by this function.
    """
    path = Path(path).resolve()
    metadata_path = path / "test/bootstrap_metadata.json"
    ci_path = path / "test/ci.csv"
    metadata = json.loads(metadata_path.read_text())
    for key, expected in {
        "sampling_unit": "image", "n_records": 565, "n_units": 565,
        "n_boot": 10000, "seed": 0, "ci": "percentile_95",
    }.items():
        _need(metadata.get(key) == expected, f"Unexpected bootstrap metadata: {key}")
    labels = metadata["family_rows"]
    _need(labels and len(labels) == len(set(labels)), "Empty or duplicate CI family")
    labels = sorted(labels)
    _need(all(isinstance(label, str) and Path(label).name == label for label in labels),
          "Invalid row label")
    score_paths = {label: path / "test/per_image" / (label + ".npz") for label in labels}
    implementation_paths = [
        Path(__file__).resolve(), PAPER_CODE / "reproduce/bootstrap_ci.py",
        PAPER_CODE / "reproduce/common.py",
    ]
    files = [metadata_path, ci_path, *score_paths.values(), *implementation_paths]
    sources = {str(p): _sha(p) for p in files}
    fingerprint_data = {"sources_sha256": sources, "numpy_version": np.__version__}
    fingerprint = hashlib.sha256(json.dumps(fingerprint_data, sort_keys=True).encode()).hexdigest()
    n_cells = len(labels) * len(METRICS)
    if cache_path is not None and Path(cache_path).exists():
        try:
            cached = json.loads(Path(cache_path).read_text())
            if (cached.get("schema") == 1 and cached.get("verified") is True
                    and cached.get("source_fingerprint") == fingerprint
                    and cached.get("sources_sha256") == sources
                    and cached.get("n_verified_cells") == n_cells
                    and len(cached.get("cells", [])) == n_cells):
                return cached
        except (OSError, ValueError, TypeError):
            pass
    with ci_path.open(newline="") as stream:
        csv_rows = list(csv.DictReader(stream))
    cells = {(row["row"], row["metric"]): row for row in csv_rows}
    expected_cells = {(label, metric) for label in labels for metric in METRICS}
    _need(len(cells) == len(csv_rows), "Duplicate CI row/metric cells")
    _need(set(cells) == expected_cells, "Missing or unexpected CI cells")
    BootstrapPlan = _canonical_bootstrap()
    verified = []
    ids = None
    plan = None
    for label in labels:
        with np.load(score_paths[label], allow_pickle=False) as archive:
            row_ids = archive["image_ids"].astype(str)
            _need(row_ids.shape == (565,) and len(set(row_ids)) == 565,
                  f"{label}: per-image IDs are not 565 unique records")
            if ids is None:
                ids = row_ids
                plan = BootstrapPlan(ids, n_boot=10000, seed=0, clustered=False)
            _need(set(row_ids) == set(ids), f"{label}: per-image ID sets differ")
            positions = {name: index for index, name in enumerate(row_ids)}
            order = [positions[name] for name in ids]
            for metric, key in METRICS.items():
                source_values = np.asarray(archive[key], dtype=float)
                _need(source_values.shape == (565,), f"{label}/{metric}: score shape differs")
                values = source_values[order]
                mean, lo, hi, n = plan.ci(values)
                expected_n = 200 if metric in ("MaxS", "AvgS") else 565
                _need(n == expected_n, f"{label}/{metric}: finite score count differs")
                stored = cells[label, metric]
                _need(int(stored["n"]) == n, f"{label}/{metric}: CI sample count differs")
                expected = {"mean": mean, "lo": lo, "hi": hi}
                for field, value in expected.items():
                    _need(math.isfinite(value), f"{label}/{metric}: nonfinite recomputed {field}")
                    actual = float(stored[field])
                    _need(math.isfinite(actual) and actual == float(f"{value:.6g}"),
                          f"{label}/{metric}: {field} differs from canonical 6g bootstrap output "
                          f"({stored[field]} != {value:.6g})")
                verified.append({"row": label, "metric": metric, "n": n,
                                 **{field: f"{value:.6g}" for field, value in expected.items()}})
    _need(all(_sha(p) == sources[str(p)] for p in files),
          "CI inputs or implementation changed during verification")
    return {
        "schema": 1, "verified": True, "source_fingerprint": fingerprint,
        "sources_sha256": sources, "numpy_version": np.__version__,
        "campaign": str(path), "n_verified_cells": n_cells,
        "n_rows": len(labels), "n_boot": 10000, "seed": 0,
        "sampling_unit": "image", "ci": "percentile_95", "csv_precision": "6g",
        "cells": verified,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("campaign", type=Path)
    parser.add_argument("--cache", type=Path, help="Previously returned report; read only")
    args = parser.parse_args()
    print(json.dumps(verify_ci_campaign(args.campaign, args.cache), indent=2) + "\n", end="")


if __name__ == "__main__":
    main()
