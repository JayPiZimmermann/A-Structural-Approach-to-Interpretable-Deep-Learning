#!/usr/bin/env python3
"""Combined-family ViT statistics using the paper's canonical CPU implementation.

The adapter supplies only admitted, fully evaluated rows. Historical Gradient
scores are read from the published (rounded) CSV; its displayed CI is retained by
the caller. Fresh rows must reproduce their campaign CI at canonical precision.
"""
from __future__ import annotations

import csv
import gzip
import hashlib
import json
import math
from itertools import combinations
from pathlib import Path
import sys

import numpy as np
import scipy

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "code/playing_backward"
sys.path.insert(0, str(PAPER))
from reproduce.bootstrap_ci import BootstrapPlan, best_label, significance_vs_best
from bwgame.evaluation.stats import holm_correction
from bwgame.evaluation import metric_spec as _metric_spec

CANONICAL_MODULES = {
    "reproduce.bootstrap_ci": PAPER / "reproduce/bootstrap_ci.py",
    "reproduce.common": PAPER / "reproduce/common.py",
    "bwgame.evaluation.stats": PAPER / "bwgame/evaluation/stats.py",
    "bwgame.evaluation.metric_spec": PAPER / "bwgame/evaluation/metric_spec.py",
}


def _canonical_imports():
    """Refuse modules cached from another checkout before this helper loaded."""
    for name, expected in CANONICAL_MODULES.items():
        actual = Path(sys.modules[name].__file__).resolve()
        if actual != expected.resolve():
            raise ValueError(f"{name} imported from {actual}, expected {expected.resolve()}")

METRIC_KEYS = {
    "AL": "attribution_localisation", "PG": "pointing_game",
    "TK": "top_k_intersection", "PF5": "pixel_flipping_abs_5pct",
    "PF20": "pixel_flipping_abs_20pct", "Sel": "selectivity",
    "MaxS": "max_sensitivity", "AvgS": "avg_sensitivity",
}
N_BOOT, SEED, ALPHA = 10000, 0, 0.05


def _sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _need(condition, message):
    if not condition:
        raise ValueError(message)


def _load(row):
    path = Path(row["source"])
    if row["source_kind"] == "npz":
        with np.load(path, allow_pickle=False) as data:
            ids = data["image_ids"].astype(str).tolist()
            _need(not np.asarray(data["map_failed"]).any(), "failed maps: " + row["row_label"])
            _need(not np.asarray(data["map_is_zero"]).any(), "zero maps: " + row["row_label"])
            scores = {metric: np.asarray(data[key], dtype=float) for metric, key in METRIC_KEYS.items()}
    elif row["source_kind"] == "paper_csv":
        with gzip.open(path, "rt") as stream:
            records = [r for r in csv.DictReader(stream) if r["row_label"] == row["row_label"]]
        ids = [r["image_id"] for r in records]
        scores = {metric: np.asarray([float(r[key]) if r[key] else np.nan for r in records])
                  for metric, key in METRIC_KEYS.items()}
    else:
        raise ValueError("unknown source_kind: " + row["source_kind"])
    _need(len(ids) == len(set(ids)) == 565, "expected 565 unique images: " + row["row_label"])
    return ids, scores


def _published_ci(row):
    if row["source_kind"] != "npz":
        return None, {}
    path = Path(row.get("ci_source", Path(row["source"]).parent.parent / "ci.csv"))
    with path.open() as stream:
        records = [r for r in csv.DictReader(stream) if r["row"] == row["row_label"]]
    _need(len(records) == len(METRIC_KEYS), "published CI row incomplete: " + row["row_label"])
    index = {r["metric"]: r for r in records}
    _need(set(index) == set(METRIC_KEYS), "published CI metric set differs")
    return path, index


def build_statistics(rows, out_path, *, image_ids=None, robustness_ids=None):
    """Write and return auditable CIs, all paired tests and table markers.

    ``rows`` is an ordered list with ``row_label``, ``source`` and
    ``source_kind`` (``npz`` or ``paper_csv``). Optional ``ci_source`` overrides
    a fresh row's adjacent test/ci.csv. The default order is the first NPZ's
    image order. Cache reuse requires identical source, CI and implementation
    hashes, image order, masks, row order and parameters.
    """
    out_path = Path(out_path)
    _canonical_imports()
    _need(bool(rows), "empty significance family")
    labels = [r["row_label"] for r in rows]
    _need(len(labels) == len(set(labels)), "duplicate displayed row in significance family")
    initial_sources = {str(Path(row["source"]).resolve()): _sha(row["source"]) for row in rows}
    loaded = {row["row_label"]: _load(row) for row in rows}
    if image_ids is None:
        first = next((row for row in rows if row["source_kind"] == "npz"), rows[0])
        image_ids = loaded[first["row_label"]][0]
    image_ids = [str(value) for value in image_ids]
    _need(len(image_ids) == len(set(image_ids)) == 565, "reference image IDs must contain 565 unique images")
    scores = {}
    sources = {}
    for source in (Path(__file__), *CANONICAL_MODULES.values()):
        sources[str(source.resolve())] = _sha(source)
    published = {}
    for row in rows:
        label = row["row_label"]
        ids, data = loaded[label]
        _need(set(ids) == set(image_ids), "test image IDs differ: " + label)
        pos = {image_id: index for index, image_id in enumerate(ids)}
        order = [pos[image_id] for image_id in image_ids]
        scores[label] = {metric: values[order] for metric, values in data.items()}
        source = Path(row["source"]).resolve()
        sources[str(source)] = initial_sources[str(source)]
        ci_path, published[label] = _published_ci(row)
        if ci_path:
            sources[str(ci_path.resolve())] = _sha(ci_path)
        for metric, values in scores[label].items():
            _need(values.shape == (565,), "wrong per-image shape")
            valid_ids = [image_id for image_id, ok in zip(image_ids, np.isfinite(values)) if ok]
            if metric in ("MaxS", "AvgS"):
                if robustness_ids is None:
                    robustness_ids = valid_ids
                _need(len(valid_ids) == 200 and set(valid_ids) == set(robustness_ids),
                      "sensitivity subset differs: " + label + "/" + metric)
            else:
                _need(len(valid_ids) == 565, "incomplete metric: " + label + "/" + metric)
            if metric == "PG":
                _need(set(np.unique(values)) <= {0.0, 1.0}, "PG is not binary")
    versions = {"numpy": np.__version__, "scipy": scipy.__version__, "python": sys.version}
    binding = {"sources_sha256": sources, "runtime_versions": versions,
               "family_rows": labels, "image_ids": image_ids,
               "robustness_ids": sorted(robustness_ids), "n_boot": N_BOOT, "seed": SEED, "alpha": ALPHA}
    fingerprint = hashlib.sha256(json.dumps(binding, sort_keys=True).encode()).hexdigest()
    if out_path.exists():
        previous = json.loads(out_path.read_text())
        if previous.get("source_fingerprint") == fingerprint:
            return previous
    plan = BootstrapPlan(image_ids, n_boot=N_BOOT, seed=SEED, clustered=False)
    output = {"schema": 1, "source_fingerprint": fingerprint,
              "source_sha256": sources, "family_rows": labels,
              "metadata": {**plan.metadata(), "alpha": ALPHA, "runtime_versions": versions,
                           "PG_test": "McNemar chi-square with continuity correction (canonical paper implementation)",
                           "sensitivity_n": 200,
                           "CI_scope": "One 565-image bootstrap plan; sensitivity NaNs preserve the fixed 200-image subset.",
                           "historical_gradient": "Paired tests use archived per-image values rounded to approximately six significant digits. The table retains the paper's original Gradient mean and CI cells.",
                           "approx_marker": "Failure to reject a difference from the observed best at Holm-adjusted alpha=.05; not equivalence.",
                           "family_scope": "All displayed unique configurations, including both selection criteria where distinct; all unordered pairs within each metric."},
              "metrics": {}}
    for metric in METRIC_KEYS:
        row_stats = {}
        for label in labels:
            mean, lo, hi, n = plan.ci(scores[label][metric])
            _need(all(math.isfinite(x) for x in (mean, lo, hi)), "nonfinite computed CI")
            row_stats[label] = {"mean": mean, "lo": lo, "hi": hi, "n": n}
            if published[label]:
                original = published[label][metric]
                _need(int(original["n"]) == n, "published CI sample count differs")
                for key, value in (("mean", mean), ("lo", lo), ("hi", hi)):
                    _need(float(original[key]) == float(f"{value:.6g}"),
                          f"published CI does not reproduce: {label}/{metric}/{key}")
        best = best_label({label: stats["mean"] for label, stats in row_stats.items()}, metric)
        pairs = []
        for left, right in combinations(sorted(labels), 2):
            delta, p, n = plan.compare(scores[left][metric], scores[right][metric], metric)
            _need(math.isfinite(p) and 0 <= p <= 1, "invalid paired p-value")
            pairs.append({"left": left, "right": right, "delta_left_minus_right": delta, "p": p, "n": n})
        adjusted = holm_correction([pair["p"] for pair in pairs])
        for pair, ph in zip(pairs, adjusted):
            pair["p_holm"] = float(ph)
            pair["significant"] = bool(ph < ALPHA)
            if best in (pair["left"], pair["right"]):
                label = pair["right"] if pair["left"] == best else pair["left"]
                sign = -1 if pair["left"] == best else 1
                row_stats[label].update({"delta_vs_best": sign * pair["delta_left_minus_right"],
                                         "p_vs_best": pair["p"], "p_vs_best_adjusted": float(ph),
                                         "marker": None if ph < ALPHA else "approx"})
        row_stats[best].update({"marker": "best", "delta_vs_best": 0.0,
                                "p_vs_best": None, "p_vs_best_adjusted": None})
        output["metrics"][metric] = {"best_row": best, "rows": row_stats, "pairs": pairs,
                                     "family_size": len(pairs)}
    # Bind the output to unchanged files even if a producer were writing during the calculation.
    _need(all(_sha(path) == digest for path, digest in sources.items()), "statistics source changed during computation")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    temporary = out_path.with_suffix(out_path.suffix + ".tmp")
    temporary.write_text(json.dumps(output, indent=2, allow_nan=False) + "\n")
    temporary.replace(out_path)
    return output


def self_test():
    """Check null pairing, known discordance and family-wise Holm ordering."""
    _canonical_imports()
    plan = BootstrapPlan([str(i) for i in range(20)], n_boot=10000, seed=0, clustered=False)
    a = np.linspace(-1, 2, 20)
    for metric in ("AL", "PG"):
        values = a if metric == "AL" else (a > 0).astype(float)
        delta, p, n = plan.compare(values, values.copy(), metric)
        _need(delta == 0 and p == 1 and n == 20, "identical paired arrays must have p=1")
    # Eight A-only and two B-only hits imply chi-square statistic (|8-2|-1)^2/10 = 2.5.
    pg_a = np.asarray([1.] * 8 + [0.] * 2 + [1.] * 10)
    pg_b = np.asarray([0.] * 8 + [1.] * 2 + [1.] * 10)
    from scipy.stats import chi2
    delta, p, n = plan.compare(pg_a, pg_b, "PG")
    _need(math.isclose(p, float(chi2.sf(2.5, 1)), rel_tol=1e-14) and n == 20,
          "known McNemar discordance disagrees")
    adjusted = holm_correction([0.04, 0.01, 0.03])
    _need(np.allclose(adjusted, [0.06, 0.03, 0.06]), "Holm correction/order failed")
    synthetic = {"a": {"AL": a}, "b": {"AL": a + .1}, "c": {"AL": a.copy()}}
    canonical = significance_vs_best(synthetic, list(synthetic), "AL", 10000, 0, plan)
    _need(all(r["family_size"] == 3 for r in canonical), "Holm family must include all three unordered pairs")
    return {"identical_pairs": "passed", "known_PG_discordance": "passed",
            "holm_ordering": "passed", "all_unordered_family": "passed"}


if __name__ == "__main__":
    print(json.dumps(self_test(), sort_keys=True))
