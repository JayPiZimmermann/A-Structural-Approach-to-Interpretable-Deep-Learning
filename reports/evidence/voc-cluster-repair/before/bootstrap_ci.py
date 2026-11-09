#!/usr/bin/env python3
"""Bootstrap confidence intervals and significance tests for test results.

Usage::

    python -m reproduce.bootstrap_ci --results results/test/vit_b16 --n-boot 10000 --seed 0

Reads every row result (``<results>/<row_label>.json``) and its per-image
scores (``<results>/per_image/<row_label>.npz``) and writes

* ``ci.csv`` (row, metric, mean, lo, hi, n): 95% percentile bootstrap CI of
  the mean over images.  The resampled image indices are drawn once and
  shared by all rows (paired resampling); images with a NaN score (failed
  map / metric) are ignored inside each resample.
* ``significance.csv`` (metric, best_row, row, delta, p, p_holm,
  significant): for every metric the best row (by mean, respecting the
  metric direction) is compared with every other row, with the paired
  bootstrap test of ``bwgame.evaluation.stats`` (McNemar's test for the
  binary PG) on the images where both rows have a score; p-values are
  Holm-corrected within the metric.  delta = mean(row) - mean(best).

By default the sweep-only rows (selected_by only ``sweep:*``) are excluded
from the significance family (``--include-sweeps`` adds them); CIs are
computed for every row.
"""
from __future__ import annotations

import argparse
import csv
import logging
import sys
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from reproduce.common import load_per_image, load_row_results, setup_logging

logger = logging.getLogger("reproduce.bootstrap_ci")

METRICS = ("AL", "PG", "TK", "PF5", "PF20", "Sel", "MaxS", "AvgS")
ALPHA = 0.05


def is_sweep_only(obj: Dict) -> bool:
    roles = obj.get("selected_by", [])
    return bool(roles) and all(r.startswith("sweep:") for r in roles)


def load_scores(results_dir: Path, metrics: Sequence[str] = METRICS):
    """Return (rows, image_ids, scores) with scores[label][metric] -> (N,) array.

    All rows are aligned to the image ids of the first row; images missing in
    a row become NaN.  Metrics a row does not have are omitted for that row.
    """
    import numpy as np
    from bwgame.evaluation.metric_spec import SHORT_TO_METRIC

    rows = load_row_results(results_dir)
    image_ids: Optional[np.ndarray] = None
    scores: Dict[str, Dict[str, "np.ndarray"]] = {}
    for label in sorted(rows):
        pi = load_per_image(results_dir, label)
        if pi is None:
            logger.warning("%s: per-image file missing; row skipped", label)
            continue
        ids = pi["image_ids"].astype(str)
        if image_ids is None:
            image_ids = ids
        pos = {i: k for k, i in enumerate(ids)}
        if not np.array_equal(ids, image_ids):
            logger.warning("%s: image ids differ from the other rows; aligning by id", label)
        scores[label] = {}
        for s in metrics:
            name = SHORT_TO_METRIC[s]
            if name not in pi:
                continue
            v = np.asarray(pi[name], dtype=float)
            aligned = np.array([v[pos[i]] if i in pos else np.nan for i in image_ids])
            scores[label][s] = aligned
    return rows, (image_ids if image_ids is not None else np.array([])), scores


def boot_indices(n: int, n_boot: int, seed: int):
    import numpy as np
    rng = np.random.RandomState(seed)
    return rng.randint(0, n, size=(n_boot, n)).astype(np.int32)


def ci_from_indices(values, idx) -> Tuple[float, float, float, int]:
    """(mean, lo, hi, n) with a 95% percentile bootstrap over ``idx``."""
    import numpy as np
    v = np.asarray(values, dtype=float)
    fin = np.isfinite(v)
    n = int(fin.sum())
    if n == 0:
        return float("nan"), float("nan"), float("nan"), 0
    mean = float(v[fin].mean())
    if n < 2:
        return mean, float("nan"), float("nan"), n
    s = np.where(fin, v, 0.0)[idx].sum(axis=1)
    c = fin.astype(float)[idx].sum(axis=1)
    with np.errstate(invalid="ignore", divide="ignore"):
        boot = s / c
    boot = boot[np.isfinite(boot)]
    lo, hi = np.percentile(boot, [2.5, 97.5])
    return mean, float(lo), float(hi), n


def compare(a, b, metric: str, n_boot: int, seed: int) -> Tuple[float, float, int]:
    """(delta = mean(a) - mean(b), two-sided p, n) on images where both are finite."""
    import numpy as np
    from bwgame.evaluation.stats import mcnemar_test, paired_bootstrap_test
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    m = np.isfinite(a) & np.isfinite(b)
    n = int(m.sum())
    if n < 2:
        return float("nan"), float("nan"), n
    delta = float(a[m].mean() - b[m].mean())
    if np.array_equal(a[m], b[m]):
        return delta, 1.0, n
    if metric == "PG":
        p = mcnemar_test(a[m] > 0.5, b[m] > 0.5)["p_value"]
    else:
        p = paired_bootstrap_test(a[m], b[m], n_bootstrap=n_boot, seed=seed)["p_value"]
    return delta, float(p), n


def best_label(means: Dict[str, float], metric: str) -> Optional[str]:
    import math
    from bwgame.evaluation.metric_spec import metric_direction
    cand = [(l, v) for l, v in means.items() if v is not None and math.isfinite(v)]
    if not cand:
        return None
    sign = -1.0 if metric_direction(metric) == "max" else 1.0
    return min(cand, key=lambda t: (sign * t[1], t[0]))[0]


def significance_vs_best(scores: Dict[str, Dict], labels: Sequence[str], metric: str,
                         n_boot: int, seed: int) -> List[Dict]:
    """Test every row in ``labels`` against the best of them; Holm within the metric."""
    import numpy as np
    from bwgame.evaluation.stats import holm_correction
    have = [l for l in labels if metric in scores.get(l, {})]
    means = {l: float(np.nanmean(scores[l][metric])) if np.isfinite(scores[l][metric]).any() else float("nan")
             for l in have}
    best = best_label(means, metric)
    if best is None:
        return []
    out = []
    for l in have:
        if l == best:
            continue
        delta, p, n = compare(scores[l][metric], scores[best][metric], metric, n_boot, seed)
        out.append({"metric": metric, "best_row": best, "row": l, "delta": delta, "p": p, "n": n})
    if out:
        ps = [r["p"] if np.isfinite(r["p"]) else 1.0 for r in out]
        for r, ph in zip(out, holm_correction(ps)):
            r["p_holm"] = float(ph)
            r["significant"] = bool(np.isfinite(r["p"]) and ph < ALPHA)
    return out


def run(results_dir: Path, n_boot: int, seed: int, include_sweeps: bool,
        out_dir: Optional[Path] = None) -> Tuple[Path, Path]:
    results_dir = Path(results_dir)
    out_dir = Path(out_dir or results_dir)
    rows, image_ids, scores = load_scores(results_dir)
    if not scores:
        raise SystemExit(f"No row results with per-image files in {results_dir}")
    n = len(image_ids)
    idx = boot_indices(n, n_boot, seed)
    logger.info("%d rows, %d images, %d bootstrap resamples", len(scores), n, n_boot)

    ci_path = out_dir / "ci.csv"
    out_dir.mkdir(parents=True, exist_ok=True)
    with open(ci_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["row", "metric", "mean", "lo", "hi", "n"])
        for label in sorted(scores):
            for s in METRICS:
                if s not in scores[label]:
                    continue
                mean, lo, hi, k = ci_from_indices(scores[label][s], idx)
                w.writerow([label, s, f"{mean:.6g}", f"{lo:.6g}", f"{hi:.6g}", k])

    family = [l for l in sorted(scores) if include_sweeps or not is_sweep_only(rows[l])]
    sig_path = out_dir / "significance.csv"
    with open(sig_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["metric", "best_row", "row", "delta", "p", "p_holm", "significant"])
        for s in METRICS:
            for r in significance_vs_best(scores, family, s, n_boot, seed):
                w.writerow([r["metric"], r["best_row"], r["row"], f"{r['delta']:.6g}",
                            f"{r['p']:.6g}", f"{r['p_holm']:.6g}", int(r["significant"])])
    logger.info("Wrote %s and %s", ci_path, sig_path)
    return ci_path, sig_path


def main(argv=None) -> None:
    ap = argparse.ArgumentParser(description="Bootstrap CIs and significance tests.")
    ap.add_argument("--results", type=Path, required=True, help="e.g. results/test/vit_b16")
    ap.add_argument("--n-boot", type=int, default=10000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--include-sweeps", action="store_true",
                    help="Include sweep-only rows in the significance family.")
    ap.add_argument("--out-dir", type=Path, default=None, help="Default: the --results directory.")
    args = ap.parse_args(argv)
    setup_logging()
    run(args.results, args.n_boot, args.seed, args.include_sweeps, args.out_dir)


if __name__ == "__main__":
    sys.exit(main())
