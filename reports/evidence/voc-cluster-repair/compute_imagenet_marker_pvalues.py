"""Reproduce the comparisons whose table markers changed after all-pairs Holm."""
from __future__ import annotations

import json
import math
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
REPO = ROOT / "code" / "playing_backward"
sys.path.insert(0, str(REPO))

from bwgame.evaluation.stats import holm_correction
from reproduce.bootstrap_ci import METRICS, is_sweep_only, significance_vs_best
from reproduce.make_tables import ResultSet, _row_name, main_rows


def main():
    evidence = Path(__file__).resolve().parent
    changes = json.loads((evidence / "table_change_review.json").read_text())["marker_changes"]
    groups = defaultdict(list)
    for change in changes:
        groups[change["file"]].append(change)
    results = REPO / "results_summary"
    output, families = [], {}
    for table, table_changes in groups.items():
        model = "vit_b16" if table == "main_vit_tabular.tex" else table.removeprefix("test_").removesuffix("_ci_longtable.tex")
        selection = json.loads((results / "selection" / model / "selected.json").read_text())
        rs = ResultSet(results / "test" / model, selection, None, 10000, 0)
        if table == "main_vit_tabular.tex":
            display_rows = [row for block in main_rows(rs) for row in block]
            names = {row["label"]: row["name"] for row in display_rows if row["label"] is not None}
        else:
            names = {label: _row_name(row) for label, row in rs.rows.items() if not is_sweep_only(row)}
        labels_by_name = {name: label for label, name in names.items()}
        assert len(labels_by_name) == len(names), (table, "duplicate display names")
        per_metric = defaultdict(list)
        for change in table_changes:
            per_metric[METRICS[change["column_index"] - 2]].append(change)
        for metric, requested in per_metric.items():
            family = sorted(label for label in names if rs.mean(label, metric) is not None and metric in rs.scores().get(label, {}))
            edges = significance_vs_best(rs.scores(), family, metric, 10000, 0, plan=rs.bootstrap_plan())
            old_adjusted = holm_correction([edge["p"] if math.isfinite(edge["p"]) else 1.0 for edge in edges])
            old_by_label = {edge["row"]: p for edge, p in zip(edges, old_adjusted)}
            by_label = {edge["row"]: edge for edge in edges}
            families[f"{table}:{metric}"] = family
            for change in requested:
                label = labels_by_name[change["row"]]
                edge = by_label[label]
                result = {
                    "table": table,
                    "model": model,
                    "metric": metric,
                    "row": change["row"],
                    "row_label": label,
                    "row_mean": rs.mean(label, metric),
                    "best_row": names[edge["best_row"]],
                    "best_row_label": edge["best_row"],
                    "best_mean": rs.mean(edge["best_row"], metric),
                    "delta_row_minus_best": edge["delta"],
                    "n_paired_images": edge["n"],
                    "p_raw": edge["p"],
                    "p_holm_all_pairs": edge["p_holm"],
                    "p_holm_old_winner_only": old_by_label[label],
                    "all_pairs_family_size": edge["family_size"],
                    "old_winner_family_size": len(edges),
                    "significant_all_pairs": edge["significant"],
                }
                assert not result["significant_all_pairs"] and result["p_holm_old_winner_only"] < 0.05, result
                output.append(result)
                print(json.dumps(result), flush=True)
    document = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "python_executable": sys.executable,
        "n_boot": 10000,
        "seed": 0,
        "sampling_unit": "image",
        "interpretation": "Added markers indicate non-rejection against the empirical best after all-pairs Holm correction; they do not establish equivalence.",
        "old_p_method": "Winner-only Holm recomputed from the identical raw paired-test p-values.",
        "comparisons": output,
        "family_rows": families,
    }
    path = evidence / "imagenet_marker_pvalues.json"
    path.write_text(json.dumps(document, indent=2) + "\n")
    print(f"Wrote {path}", flush=True)


if __name__ == "__main__":
    main()
