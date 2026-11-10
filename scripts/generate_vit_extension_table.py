#!/usr/bin/env python3
"""Audit completed ViT campaigns and stage the thesis's existing CI table layout.

This is a read-only experiment adapter: no model evaluation, GPU work, experiment
edits, active-TeX edits, or test-dependent selection. Exit 0 means all requested
campaigns passed the completion gate; 2 means results remain pending or invalid.
Only a complete gate produces extension_ci_longtable.tex and integration.tex.
"""
from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import io
import json
import math
import re
from decimal import Decimal
from pathlib import Path

import numpy as np

from table_presentation import cells
from vit_extension_statistics import build_statistics

ROOT = Path(__file__).resolve().parents[1]
REPOS = ROOT.parent
CAMPAIGNS = {
    "cam": REPOS / "hidden-monotonicity-transformer-dc/results/vit_cam_paper_campaign/compact_2026-11-10",
    "paper": REPOS / "hidden-monotonicity-transformer-dc/results/vit_paper_splitcam_campaign/compact_2026-11-10",
    "weaker": REPOS / "hidden-monotonicity-live-stability/results/vit_paper_splitcam_campaign/weaker_2026-11-10",
}
TEMPLATE = ROOT / "tex/tables/ptnb_v2/generated/test_vit_b16_ci_longtable.tex"
OLD_RESULTS = ROOT / "code/playing_backward/results_summary/test/vit_b16"
METRICS = {
    "AL": "attribution_localisation", "PG": "pointing_game",
    "TK": "top_k_intersection", "PF5": "pixel_flipping_abs_5pct",
    "PF20": "pixel_flipping_abs_20pct", "Sel": "selectivity",
    "MaxS": "max_sensitivity", "AvgS": "avg_sensitivity",
}
EXPECTED_READOUT = {"g": "sum((p-n)*(pp-np)/2)", "g_minus": "sum(n*np)",
                    "g_plus": "sum(p*pp)", "h": "sum((p-n)*(pn-nn)/2)",
                    "h_minus": "sum(n*nn)", "h_plus": "sum(p*pn)"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_read(path: Path):
    return json.loads(path.read_text())


def csv_read(path: Path):
    lines = path.read_text().splitlines()
    metadata = dict(line[2:].split(": ", 1) for line in lines
                    if line.startswith("# ") and ": " in line)
    rows = list(csv.DictReader(io.StringIO("\n".join(line for line in lines if not line.startswith("#")))))
    return metadata, rows


def need(condition, message):
    if not condition:
        raise ValueError(message)


def decimals(metric):
    return 2 if metric in ("PF5", "PF20") else 3


def ci_cell(metric, mean, lo, hi):
    d = decimals(metric)
    return (r"\begin{tabular}[t]{@{}c@{}}" + f"{mean:.{d}f}" +
            r"\\[-1pt]{\tiny[" + f"{lo:.{d}f},{hi:.{d}f}" + r"]}\end{tabular}")


def marked_cell(cell, marker):
    if marker == "best":
        return r"\cellbest{" + re.sub(r"(\}\})([0-9.]+)(?=\\\\)", r"\1\\textbf{\2}", cell, count=1) + "}"
    if marker == "approx":
        return r"\cellapprox{" + re.sub(r"(\}\})([0-9.]+)(?=\\\\)", r"\1\2\\textsuperscript{$\\approx$}", cell, count=1) + "}"
    return cell


def manifest_identity(protocol, split):
    return [(r["image_name"], r["wnid"], r["image_path_sha256"], r["mask_path_sha256"])
            for r in protocol[split + "_manifest"]]


def protocol_check(protocol, reference):
    need(protocol["dataset"] == "imagenet-s" and protocol["model"] == "vit_b16", "wrong dataset/model")
    for split, n in (("validation", 50), ("test", 565)):
        ids = manifest_identity(protocol, split)
        need(len(ids) == n and len({r[0] for r in ids}) == n, f"{split} sample size/duplicates")
        need(ids == manifest_identity(reference, split), f"{split} images, classes or content differ")
    need(protocol["checkpoint"]["sha256"] == reference["checkpoint"]["sha256"], "checkpoint mismatch")
    need(protocol["robustness"] == reference["robustness"], "robustness subset/protocol differs")
    need(protocol["test_metrics"] == list(METRICS), "test metric set/order differs")
    need(protocol["selection"]["loc"] == ["AL", "PG", "TK"], "localisation selection changed")
    need(protocol["selection"]["faith"] == ["PF5", "PF20", "Sel"], "faithfulness selection changed")
    if "readout" in protocol:
        need(protocol["readout"] == EXPECTED_READOUT, "signed SplitCAM formulas differ")
        need("no ReLU or gradient clipping" in protocol["paper_definition"], "unsigned SplitCAM definition")
    sources = protocol["source_sha256"]
    reference_sources = reference["source_sha256"]
    for path, digest in reference_sources.items():
        if "/configs/metrics_main_table/" in path:
            need(sources.get(path) == digest, "metric configuration source changed: " + path)


def row_check(result, protocol, baseline):
    need(result["n_images"] == 565 and result["split"] == "test", "wrong test size/split")
    need(result["dataset"] == "imagenet-s" and result["model"] == "vit_b16", "wrong row dataset/model")
    need(result["map_failures"] == 0 and result["zero_maps"] == 0, "failed/zero maps")
    need(result["metric_params"] == baseline["metric_params"], "metric parameters differ from paper Gradient")
    need(result["environment"]["quantus"] == baseline["environment"]["quantus"] == "0.6.0", "Quantus version differs")
    for metric in METRICS:
        value = result["metrics"][metric]
        n = 200 if metric in ("MaxS", "AvgS") else 565
        need(value["n"] == n and value["coverage"] == 1, f"{metric}: incomplete coverage")
        need(math.isfinite(value["mean"]), f"{metric}: nonfinite mean")


def npz_check(path, result, protocol):
    with np.load(path, allow_pickle=False) as scores:
        ids = scores["image_ids"].tolist()
        expected = [r["image_name"] for r in protocol["test_manifest"]]
        need(ids == expected, "per-image test IDs/order differ")
        need(not scores["map_failed"].any() and not scores["map_is_zero"].any(), "per-image failed/zero maps")
        for metric, key in METRICS.items():
            values = scores[key]
            need(values.shape == (565,), f"{metric}: per-image score shape")
            good = np.isfinite(values)
            expected_ids = protocol["robustness"]["image_names"] if metric in ("MaxS", "AvgS") else expected
            need([name for name, ok in zip(ids, good) if ok] == expected_ids, f"{metric}: subset mismatch/nonfinite score")
            need(math.isclose(float(values[good].mean()), result["metrics"][metric]["mean"], rel_tol=1e-10, abs_tol=1e-10),
                 f"{metric}: summary differs from per-image scores")


def row_labels(row, campaign):
    choice = "/".join(s for s in ("loc", "faith") if s in row["selected_by"])
    params = row["params"]
    if row["method"] in ("gcam", "lcam"):
        name = {"gcam": "Grad-CAM", "lcam": "LayerCAM"}[row["method"]]
        block = int(re.search(r"encoder_layer_(\d+)", params["target_layer_name"]).group(1)) + 1
        config = f"$B{{=}}{block}$"
    else:
        name = "SplitCAM"
        policy = {"fixed_both": "F", "fixed_ln": "L", "full": "U"}[params["policy"]]
        formula = params["formula"].replace("_minus", "^{-}").replace("_plus", "^{+}")
        # Decimal arithmetic preserves the round-trip spelling without a wide
        # 18-digit literal or the :g rounding that conflates it with 0.5.
        alpha = repr(params["alpha"])
        gap = Decimal("0.5") - Decimal(alpha)
        if 0 < abs(gap) < Decimal("1e-8"):
            coefficient, exponent = format(abs(gap).normalize(), "E").split("E")
            sign = "-" if gap > 0 else "+"
            alpha = rf"0.5{sign}{coefficient}\!\times\!10^{{{int(exponent)}}}"
        parts = [policy, f"B{{=}}{params['block']}", rf"\alpha{{=}}{alpha}", formula]
        if campaign == "weaker":
            parts.append(f"p{{=}}{params['backward_scale_power']:g}")
        config = "$" + r",\allowbreak ".join(parts) + "$"
    return f"{name} ({choice})", config


def audit_campaign(name, path, reference, baseline, ledger):
    result = {"name": name, "path": str(path), "ready": False, "issues": [], "excluded_methods": [], "rows": []}
    try:
        status = json_read(path / "status.json")
        result["status"] = status
        protocol = json_read(path / "protocol.json")
        protocol_check(protocol, reference)
        ledger(path / "status.json"); ledger(path / "protocol.json")
        if status["stage"] not in ("complete", "completed_no_admissible_configuration"):
            result["issues"].append("campaign stage: " + status["stage"])
            return result
        need(not status.get("failures"), "campaign stage failures")
        if (path / "test_stage_failures.json").exists():
            need(not json_read(path / "test_stage_failures.json"), "recorded test-stage failures remain")
        selection = json_read(path / "selected_frozen.json")
        ledger(path / "selected_frozen.json")
        need(selection["protocol_sha256"] == sha(path / "protocol.json"), "selection protocol hash mismatch")
        if status.get("selected_sha256"):
            need(status["selected_sha256"] == sha(path / "selected_frozen.json"), "completed selection hash mismatch")
        need(not selection["missing_rows"], "missing validation records")
        need(selection["n_val_configs"] == selection["n_grid_rows"] == len(protocol["grid"]), "incomplete grid selection")
        need(set(selection["methods"]) == set(protocol["methods"]), "selected methods differ from protocol")
        grid = {r["row_label"]: r for r in protocol["grid"]}
        need(len(grid) == len(protocol["grid"]), "duplicate grid row identifiers")
        for method, item in selection["methods"].items():
            declared = sum(r["method"] == method for r in protocol["grid"])
            need(item["n_evaluated"] == item["n_configs"] == declared, "incomplete method validation")
            chosen = [r for r in selection["rows"] if r["method"] == method]
            if item["n_admissible"] == 0:
                need(not chosen, "inadmissible method was selected")
                result["excluded_methods"].append({"method": method, "reason": "no admissible validation configuration",
                                                   "declared_configurations": item["n_configs"]})
            else:
                need({s for r in chosen for s in r["selected_by"]} == {"loc", "faith"}, "missing selection criterion")
                for row in chosen:
                    for criterion in row["selected_by"]:
                        need(item[criterion]["row_label"] == row["row_label"], "frozen row differs from validation selector")
                        need(item[criterion]["params"] == row["params"], "selected parameters differ from validation selector")
        if not selection["rows"]:
            need(status["stage"] == "completed_no_admissible_configuration", "empty completed selection")
            result["ready"] = True
            return result
        archive = path / "source_archive.json"
        need(name == "cam" or archive.exists(), "SplitCAM source archive missing")
        if archive.exists():
            ledger(archive)
            for source, entry in json_read(archive).items():
                need(protocol["source_sha256"][source] == entry["sha256"], "archive/source hash differs")
                need(sha(path / entry["archive"]) == entry["sha256"], "source snapshot changed: " + source)
        receipt = path / "selection_receipt.json"
        if receipt.exists():
            binding = json_read(receipt); ledger(receipt)
            need(binding["selected_sha256"] == sha(path / "selected_frozen.json"), "selection receipt mismatch")
            need(binding["protocol_sha256"] == sha(path / "protocol.json"), "protocol receipt mismatch")
        bootstrap = json_read(path / "test/bootstrap_metadata.json")
        ledger(path / "test/bootstrap_metadata.json")
        for key, expected in {"sampling_unit": "image", "n_units": 565, "n_boot": 10000, "seed": 0, "ci": "percentile_95"}.items():
            need(bootstrap[key] == expected, "bootstrap metadata differs: " + key)
        need(set(bootstrap["family_rows"]) == {r["row_label"] for r in selection["rows"]}, "CI family differs from selection")
        _, cis = csv_read(path / "test/ci.csv"); ledger(path / "test/ci.csv")
        ci_index = {(r["row"], r["metric"]): r for r in cis}
        need(len(ci_index) == len(cis), "duplicate CI cells")
        runtime_path = path / ("runtime.csv" if name == "cam" else "runtime/vit_b16.csv")
        hardware, runtimes = csv_read(runtime_path); ledger(runtime_path)
        times = {r["row_label"]: r for r in runtimes}
        need(set(times) == {r["row_label"] for r in selection["rows"]}, "runtime rows differ from selection")
        result["protocol"] = {k: protocol[k] for k in ("checkpoint", "precision", "postprocessing", "test_exposure")}
        for row in selection["rows"]:
            uid = row["row_label"]
            need(grid[uid]["params"] == row["params"] and grid[uid]["method"] == row["method"], "selected configuration changed")
            f = path / "test" / (uid + ".json")
            item = json_read(f); ledger(f)
            need(item["row_label"] == uid and item["params"] == row["params"] and item["method"] == row["method"], "result configuration changed")
            row_check(item, protocol, baseline)
            score_path = path / "test/per_image" / (uid + ".npz")
            npz_check(score_path, item, protocol); ledger(score_path)
            if "policy" in row["params"]:
                admission_path = path / "policy_admission" / (row["params"]["policy"] + ".json")
                admission = json_read(admission_path); ledger(admission_path)
                need(admission["status"] == "policy_admitted" and admission["diagnostics"]["passed"], "policy not admitted")
                need(admission["protocol_sha256"] == sha(path / "protocol.json"), "policy admission protocol mismatch")
            timing = times[uid]
            need(int(timing["n_images"]) == 50 and int(timing["failures"]) == 0, "runtime incomplete")
            need(math.isfinite(float(timing["median_s"])) and float(timing["median_s"]) > 0, "runtime invalid")
            values = {}
            for metric in METRICS:
                c = ci_index[uid, metric]
                mean = item["metrics"][metric]["mean"]
                lo, hi = float(c["lo"]), float(c["hi"])
                need(int(c["n"]) == item["metrics"][metric]["n"], "CI sample size differs")
                need(math.isclose(float(c["mean"]), mean, rel_tol=6e-6, abs_tol=1e-6), "CI mean differs")
                need(math.isfinite(lo) and math.isfinite(hi) and lo <= mean <= hi, "invalid CI bounds")
                values[metric] = {"mean": mean, "lo": lo, "hi": hi, "n": int(c["n"]), "coverage": 1.0}
            label, config = row_labels(row, name)
            result["rows"].append({"row_label": uid, "campaign": name, "label": label, "config_latex": config,
                                   "selected_by": row["selected_by"], "params": row["params"], "metrics": values,
                                   "source": str(score_path), "source_kind": "npz",
                                   "runtime": {**timing, "hardware": hardware}})
        result["rows"].sort(key=lambda r: (0 if r["row_label"].startswith("gcam") else 1 if r["row_label"].startswith("lcam") else 2,
                                                r["params"].get("policy", ""), 0 if "loc" in r["selected_by"] else 1))
        result["ready"] = True
    except (OSError, ValueError, KeyError, TypeError, IndexError) as error:
        result["issues"].append(f"{type(error).__name__}: {error}")
        result["rows"] = []
    return result


def build(out, names):
    need(not out.is_relative_to(ROOT / "tex"), "output must be staged outside active TeX")
    out.mkdir(parents=True, exist_ok=True)
    (out / "admission.json").write_text(json.dumps({"ready": False, "stage": "auditing"}) + "\n")
    for name in ("extension_ci_longtable.tex", "integration.tex"):
        (out / name).unlink(missing_ok=True)
    sources = {}

    def ledger(path):
        sources[str(path.resolve())] = sha(path)

    ledger(Path(__file__))
    reference = json_read(CAMPAIGNS["cam"] / "protocol.json")
    ledger(CAMPAIGNS["cam"] / "protocol.json")
    baseline_path = OLD_RESULTS / "gradient__cr-maxabs.json"
    baseline = json_read(baseline_path); ledger(baseline_path)
    row_check(baseline, reference, baseline)
    historical_csv = OLD_RESULTS / "per_image_scores.csv.gz"
    with gzip.open(historical_csv, "rt") as stream:
        old_scores = [r for r in csv.DictReader(stream) if r["row_label"] == baseline["row_label"]]
    ledger(historical_csv)
    need({r["image_id"] for r in old_scores} == {r["image_name"] for r in reference["test_manifest"]}, "historical Gradient IDs differ")
    for metric in ("MaxS", "AvgS"):
        need({r["image_id"] for r in old_scores if r[METRICS[metric]]} == set(reference["robustness"]["image_names"]), "historical Gradient sensitivity IDs differ")
    template = TEMPLATE.read_text(); ledger(TEMPLATE)
    prefix, _ = template.split("\\endlastfoot\n", 1)
    original = next(cells(line)[0] for line in template.splitlines() if line.startswith("Gradient &"))
    need(len(original) == 10, "existing ViT table changed layout")
    review_path = ROOT / "reports/vit-extension/gradient-provenance-review.json"
    review = json_read(review_path); ledger(review_path)
    need(cells(review["gradient"]["canonical_full_ci_tex_row"])[0] == original,
         "copied Gradient cells differ from independently verified CI row")
    for index, metric in enumerate(METRICS, 2):
        # Displayed means remain byte-for-byte copied; verify their rounded value.
        displayed = original[index].split("}}", 1)[1].split("\\", 1)[0]
        need(displayed == f"{baseline['metrics'][metric]['mean']:.{decimals(metric)}f}", "copied Gradient mean differs")
    original[0] = "Gradient (paper)"
    campaigns = [audit_campaign(name, CAMPAIGNS[name], reference, baseline, ledger) for name in names]
    ready = all(c["ready"] for c in campaigns)
    rows = [r for c in campaigns for r in c["rows"]]
    statistics = None
    statistics_digest = None
    if ready:
        stats_rows = [{"row_label": baseline["row_label"], "source": str(historical_csv), "source_kind": "paper_csv",
                       "metrics": baseline["metrics"]}, *rows]
        statistics = build_statistics(stats_rows, out / "combined_statistics.json",
                                      image_ids=[r["image_name"] for r in reference["test_manifest"]],
                                      robustness_ids=reference["robustness"]["image_names"])
        statistics_digest = sha(out / "combined_statistics.json")
        sources.update(statistics["source_sha256"])
        for index, metric in enumerate(METRICS, 2):
            original[index] = marked_cell(original[index], statistics["metrics"][metric]["rows"][baseline["row_label"]]["marker"])
    lines = [prefix + "\\endlastfoot", " & ".join(original) + r" \\"]
    for row in rows:
        lines.append(" & ".join([row["label"], row["config_latex"], *[
            marked_cell(ci_cell(metric, row["metrics"][metric]["mean"], row["metrics"][metric]["lo"], row["metrics"][metric]["hi"]),
                        statistics["metrics"][metric]["rows"][row["row_label"]]["marker"] if statistics else None)
            for metric in METRICS]]) + r" \\")
    table = "\n".join(lines) + "\n\\end{longtable}\n"
    fingerprint = hashlib.sha256(json.dumps({"sources_sha256": sources,
                                             "combined_statistics_sha256": statistics_digest}, sort_keys=True).encode()).hexdigest()
    admission = {"schema": 1, "ready": ready, "source_fingerprint": fingerprint,
                 "requested_campaigns": names, "campaigns": campaigns, "n_rows": len(rows) + 1,
                 "rows": rows, "metric_order": list(METRICS), "metric_directions": {k: "up" if k in ("AL", "PG", "TK") else "down" for k in METRICS},
                 "table": "extension_ci_longtable.tex" if ready else None,
                 "integration": "integration.tex" if ready else None,
                 "statistics": "combined_statistics.json" if ready else None,
                 "combined_statistics": {"status": "complete", "path": "combined_statistics.json",
                                         "sha256": statistics_digest,
                                         "family_rows": [baseline["row_label"], *[r["row_label"] for r in rows]]} if ready else {"status": "pending"},
                 "exported_files": {"extension_ci_longtable.tex": "tables/vit_extension/generated/extension_ci_longtable.tex",
                                    "integration.tex": "tables/vit_extension/generated/integration.tex"} if ready else {},
                 "preview": "preview_ci_longtable.tex", "copied_gradient": str(baseline_path)}
    provenance = {"sources_sha256": sources, "source_fingerprint": fingerprint,
                  "combined_statistics_sha256": statistics_digest,
                  "copied_gradient": {"row_label": baseline["row_label"], "means_and_CIs": str(TEMPLATE),
                                      "note": "Copied unchanged from the paper table; no new Gradient run. Historical checkpoint hash was not recorded.",
                                      "runtime": "Excluded from this ten-column layout; paper timing uses A100 and new campaign timings use TITAN V."},
                  "statistics": "Per-row 95% image bootstrap CIs; combined displayed-family paper-protocol paired tests with Holm adjustment over every unordered eligible pair per metric. The approximate marker denotes no significant difference, not equivalence. Copied Gradient pairwise tests use archived per-image scores rounded to about six significant digits; its original displayed CI cells are retained.",
                  "targets": "Annotated ImageNet-S class, as in the canonical evaluator; class identifiers and image/mask hashes match across the new campaigns.",
                  "validation_images": 50, "test_images": 565, "sensitivity_images": 200,
                  "test_exposure": reference["test_exposure"]}
    need(all(sha(Path(path)) == digest for path, digest in sources.items()),
         "a source artifact changed during export; retry against a stable snapshot")
    (out / "preview_ci_longtable.tex").write_text(table)
    (out / "admission.json").write_text(json.dumps(admission, indent=2) + "\n")
    (out / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    if ready:
        (out / "extension_ci_longtable.tex").write_text(table)
        (out / "integration.tex").write_text(integration_text(campaigns))
    else:
        for name in ("extension_ci_longtable.tex", "integration.tex"):
            (out / name).unlink(missing_ok=True)
    print(json.dumps({"ready": ready, "rows": len(rows) + 1, "out": str(out),
                      "campaigns": {c["name"]: {"ready": c["ready"], "issues": c["issues"]} for c in campaigns}}))
    return 0 if ready else 2


def integration_text(campaigns):
    text = r"""\section{Transformer DC Extension Results}
\label{sec:vit-extension}
\appneedspace{8\baselineskip}
\begin{center}
    \captionsetup{hypcap=false}
    \captionof{table}[ViT-B/16: extension results with confidence intervals]{ViT-B/16 extension results on the same ImageNet-S test split (565 images; MaxS/AvgS: the fixed 200-image subset), with 95\% image-bootstrap confidence intervals. Gradient is copied from Table~\ref{ptnb:tab:test-ci-vit}; the other configurations were selected on the same 50 validation images. Labels loc/faith denote the unchanged selection criteria. Bold/dark shading marks the best row; $^{\approx}$/light shading marks no significant difference under Holm adjustment across all row pairs within each metric of this table (Section~\ref{ptnb:app:stats}).}
    \label{tab:vit-extension}
\end{center}
\captionsetup{hypcap=true}
\appinputgenci{tables/vit_extension/generated/extension_ci_longtable}
\noindent $B$ is the one-based block index (LN1 readout). SplitCAM uses the signed paper formulas without ReLU; $F$, $L$ and $U$ denote fixed attention and LayerNorm, fixed LayerNorm only, and both live. Configurations with $p$ use adaptive common-component scaling and the selected backward scale power; the remaining SplitCAM rows use the paper post-shifts. Fixed quantities are recomputed for each perturbed input. CAM baselines retain their library normalization and bilinear resize; SplitCAM retains signed maps and nearest-neighbor resize. All metrics apply their original absolute-value preprocessing. Gradient pairwise tests use archived rounded per-image scores; its original confidence intervals are retained. Three test illustrations were viewed during method development.
"""
    runs = {"cam": "CAM search", "paper": "paper-postshift search", "weaker": "adaptive search"}
    methods = {"paper_splitcam_fixed_both": "$F$", "paper_splitcam_fixed_ln": "$L$",
               "paper_splitcam_full": "$U$", "gcam": "Grad-CAM", "lcam": "LayerCAM"}
    for campaign in campaigns:
        rejected = [methods[r["method"]] for r in campaign["excluded_methods"]]
        if rejected:
            text += "The " + runs[campaign["name"]] + " admitted no validation configuration for " + ", ".join(rejected) + ".\n"
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=ROOT / "reports/vit-extension/candidate")
    parser.add_argument("--campaign", action="append", choices=list(CAMPAIGNS), help="repeat to stage a completed subset; default: all three")
    args = parser.parse_args()
    return build(args.out.resolve(), list(dict.fromkeys(args.campaign or CAMPAIGNS)))


if __name__ == "__main__":
    raise SystemExit(main())
