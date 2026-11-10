#!/usr/bin/env python3
"""Independently recover validation facts from the compact matrix and CI tables.

This checker does not import or call the view generator. It preserves the
separate-parser checks used in the independent review and writes a hash-bound
receipt. It reads TeX as data and does not run a TeX build.
"""

from __future__ import annotations

import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORTS = Path("reports/single-pdf")
SOURCE = Path("tex/tables/ptnb_v2/generated")
MATRIX = Path("tex/tables/integrated/validation_rank_matrix_tabular.tex")
GENERATOR = REPORTS / "build_experiment_views.py"
AUDIT = REPORTS / "experiment-view-audit.json"
CHECKER = REPORTS / "check_validation_matrix_independent.py"
RECEIPT = REPORTS / "validation-matrix-independent-review.json"
MODELS = ("vit_b16", "vgg16", "resnet50")


def require(condition: bool, detail: object) -> None:
    if not condition:
        raise AssertionError(detail)


def main() -> None:
    paths = [
        SOURCE / f"{prefix}_{model}_{suffix}.tex"
        for model in MODELS
        for prefix, suffix in (
            ("val_selection", "tabular"), ("test", "ci_longtable")
        )
    ] + [MATRIX, GENERATOR, AUDIT, CHECKER]
    snapshots = {path: (ROOT / path).read_bytes() for path in paths}
    texts = {path: content.decode("utf-8") for path, content in snapshots.items()}

    def data(path: Path, columns: int, header: str) -> list[tuple[int, list[str]]]:
        parsed = []
        for line_number, line in enumerate(texts[path].splitlines(), 1):
            if not line.endswith(r"\\") or "&" not in line:
                continue
            cells = [value.strip() for value in line[:-2].split("&")]
            if len(cells) == columns and cells[0] != header:
                parsed.append((line_number, cells))
        return parsed

    def normalize(value: str) -> str:
        return "".join(value.replace(r"\allowbreak", "").split())

    matrix = [
        (line, cells) for line, cells in data(MATRIX, 8, "Method")
        if cells[1] in ("loc", "faith", "loc/faith", "anchor")
    ]
    expanded = {}
    method = ""
    count = {}
    for line, cells in matrix:
        method = cells[0] or method
        for model_index, model in enumerate(MODELS):
            grid_count, pair = cells[2 + 2 * model_index:4 + 2 * model_index]
            if grid_count:
                count[(model, method)] = grid_count
            if pair == "---":
                continue
            require(count[(model, method)].isdigit(), (model, method, grid_count))
            ranks = pair.removeprefix("$(").removesuffix(")$").split(",")
            require(len(ranks) == 2, (model, method, pair))
            for criterion in cells[1].split("/"):
                key = model, method, criterion
                require(key not in expanded, ("duplicate matrix entry", key))
                expanded[key] = (count[(model, method)], ranks, line)

    expected = {}
    fixed = []
    configurations = set()
    total = 0
    anchor_count = 0
    per_model = {}
    for model in MODELS:
        ci_path = SOURCE / f"test_{model}_ci_longtable.tex"
        source_path = SOURCE / f"val_selection_{model}_tabular.tex"
        full = {cells[0]: (line, cells[1]) for line, cells in data(ci_path, 10, "Method")}
        raw = data(source_path, 5, "Method")
        name = ""
        local_fixed = local_anchors = 0
        for line, cells in raw:
            name = cells[0] or name
            match = re.fullmatch(r"(.*) \((\d+)\)", name)
            require(match is not None, (model, line, name))
            method, grid_count = match.groups()
            criterion = cells[1]
            key = model, method, criterion
            if criterion == "fixed":
                require(grid_count == "1" and cells[3:] == ["n/a", "n/a"], key)
                fixed.append(key)
                local_fixed += 1
                identifier = method
            elif criterion == "anchor":
                identifier = method + " anchor"
                anchor_count += 1
                local_anchors += 1
            else:
                identifier = method + " (" + criterion + ")"
                if identifier not in full:
                    identifier = method + " (loc/faith)"
            require(identifier in full, (model, identifier))
            require(
                normalize(cells[2]) == normalize(full[identifier][1]),
                ("configuration differs", model, identifier, cells[2], full[identifier][1]),
            )
            configurations.add((model, identifier))
            total += 1
            if criterion != "fixed":
                require(key not in expected, ("duplicate source entry", key))
                expected[key] = (grid_count, cells[3:])
        per_model[model] = {
            "source_records": len(raw),
            "fixed_records": local_fixed,
            "nonfixed_records": len(raw) - local_fixed,
            "anchor_records": local_anchors,
            "canonical_configurations": len({key for key in configurations if key[0] == model}),
        }

    require(expected.keys() == expanded.keys(), "matrix/source method and criterion coverage")
    for key, (grid_count, ranks) in expected.items():
        require(expanded[key][:2] == (grid_count, ranks), (key, expected[key], expanded[key]))
    require(
        (total, len(expected), len(fixed), len(configurations), len(matrix), anchor_count)
        == (63, 44, 19, 57, 20, 4),
        "unexpected review counts",
    )
    note = texts[MATRIX]
    require("Fixed methods have one configuration and n/a rank-sums." in note, "fixed-method note")
    require("declared grid size" in note and "ranks use admitted configurations" in note, "grid/admission distinction")
    require(
        not re.search(r"\\(?:resizebox|scalebox|fontsize|small|footnotesize|scriptsize|tiny)\b", note),
        "view must not change font or resize",
    )
    require(expected[("vgg16", "SG", "loc")][0] == "40", "SG declared grid count")
    duplicate_pair_checks = []
    for model in ("vit_b16", "vgg16"):
        for method in ("SmGrad", "IntGrad"):
            require(
                expected[(model, method, "loc")] == expected[(model, method, "faith")],
                ("shared-selection rank pair", model, method),
            )
            duplicate_pair_checks.append({"architecture": model, "method": method, "status": "pass"})

    audit = json.loads(texts[AUDIT])["validation_matrix"]
    require(len(audit["record_mapping"]) == 63, "audit coverage")
    for record in audit["record_mapping"]:
        canonical_path = Path(record["canonical_configuration_source"])
        line = texts[canonical_path].splitlines()[record["canonical_configuration_line"] - 1]
        cells = [value.strip() for value in line[:-2].split("&")]
        require(cells[0] == record["canonical_configuration_identifier"], "audit identifier")
        require(cells[1] == record["canonical_configuration_tex"], "audit canonical TeX")
        require(normalize(cells[1]) == normalize(record["configuration"]), "audit configuration")
        if record["criterion"] != "fixed":
            key = record["architecture"], record["method"], record["criterion"]
            require(expanded[key][2] == record["matrix_line"], ("audit matrix line", key))
            require(
                expected[key] == (str(record["declared_grid_count"]), record["rank_sums"]),
                ("audit rank/count", key),
            )

    for path, snapshot in snapshots.items():
        require((ROOT / path).read_bytes() == snapshot, ("input changed during check", str(path)))
    receipt = {
        "status": "pass",
        "reviewed_at_utc": datetime.now(timezone.utc).isoformat(),
        "reviewer": "independent child agent verify_table_views",
        "checker": str(CHECKER),
        "method": "Separate physical-line TeX parser, independent of the generator. Resolve inherited labels; expand loc/faith matrix cells; compare every original method/criterion/grid-count/rank-pair; match all original configurations to canonical full-CI rows after removing only whitespace and allowbreak; verify audit identifiers, line references and values.",
        "counts": {
            "source_records": total,
            "nonfixed_rank_pair_records": len(expected),
            "fixed_records_with_one_configuration_and_na_ranks": len(fixed),
            "canonical_configurations": len(configurations),
            "matrix_rows": len(matrix),
            "anchor_records": anchor_count,
            "audit_records_checked": len(audit["record_mapping"]),
        },
        "per_model": per_model,
        "findings": {
            "all_original_configurations_mapped_exactly": "pass",
            "all_nonfixed_rank_pairs_grid_counts_and_criteria_preserved": "pass",
            "all_fixed_records_preserved_via_note_and_full_ci_rows": "pass",
            "all_anchor_records_preserved": "pass",
            "shared_smoothgrad_integrated_gradients_rank_pairs": duplicate_pair_checks,
            "sg_declared_count_40_with_admitted_configuration_rank_note": "pass",
            "audit_configuration_and_matrix_line_mappings": "pass",
            "no_resizing_or_font_commands_in_matrix": "pass",
            "inputs_unchanged_during_check": "pass",
        },
        "sha256": {str(path): hashlib.sha256(content).hexdigest() for path, content in snapshots.items()},
        "commands": ["python3 reports/single-pdf/check_validation_matrix_independent.py"],
        "tools": ["Python 3 standard library: pathlib, re, json, hashlib, datetime"],
        "tex_build_performed": False,
        "scope_limit": "Numerical/source-retention review only; rendered width, page placement and readability are not assessed by this checker.",
    }
    (ROOT / RECEIPT).write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: 63 source records, 44 nonfixed, 19 fixed, 57 canonical configurations, 20 matrix rows, 4 anchors. Receipt: {RECEIPT}")


if __name__ == "__main__":
    main()
