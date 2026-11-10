#!/usr/bin/env python3
"""Generate compact table views without changing the source evaluation tables.

Run from any directory; --check verifies the views and their row-level audit.
Only identical validation selections and repeated selected-center ablation
rows are merged. All other data rows, their order, and typography are retained.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE = Path("tex/tables/ptnb_v2/generated")
DESTINATION = Path("tex/tables/integrated")
AUDIT = Path("reports/single-pdf/experiment-view-audit.json")
MATRIX = DESTINATION / "validation_rank_matrix_tabular.tex"
TABLES = (
    ("val_selection_vit_b16_tabular.tex", "validation"),
    ("val_selection_vgg16_tabular.tex", "validation"),
    ("ablations_vit_b16_longtable.tex", "ablation"),
    ("ablations_vgg16_longtable.tex", "ablation"),
    ("ablations_resnet50_longtable.tex", "ablation"),
)


@dataclass(frozen=True)
class Row:
    number: int
    line: int
    cells: tuple[str, ...]
    context: tuple[str, ...]


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def parse_rows(text: str, kind: str) -> list[Row]:
    """Resolve empty inherited labels while retaining each exact source cell."""
    rows = []
    method = factor = ""
    expected = 5 if kind == "validation" else 9
    for line_number, line in enumerate(text.splitlines(), 1):
        if "&" not in line or not line.rstrip().endswith(r"\\"):
            continue
        cells = tuple(cell.strip() for cell in line.rstrip()[:-2].split("&"))
        if cells[0] in {"Method", "Center"}:
            continue
        if len(cells) != expected:
            raise ValueError(f"Unexpected row shape at line {line_number}: {cells}")
        if cells[0]:
            method = cells[0]
        if kind == "ablation":
            if cells[1]:
                factor = cells[1]
            context = (method, factor)
        else:
            context = (method,)
        if not all(context):
            raise ValueError(f"Unresolved row context at line {line_number}")
        rows.append(Row(len(rows) + 1, line_number, cells, context))
    return rows


def unbold(value: str) -> str:
    prefix = r"\textbf{"
    if not value.startswith(prefix) or not value.endswith("}"):
        raise ValueError(f"Selected value is not wholly bold: {value}")
    return value[len(prefix):-1]


def parameter_text(factor: str, value: str) -> str:
    if factor.startswith("$") and factor.endswith("$"):
        return "$" + factor[1:-1] + "{=}" + value + "$"
    return factor + " " + value


def render_view(
    text: str,
    rows: list[Row],
    canonical: dict[int, int],
    replacements: dict[int, tuple[str, ...]],
    prefix: str = "",
) -> tuple[str, dict[int, dict[str, int]]]:
    by_line = {row.line: row for row in rows}
    lines = prefix.splitlines()
    positions = {}
    output_row = 0
    for source_line, line in enumerate(text.splitlines(), 1):
        row = by_line.get(source_line)
        if row is not None:
            if canonical[row.number] != row.number:
                continue
            if row.number in replacements:
                line = " & ".join(replacements[row.number]) + r" \\"
            output_row += 1
            positions[row.number] = {
                "output_row": output_row,
                "output_line": len(lines) + 1,
            }
        lines.append(line)
    return "\n".join(lines) + "\n", positions


def validation_view(text: str) -> tuple[str, dict]:
    rows = parse_rows(text, "validation")
    groups: dict[tuple, list[Row]] = {}
    for row in rows:
        key = row.context + row.cells[2:]
        groups.setdefault(key, []).append(row)
    canonical = {row.number: row.number for row in rows}
    replacements = {}
    merged = []
    for group in groups.values():
        if len(group) == 2 and {row.cells[1] for row in group} == {"loc", "faith"}:
            first, second = group
            canonical[second.number] = first.number
            cells = list(first.cells)
            cells[1] = "loc/faith"
            replacements[first.number] = tuple(cells)
            merged.append({
                "method": first.context[0],
                "configuration": first.cells[2],
                "rank_sums": list(first.cells[3:]),
                "source_rows": [first.number, second.number],
                "canonical_source_row": first.number,
            })
    output, positions = render_view(text, rows, canonical, replacements)
    output_rows = parse_rows(output, "validation")
    mapping = []
    for row in rows:
        destination = positions[canonical[row.number]]
        target = output_rows[destination["output_row"] - 1]
        assert target.context == row.context
        assert target.cells[2:] == row.cells[2:]
        assert row.cells[1] in target.cells[1].split("/")
        mapping.append({
            "source_row": row.number,
            "source_line": row.line,
            "source_cells": list(row.cells),
            "resolved_method": row.context[0],
            "action": (
                "merged_loc_faith" if canonical[row.number] != row.number
                else "retained_with_merged_criterion" if row.number in replacements
                else "retained"
            ),
            "canonical_source_row": canonical[row.number],
            "canonical_source_line": rows[canonical[row.number] - 1].line,
            **destination,
        })
    return output, {
        "source_data_rows": len(rows),
        "output_data_rows": len(output_rows),
        "removed_repeated_rows": len(rows) - len(output_rows),
        "merged_selections": merged,
        "row_mapping": mapping,
    }


def ablation_view(text: str) -> tuple[str, dict]:
    rows = parse_rows(text, "ablation")
    centers: dict[str, dict] = {}
    canonical = {row.number: row.number for row in rows}
    for row in rows:
        if r"\textbf{" not in row.cells[2]:
            continue
        center, factor = row.context
        value = unbold(row.cells[2])
        if center not in centers:
            centers[center] = {
                "canonical_source_row": row.number,
                "metrics": list(row.cells[3:]),
                "selected_parameters": [],
            }
        record = centers[center]
        assert record["metrics"] == list(row.cells[3:]), (
            f"Selected-center metrics differ: {center}, row {row.number}"
        )
        assert factor not in [entry["factor"] for entry in record["selected_parameters"]]
        record["selected_parameters"].append({
            "factor": factor,
            "value": value,
            "source_row": row.number,
            "source_line": row.line,
            "note_tex": parameter_text(factor, value),
        })
        canonical[row.number] = record["canonical_source_row"]
    notes = []
    for center, record in centers.items():
        parameters = ", ".join(entry["note_tex"] for entry in record["selected_parameters"])
        notes.append(center + ": " + parameters)
    prefix = (
        r"\noindent Selected centers (one bold row each): "
        + "; ".join(notes) + r".\par" + "\n"
    )
    # If the first row of a factor block was the redundant center, its next
    # row must explicitly inherit the removed row's center and factor labels.
    replacements = {}
    seen_contexts = set()
    for row in rows:
        if canonical[row.number] != row.number:
            continue
        if row.context not in seen_contexts:
            seen_contexts.add(row.context)
            cells = list(row.cells)
            cells[:2] = row.context
            if tuple(cells) != row.cells:
                replacements[row.number] = tuple(cells)
    output, positions = render_view(text, rows, canonical, replacements, prefix)
    output_rows = parse_rows(output, "ablation")
    mapping = []
    for center, record in centers.items():
        record.update(positions[record["canonical_source_row"]])
        record["canonical_source_line"] = rows[record["canonical_source_row"] - 1].line
    for row in rows:
        destination = positions[canonical[row.number]]
        target = output_rows[destination["output_row"] - 1]
        assert target.cells[3:] == row.cells[3:]
        assert target.context[0] == row.context[0]
        entry = {
            "source_row": row.number,
            "source_line": row.line,
            "source_cells": list(row.cells),
            "resolved_center": row.context[0],
            "resolved_factor": row.context[1],
            "action": (
                "deduplicated_center" if canonical[row.number] != row.number
                else "retained_with_explicit_context" if row.number in replacements
                else "retained"
            ),
            "canonical_source_row": canonical[row.number],
            "canonical_source_line": rows[canonical[row.number] - 1].line,
            **destination,
        }
        if canonical[row.number] == row.number:
            assert target.context == row.context
            assert target.cells[2:] == row.cells[2:]
        else:
            parameter = next(
                parameter for parameter in centers[row.context[0]]["selected_parameters"]
                if parameter["source_row"] == row.number
            )
            assert parameter["note_tex"] in prefix
            entry["selected_value_preserved_in_note"] = parameter["note_tex"]
            entry["note_line"] = 1
        mapping.append(entry)
    return output, {
        "source_data_rows": len(rows),
        "output_data_rows": len(output_rows),
        "removed_repeated_rows": len(rows) - len(output_rows),
        "selected_centers": centers,
        "row_mapping": mapping,
    }


def validation_matrix() -> tuple[str, dict]:
    """Join architecture-specific ranks, keeping full configurations canonical."""
    models = ("vit_b16", "vgg16", "resnet50")
    methods = (
        "SmGrad", "IntGrad", r"LRP-$\varepsilon$", r"LRP-$\gamma$",
        "AttnLRP", "DAVE", "AR", "SG", "RG", "RG+Eq",
    )
    records = []
    source_files = []
    ci_files = []
    lookup = {}
    normalize = lambda value: re.sub(r"\s+", "", value.replace(r"\allowbreak", ""))
    for model in models:
        source_path = SOURCE / f"val_selection_{model}_tabular.tex"
        ci_path = SOURCE / f"test_{model}_ci_longtable.tex"
        source = (ROOT / source_path).read_text(encoding="utf-8")
        ci_text = (ROOT / ci_path).read_text(encoding="utf-8")
        source_files.append({"path": str(source_path), "sha256": digest(source)})
        ci_files.append({"path": str(ci_path), "sha256": digest(ci_text)})
        ci_rows = {}
        for line_number, line in enumerate(ci_text.splitlines(), 1):
            if "&" not in line or not line.rstrip().endswith(r"\\"):
                continue
            cells = [cell.strip() for cell in line.rstrip()[:-2].split("&")]
            if len(cells) == 10 and cells[0] != "Method":
                ci_rows[cells[0]] = (line_number, cells[1])
        for row in parse_rows(source, "validation"):
            match = re.fullmatch(r"(.+) \((\d+)\)", row.context[0])
            assert match is not None
            method, count = match.groups()
            criterion = row.cells[1]
            if criterion == "fixed":
                identifier = method
                assert count == "1" and row.cells[3:] == ("n/a", "n/a")
            elif criterion == "anchor":
                identifier = method + " anchor"
            else:
                identifier = method + " (" + criterion + ")"
                if identifier not in ci_rows:
                    assert criterion in {"loc", "faith"}
                    identifier = method + " (loc/faith)"
            assert identifier in ci_rows, (model, identifier)
            ci_line, ci_config = ci_rows[identifier]
            assert normalize(ci_config) == normalize(row.cells[2]), (
                model, identifier, ci_config, row.cells[2]
            )
            record = {
                "architecture": model,
                "source": str(source_path),
                "source_row": row.number,
                "source_line": row.line,
                "source_cells": list(row.cells),
                "method": method,
                "criterion": criterion,
                "declared_grid_count": int(count),
                "configuration": row.cells[2],
                "rank_sums": list(row.cells[3:]),
                "canonical_configuration_source": str(ci_path),
                "canonical_configuration_line": ci_line,
                "canonical_configuration_identifier": identifier,
                "canonical_configuration_tex": ci_config,
            }
            records.append(record)
            if criterion != "fixed":
                assert method in methods
                lookup[(model, method, criterion)] = record
    lines = [
        r"\begin{tabular}{@{}ll rc rc rc@{}}",
        r"\toprule",
        r"Method & Selection & \multicolumn{2}{c}{ViT-B/16} & \multicolumn{2}{c}{VGG-16} & \multicolumn{2}{c}{ResNet-50} \\",
        r" & & $n$ & $(r_{\mathrm{loc}},r_{\mathrm{faith}})$ & $n$ & $(r_{\mathrm{loc}},r_{\mathrm{faith}})$ & $n$ & $(r_{\mathrm{loc}},r_{\mathrm{faith}})$ \\",
        r"\midrule",
    ]
    matrix_rows = []
    for method in methods:
        selections = (
            ("loc/faith",) if method in {"DAVE", "AR"}
            else ("loc", "faith", "anchor") if method in {"RG", "RG+Eq"}
            else ("loc", "faith")
        )
        for selection_number, selection in enumerate(selections):
            cells = [method if selection_number == 0 else "", selection]
            matrix_row = len(matrix_rows) + 1
            source_records = []
            for model_index, model in enumerate(models):
                criteria = ("loc", "faith") if selection == "loc/faith" else (selection,)
                matched = [lookup[(model, method, criterion)] for criterion in criteria
                           if (model, method, criterion) in lookup]
                if not matched:
                    cells.extend(["---" if selection_number == 0 else "", "---"])
                    continue
                first = matched[0]
                for record in matched:
                    assert record["rank_sums"] == first["rank_sums"]
                    assert record["configuration"] == first["configuration"]
                    assert record["declared_grid_count"] == first["declared_grid_count"]
                pair = "$({},{})$".format(*first["rank_sums"])
                cells.extend([
                    str(first["declared_grid_count"]) if selection_number == 0 else "", pair
                ])
                for record in matched:
                    record.update({
                        "matrix_row": matrix_row,
                        "matrix_line": len(lines) + 1,
                        "matrix_rank_column": 4 + 2 * model_index,
                        "matrix_rank_tex": pair,
                        "matrix_count_column": 3 + 2 * model_index,
                        "matrix_count_first_selection": selections[0],
                    })
                    source_records.append({
                        "architecture": model, "source_row": record["source_row"]
                    })
            lines.append(" & ".join(cells) + r" \\")
            matrix_rows.append({
                "matrix_row": matrix_row, "method": method, "selection": selection,
                "cells": cells, "source_records": source_records,
            })
        if method != methods[-1]:
            lines.append(r"\addlinespace")
    lines.extend([
        r"\bottomrule", r"\end{tabular}", r"\par\smallskip\noindent",
        r"$n$: declared grid size (Table~\ref{ptnb:tab:main-search-grid}); ranks use admitted configurations (Section~\ref{ptnb:app:selection}).",
        r"Configurations are identified by method and selection in Tables~\ref{ptnb:tab:test-ci-vit}, \ref{ptnb:tab:test-ci-vgg} and~\ref{ptnb:tab:test-ci-resnet}.",
        r"Fixed methods have one configuration and n/a rank-sums. A dash marks an architecture on which the method was not evaluated.",
    ])
    for record in records:
        if record["criterion"] == "fixed":
            record["representation"] = "fixed-method note and canonical full-CI configuration"
            record["note_line"] = len(lines)
        else:
            assert "matrix_row" in record
            target = matrix_rows[record["matrix_row"] - 1]
            assert target["cells"][record["matrix_rank_column"] - 1] == record["matrix_rank_tex"]
            count_row = next(row for row in matrix_rows if row["method"] == record["method"])
            assert count_row["cells"][record["matrix_count_column"] - 1] == str(record["declared_grid_count"])
            record["matrix_count_row"] = count_row["matrix_row"]
    return "\n".join(lines) + "\n", {
        "output": str(MATRIX),
        "source_files": source_files,
        "canonical_configuration_files": ci_files,
        "source_records": len(records),
        "unique_configuration_records": len({
            (record["architecture"], record["canonical_configuration_identifier"])
            for record in records
        }),
        "fixed_records_represented_by_note": sum(record["criterion"] == "fixed" for record in records),
        "output_data_rows": len(matrix_rows),
        "matrix_rows": matrix_rows,
        "record_mapping": records,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify without writing")
    args = parser.parse_args()
    audit = {
        "baseline_commit": "b43bc24",
        "generator": "reports/single-pdf/build_experiment_views.py",
        "policy": [
            "Original generated inputs are unchanged.",
            "Validation criteria merge only for identical method, configuration and both rank sums.",
            "Ablation center rows merge only within the same method and selection criterion, with all six displayed metrics identical.",
            "Every selected factor value is retained in the center note; every distinct non-center row is retained in source order.",
            "The table structure and typography are unchanged; inherited labels are made explicit where needed.",
        ],
        "tables": [],
    }
    artifacts = {}
    sources = {}
    for name, kind in TABLES:
        source_path = SOURCE / name
        output_path = DESTINATION / name
        source = (ROOT / source_path).read_text(encoding="utf-8")
        sources[source_path] = source
        output, table_audit = (
            validation_view(source) if kind == "validation" else ablation_view(source)
        )
        artifacts[output_path] = output
        audit["tables"].append({
            "kind": kind,
            "source": source_path.as_posix(),
            "output": output_path.as_posix(),
            "source_sha256": digest(source),
            "output_sha256": digest(output),
            **table_audit,
        })
    matrix, matrix_audit = validation_matrix()
    artifacts[MATRIX] = matrix
    audit["validation_matrix"] = {"output_sha256": digest(matrix), **matrix_audit}
    audit["totals"] = {
        key: sum(table[key] for table in audit["tables"])
        for key in ("source_data_rows", "output_data_rows", "removed_repeated_rows")
    }
    artifacts[AUDIT] = json.dumps(audit, indent=2, ensure_ascii=False) + "\n"
    for path, text in artifacts.items():
        target = ROOT / path
        if args.check:
            if not target.exists() or target.read_text(encoding="utf-8") != text:
                raise SystemExit(f"Stale or missing generated artifact: {path}")
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text, encoding="utf-8")
    for path, text in sources.items():
        assert (ROOT / path).read_text(encoding="utf-8") == text
    mode = "Verified" if args.check else "Generated"
    totals = audit["totals"]
    print(
        f"{mode} {len(TABLES)} views: {totals['source_data_rows']} -> "
        f"{totals['output_data_rows']} data rows; "
        f"{totals['removed_repeated_rows']} exact repeats merged."
    )
    print(
        f"{mode} validation matrix: {matrix_audit['source_records']} source records, "
        f"{matrix_audit['unique_configuration_records']} canonical configurations, "
        f"{matrix_audit['output_data_rows']} matrix rows; all ranks and grid counts verified."
    )


if __name__ == "__main__":
    main()
