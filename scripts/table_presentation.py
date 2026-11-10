#!/usr/bin/env python3
"""Apply documented presentation changes to the conference table output.

Measured values and confidence intervals are unchanged. Entirely unmeasured
metric columns are omitted; nonnumeric placeholders acquire explicit meanings.
The source tables remain untouched for provenance and comparison.
"""
from __future__ import annotations

import re
from pathlib import Path
from normalize_thesis_terms import normalize

DASH = {"-", "--", "---", "$-$", "–", "—"}


def cells(line: str) -> tuple[list[str], str] | None:
    """The source writers put each outer row on one physical line."""
    if "&" not in line or not line.rstrip().endswith(r"\\"):
        return None
    body = line.rstrip()[:-2].rstrip()
    return [part.strip() for part in re.split(r"(?<!\\)&", body)], r" \\"


def present(filename: str, text: str) -> tuple[str, list[dict]]:
    changes: list[dict] = []
    lines = text.splitlines()
    if filename.startswith("test_") and filename.endswith("_ci_longtable.tex"):
        headers = [cells(line)[0] for line in lines if line.startswith("Method & Config &")]
        if len(headers) != 2 or headers[0] != headers[1]:
            raise ValueError(f"Unexpected repeated table header in {filename}")
        header = headers[0]
        start = lines.index(r"\endlastfoot") + 1
        rows = [cells(line)[0] for line in lines[start:] if cells(line)]
        if not rows or any(len(row) != len(header) for row in rows):
            raise ValueError(f"Unexpected data-row shape in {filename}")
        drop = [i for i in range(2, len(header))
                if all(row[i] in DASH or not row[i] for row in rows)]
        if drop:
            # Upstream CI tables have two descriptor columns followed by the
            # same simple centered metric specification. Refuse other layouts.
            old = r"@{\hspace{2.5pt}}c"
            if lines[0].count(old) != len(header) - 2:
                raise ValueError(f"Unexpected column specification in {filename}")
            for _ in drop:
                at = lines[0].rfind(old)
                lines[0] = lines[0][:at] + lines[0][at + len(old):]
            for n, line in enumerate(lines):
                row = cells(line)
                if row and len(row[0]) == len(header):
                    lines[n] = " & ".join(v for i, v in enumerate(row[0]) if i not in drop) + row[1]
                lines[n] = lines[n].replace(r"\multicolumn{" + str(len(header)) + "}",
                    r"\multicolumn{" + str(len(header) - len(drop)) + "}")
            changes.append({"action": "omit_unmeasured_columns", "columns": [header[i] for i in drop],
                            "data_rows": len(rows)})
        if r"\hspace{2.5pt}" in lines[0]:
            lines[0] = lines[0].replace(r"\hspace{2.5pt}", r"\hspace{1.5pt}")
            changes.append({"action": "fit_thesis_width", "intercolumn_space_pt": 1.5})
        elif r"\hspace{2pt}" in lines[0]:
            lines[0] = lines[0].replace(r"\hspace{2pt}", r"\hspace{1.5pt}")
            changes.append({"action": "fit_thesis_width", "intercolumn_space_pt": 1.5})
        right_column = r">{\setlength{\RaggedRightRightskip}{0pt plus 1fil}\RaggedRight\arraybackslash}p{2.7cm}"
        plain_column = r">{\raggedright\arraybackslash}p{2.7cm}"
        if plain_column in lines[0]:
            lines[0] = lines[0].replace(
                plain_column, right_column,
            )
            changes.append({"action": "hyphenating_ragged_config_column"})
        elif "p{2.7cm}" in lines[0]:
            lines[0] = lines[0].replace(
                "p{2.7cm}", right_column
            )
            changes.append({"action": "hyphenating_ragged_config_column"})
    for n, line in enumerate(lines):
        row = cells(line)
        if not row:
            continue
        values, ending = row
        before = values.copy()
        if filename.startswith("test_") or filename == "main_vit_tabular.tex":
            if len(values) > 2 and values[1] in DASH:
                values[1] = "fixed"
        elif filename.startswith("val_selection_"):
            if len(values) == 5 and values[1] == "fixed":
                values = ["fixed" if i == 2 and v in DASH else
                          "n/a" if i >= 3 and v in DASH else v for i, v in enumerate(values)]
        elif filename.startswith("ablations_"):
            if len(values) > 3 and "+Eq" in values[1] and values[2] in DASH:
                values[2] = "on"
        elif filename == "per_image_corr_tabular.tex":
            # The paper suppresses only the diagonal of a correlation matrix.
            for i in range(2, min(6, len(values))):
                if values[i] == "$-$":
                    values[i] = "$1.00$"
        if values != before:
            lines[n] = " & ".join(values) + ending
            changes.append({"action": "clarify_placeholder", "line": n + 1,
                            "row": before[0], "before": before, "after": values})
    result, terminology = normalize("\n".join(lines) + "\n")
    if terminology:
        changes.append({"action": "canonical_terminology", "edits": terminology})
    return result, changes


def adapt_directory(directory: Path, filenames: list[str]) -> dict:
    changes = {}
    for name in filenames:
        path = directory / name
        updated, edits = present(name, path.read_text())
        if edits:
            path.write_text(updated)
            changes[name] = edits
    return changes
