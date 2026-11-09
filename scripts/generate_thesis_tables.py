#!/usr/bin/env python3
"""Regenerate available paper tables and optionally sync verified outputs."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shlex
import subprocess
import sys
import tempfile
import os
from pathlib import Path
from table_presentation import adapt_directory

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "scripts" / "table_sources.json"
PTNB_TARGET = ROOT / "tex" / "tables" / "ptnb_v2" / "generated"
NUMBER_RE = re.compile(
    r"(?<![A-Za-z_])[-+]?(?:\d{1,3}(?:,\d{3})+|\d+)(?:\.\d+)?(?:[eE][-+]?\d+)?"
)


def read_manifest() -> dict:
    return json.loads(MANIFEST.read_text())


def resolve_repo(code_root: Path, name: str, submodule_path: str) -> Path:
    """Accept the code parent, a clone directory, or the code root itself."""
    code_root = code_root.expanduser().resolve()
    short = submodule_path.rsplit("/", 1)[-1]
    candidates = [code_root / short, code_root / name, code_root]
    for candidate in candidates:
        if name == "playing_backward" and (candidate / "reproduce" / "make_tables.py").is_file():
            return candidate
        if name == "hidden_monotonicity" and (candidate / "dc_decomposition").is_dir():
            return candidate
    expected = ", ".join(str(x) for x in candidates[:-1])
    raise FileNotFoundError(f"Cannot find {name} beneath {code_root}; tried {expected}")


def numeric_tokens(path: Path) -> list[str]:
    """Extract numeric tokens while ignoring LaTeX comments."""
    lines = []
    for line in path.read_text(errors="replace").splitlines():
        # Ignore unescaped TeX comments; a backslash before % makes it data.
        kept = []
        for i, char in enumerate(line):
            if char == "%":
                slash_count = 0
                j = i - 1
                while j >= 0 and line[j] == "\\":
                    slash_count += 1
                    j -= 1
                if slash_count % 2 == 0:
                    break
            kept.append(char)
        lines.append("".join(kept))
    return NUMBER_RE.findall("\n".join(lines))


def canonical_tex(path: Path) -> str:
    """Compare content after comment removal and whitespace normalization."""
    lines = []
    for line in path.read_text(errors="replace").splitlines():
        kept = []
        for i, char in enumerate(line):
            if char == "%":
                slash_count = 0
                j = i - 1
                while j >= 0 and line[j] == "\\":
                    slash_count += 1
                    j -= 1
                if slash_count % 2 == 0:
                    break
            kept.append(char)
        lines.append("".join(kept))
    return "".join("".join(lines).split())


def compare_numeric_values(output: Path, thesis: Path) -> tuple[bool, str]:
    actual = numeric_tokens(output)
    expected = numeric_tokens(thesis)
    if actual == expected:
        return True, f"{output.name}: {len(actual)} numeric tokens match"
    limit = min(len(actual), len(expected))
    mismatch = next((i for i in range(limit) if actual[i] != expected[i]), limit)
    lo = max(0, mismatch - 3)
    hi_actual = min(len(actual), mismatch + 4)
    hi_expected = min(len(expected), mismatch + 4)
    return False, (
        f"{output.name}: numeric values differ at token {mismatch + 1}; "
        f"generated={actual[lo:hi_actual]!r}, thesis={expected[lo:hi_expected]!r}; "
        f"token counts {len(actual)} vs {len(expected)}"
    )


def compare_tex(output: Path, thesis: Path) -> tuple[bool, str]:
    if canonical_tex(output) == canonical_tex(thesis):
        return True, f"{output.name}: canonical TeX content matches (comments/whitespace ignored)"
    same, numeric_detail = compare_numeric_values(output, thesis)
    if not same:
        return False, numeric_detail
    return False, (
        f"{output.name}: numeric values match but TeX structure, labels, or row associations differ; "
        "refusing automatic synchronization"
    )


def check_outputs(output_dir: Path, generated: list[str]) -> tuple[list[str], list[str]]:
    matches: list[str] = []
    mismatches: list[str] = []
    for filename in generated:
        output = output_dir / filename
        thesis = PTNB_TARGET / filename
        if not output.is_file():
            mismatches.append(f"{filename}: upstream generator did not produce this file")
        elif not thesis.is_file():
            mismatches.append(f"{filename}: thesis target is missing: {thesis}")
        else:
            same, detail = compare_tex(output, thesis)
            (matches if same else mismatches).append(detail)
    return matches, mismatches


def copy_command(output_dir: Path, generated: list[str]) -> str:
    srcs = " ".join(shlex.quote(str(output_dir / name)) for name in generated)
    return f"cp -i {srcs} {shlex.quote(str(PTNB_TARGET))}/"


def main() -> int:
    manifest = read_manifest()
    ptnb = manifest["repositories"]["playing_backward"]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--code-root",
        type=Path,
        default=ROOT / "code",
        help="Parent directory containing code/playing_backward or code-root itself; default: ./code",
    )
    parser.add_argument(
        "--python",
        default=sys.executable,
        help="Python executable with the upstream table generator dependencies (including PyTorch)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Write generated tables to this review directory; no thesis files are changed",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Compare canonical TeX content and values with current thesis tables",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="Atomically update thesis tables after all canonical comparisons pass",
    )
    args = parser.parse_args()
    if args.write and not args.check:
        parser.error("--write requires --check so values and table structure are verified first")

    try:
        repo = resolve_repo(args.code_root, "playing_backward", ptnb["submodule_path"])
    except FileNotFoundError as exc:
        parser.error(str(exc))

    head_result = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True, capture_output=True, check=False
    )
    actual_commit = head_result.stdout.strip() if head_result.returncode == 0 else None
    dirty_result = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=no"],
        cwd=repo, text=True, capture_output=True, check=False,
    )
    tracked_dirty = dirty_result.returncode != 0 or bool(dirty_result.stdout.strip())
    print(f"Source commit: {actual_commit or 'unavailable'} (pinned {ptnb['verified_commit']})")
    if args.write and actual_commit != ptnb["verified_commit"]:
        parser.error("--write requires the code checkout to match the manifest's verified_commit")
    if args.write and tracked_dirty:
        parser.error("--write requires unmodified tracked upstream code and result summaries")

    output_dir: Path
    if args.output is None:
        output_dir = Path(tempfile.mkdtemp(prefix="thesis-table-review-"))
        print(f"Using temporary review output: {output_dir}")
    else:
        output_dir = args.output.expanduser().resolve()
        if output_dir == PTNB_TARGET.resolve():
            parser.error(f"--output may not be the live thesis table directory: {PTNB_TARGET}")
        if output_dir.exists() and any(output_dir.iterdir()):
            parser.error(f"--output must be empty to prevent overwriting files: {output_dir}")
        output_dir.mkdir(parents=True, exist_ok=True)

    results_dir = repo / ptnb["table_generation"]["results_input"]
    if not results_dir.is_dir():
        parser.error(f"Shipped result summaries not found: {results_dir}")

    command = [
        args.python,
        "-m",
        ptnb["table_generation"]["generator_module"],
        "--results",
        str(results_dir),
        "--out",
        str(output_dir),
        "--strict",
    ]
    print("Running summary-only table generation; no model or dataset evaluation is run:")
    print("  " + " ".join(shlex.quote(part) for part in command))
    completed = subprocess.run(command, cwd=repo, check=False)
    if completed.returncode:
        print(
            f"Upstream table generation exited {completed.returncode}. "
            "No thesis tables were modified.",
            file=sys.stderr,
        )
        return completed.returncode

    generated = ptnb["table_generation"]["generated_outputs"]
    missing = [
        item["file"] for item in ptnb["table_generation"]["unavailable_from_results_summary"]
    ]
    produced = [name for name in generated if (output_dir / name).is_file()]
    absent = [name for name in generated if not (output_dir / name).is_file()]
    if absent:
        print("Expected upstream outputs missing: " + ", ".join(absent), file=sys.stderr)
        return 2

    raw_hashes = {name: hashlib.sha256((output_dir / name).read_bytes()).hexdigest()
                  for name in generated}
    presentation_changes = adapt_directory(output_dir, generated)

    print(f"Generated {len(produced)} summary-backed tables in {output_dir}.")
    print(
        f"Not generated from shipped summaries ({len(missing)} diagnostics): "
        + ", ".join(missing)
    )

    if args.check:
        matches, mismatches = check_outputs(output_dir, generated)
        for result in matches:
            print("MATCH " + result)
        for result in mismatches:
            print("MISMATCH " + result, file=sys.stderr)
        if mismatches:
            print("Table content checks failed; no thesis files were changed.", file=sys.stderr)
            return 1
        if args.write:
            for filename in generated:
                target = PTNB_TARGET / filename
                target.parent.mkdir(parents=True, exist_ok=True)
                fd, temp_name = tempfile.mkstemp(prefix=f".{filename}.", dir=target.parent)
                try:
                    with os.fdopen(fd, "wb") as temp_file:
                        temp_file.write((output_dir / filename).read_bytes())
                        temp_file.flush()
                        os.fsync(temp_file.fileno())
                    os.replace(temp_name, target)
                finally:
                    if os.path.exists(temp_name):
                        os.unlink(temp_name)
            print(f"Canonical checks passed; atomically updated {len(generated)} thesis tables.")
        else:
            print("Canonical checks passed. No thesis files were changed.")
    else:
        print("No thesis files were changed. Review the output, then rerun with --check --write to sync.")

    provenance = {
        "generator": ptnb["table_generation"]["generator_module"],
        "results_input": str(results_dir),
        "results_only": True,
        "strict": True,
        "repository": ptnb["url"],
        "expected_commit": ptnb["verified_commit"],
        "actual_commit": actual_commit,
        "tracked_source_modified": tracked_dirty,
        "raw_upstream_sha256": raw_hashes,
        "thesis_presentation_changes": presentation_changes,
        "outputs": {
            name: hashlib.sha256((output_dir / name).read_bytes()).hexdigest()
            for name in generated
        },
        "unavailable_from_results_summary": missing,
    }
    (output_dir / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    if provenance["actual_commit"] != provenance["expected_commit"]:
        print(
            f"WARNING: source HEAD {provenance['actual_commit']} does not match pinned "
            f"commit {provenance['expected_commit']}; provenance.json records both.",
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
