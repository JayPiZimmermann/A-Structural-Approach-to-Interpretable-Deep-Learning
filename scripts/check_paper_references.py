#!/usr/bin/env python3
"""Audit active references in the two source papers against the thesis.

The checker follows recursive TeX input/include files (including the generated
longtable helpers), strips TeX comments before collecting commands, applies only
the explicit aliases recorded in reports/*-citation-aliases.json, and checks
both active thesis citations and bibliography records. It is offline and writes
a deterministic JSON report.

Run from any directory with:
    python3 scripts/check_paper_references.py --check
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import unicodedata
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
REPORT = ROOT / "reports" / "paper-reference-coverage.json"
PTNB_ALIAS_FILE = ROOT / "reports" / "paper-v2-citation-aliases.json"
HM_ALIAS_FILE = ROOT / "reports" / "hidden-monotonicity-citation-aliases.json"

PAPERS = {
    "hidden_monotonicity": {
        "root": ROOT / "arxive/hiddenMonotonicity/main.tex",
        "bibliography": ROOT / "arxive/hiddenMonotonicity/references.bib",
        "supplemental_bibliography": None,
        "alias_file": HM_ALIAS_FILE,
        "kind": "bibtex",
    },
    "playing_the_network_backward_v2": {
        "root": ROOT / "arxive/playingTheNetworkBackward/main.tex",
        "bibliography": ROOT / "arxive/playingTheNetworkBackward/main.bbl",
        "supplemental_bibliography": None,
        "alias_file": PTNB_ALIAS_FILE,
        "kind": "bbl",
    },
}

THESIS_ROOT = ROOT / "tex/main.tex"
SUPPLEMENT_ROOT = ROOT / "tex/supplement.tex"
THESIS_BIB = ROOT / "tex/bibliography/references.bib"

CITATION_COMMANDS = {
    "cite", "citep", "citet", "citealp", "citealt", "citeauthor",
    "citeyear", "citeyearpar", "textcite", "parencite", "autocite",
    "nocite", "citeapp", "citepapp", "citetapp",
}
INCLUDE_COMMANDS = {"input", "include", "appinputgen", "appinputgenlt", "appinputgenci"}


def relpath(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return path.resolve().as_posix()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(text: str) -> str:
    """Remove TeX comments while respecting escaped percent signs."""
    kept: list[str] = []
    for line in text.splitlines(keepends=True):
        cut = None
        for i, char in enumerate(line):
            if char != "%":
                continue
            slashes = 0
            j = i - 1
            while j >= 0 and line[j] == "\\":
                slashes += 1
                j -= 1
            if slashes % 2 == 0:
                cut = i
                break
        kept.append(line if cut is None else line[:cut] + ("\n" if line.endswith("\n") else ""))
    return "".join(kept)


def read_text(path: Path) -> str:
    return strip_comments(path.read_text(encoding="utf-8", errors="replace"))


def resolve_tex_path(raw: str, including_file: Path, project_root: Path) -> Path | None:
    name = raw.strip()
    if not name or "#" in name or "\\" in name:
        return None
    path = Path(name)
    candidates = [path] if path.suffix else [path.with_suffix(".tex"), path]
    for candidate in candidates:
        for base in (project_root, including_file.parent):
            full = (base / candidate).resolve()
            if full.is_file():
                return full
    return None


def tex_closure(root_file: Path, project_root: Path) -> tuple[list[Path], list[dict[str, str]]]:
    """Return ordered, recursive active TeX inputs and unresolved include paths."""
    visited: set[Path] = set()
    ordered: list[Path] = []
    unresolved: list[dict[str, str]] = []
    command_re = re.compile(
        r"\\([A-Za-z]+)\*?(?:\s*\[[^]]*\])*\s*\{([^{}]+)\}"
    )

    def visit(path: Path, parent_command: str = "root", parent_file: Path | None = None) -> None:
        path = path.resolve()
        if path in visited:
            return
        if not path.is_file():
            if parent_file is not None:
                unresolved.append({"from": relpath(parent_file), "command": parent_command, "path": str(path)})
            return
        visited.add(path)
        ordered.append(path)
        text = read_text(path)
        for match in command_re.finditer(text):
            command, raw = match.group(1), match.group(2).strip()
            if command not in INCLUDE_COMMANDS:
                continue
            # Macro definitions such as \input{#1} are not concrete includes.
            if "#" in raw:
                continue
            included = resolve_tex_path(raw, path, project_root)
            if included is None:
                unresolved.append({"from": relpath(path), "command": command, "path": raw})
                continue
            visit(included, command, path)

    visit(root_file)
    return ordered, unresolved


def citation_keys(text: str) -> dict[str, list[dict[str, Any]]]:
    found: dict[str, list[dict[str, Any]]] = {}
    command_re = re.compile(
        r"\\(" + "|".join(sorted(CITATION_COMMANDS, key=len, reverse=True))
        + r")\*?(?:\s*\[[^]]*\])*\s*\{([^{}]+)\}"
    )
    for match in command_re.finditer(text):
        command = match.group(1)
        for raw_key in match.group(2).split(","):
            key = raw_key.strip()
            if not key or key == "*":
                continue
            found.setdefault(key, []).append({"command": command})
    return found


def tex_include_manifest(paths: list[Path]) -> dict[str, Any]:
    merged: dict[str, list[dict[str, Any]]] = {}
    for path in paths:
        for key, occurrences in citation_keys(read_text(path)).items():
            merged.setdefault(key, []).extend(
                [{"file": relpath(path), **occurrence} for occurrence in occurrences]
            )
    return merged


def bib_entries(path: Path) -> dict[str, dict[str, str]]:
    """Read BibTeX entries and common braced/quoted field values."""
    if not path or not path.is_file():
        return {}
    text = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
    entries: dict[str, dict[str, str]] = {}
    start_re = re.compile(r"@([A-Za-z]+)\s*([({])\s*([^,\s]+)\s*,")
    for match in start_re.finditer(text):
        key = match.group(3)
        body_start = match.end()
        opener = match.group(2)
        closer = "}" if opener == "{" else ")"
        depth = 1
        in_quote = False
        escaped = False
        pos = body_start
        while pos < len(text) and depth:
            ch = text[pos]
            if ch == '"' and not escaped:
                in_quote = not in_quote
            elif not in_quote and not escaped:
                if ch == opener:
                    depth += 1
                elif ch == closer:
                    depth -= 1
            escaped = ch == "\\" and not escaped
            if ch != "\\":
                escaped = False
            pos += 1
        body = text[body_start:pos - 1]
        fields: dict[str, str] = {}
        pos = 0
        field_start_re = re.compile(r"([A-Za-z][A-Za-z0-9_-]*)\s*=\s*")
        while pos < len(body):
            while pos < len(body) and body[pos] in " \t\r\n,":
                pos += 1
            fm = field_start_re.match(body, pos)
            if not fm:
                break
            field_name = fm.group(1).lower()
            pos = fm.end()
            value_start = pos
            if pos < len(body) and body[pos] == "{":
                depth = 0
                escaped = False
                while pos < len(body):
                    ch = body[pos]
                    if ch == "{" and not escaped:
                        depth += 1
                    elif ch == "}" and not escaped:
                        depth -= 1
                        if depth == 0:
                            pos += 1
                            break
                    escaped = ch == "\\" and not escaped
                    if ch != "\\":
                        escaped = False
                    pos += 1
            elif pos < len(body) and body[pos] == '"':
                pos += 1
                escaped = False
                while pos < len(body):
                    ch = body[pos]
                    if ch == '"' and not escaped:
                        pos += 1
                        break
                    escaped = ch == "\\" and not escaped
                    if ch != "\\":
                        escaped = False
                    pos += 1
            else:
                while pos < len(body) and body[pos] != ",":
                    pos += 1
            fields[field_name] = bib_value(body[value_start:pos].strip())
            while pos < len(body) and body[pos] not in ",":
                pos += 1
            if pos < len(body) and body[pos] == ",":
                pos += 1
        entries[key] = fields
    return entries


def bib_value(raw: str) -> str:
    if raw.startswith("{"):
        depth = 0
        escaped = False
        for i, ch in enumerate(raw):
            if ch == "{" and not escaped:
                depth += 1
            elif ch == "}" and not escaped:
                depth -= 1
                if depth == 0:
                    return raw[1:i]
            escaped = ch == "\\" and not escaped
            if ch != "\\":
                escaped = False
        return raw[1:]
    if raw.startswith('"'):
        escaped = False
        for i in range(1, len(raw)):
            if raw[i] == '"' and not escaped:
                return raw[1:i]
            escaped = raw[i] == "\\" and not escaped
            if raw[i] != "\\":
                escaped = False
        return raw[1:]
    return raw.split("#", 1)[0].strip()


def source_bbl_entries(path: Path) -> dict[str, str]:
    if not path.is_file():
        return {}
    text = path.read_text(encoding="utf-8", errors="replace")
    result: dict[str, str] = {}
    entry_re = re.compile(
        r"\\bibitem(?:\[[^]]*\])?\{([^}]+)\}(.*?)(?=\\bibitem(?:\[[^]]*\])?\{|\\end\{thebibliography\})",
        re.S,
    )
    for match in entry_re.finditer(text):
        blocks = re.findall(r"\\newblock\s+(.*?)(?=\\newblock|\Z)", match.group(2), re.S)
        if blocks:
            result[match.group(1)] = blocks[0]
    return result


def normalize_title(value: str | None) -> str | None:
    if value is None:
        return None
    value = re.sub(r",?\s*(?:19|20)\d{2}[.]?\s*$", "", value)
    # BibTeX braces protect capitalization and often split a word into pieces;
    # they are not title word boundaries. Keep command arguments (e.g. accents)
    # while discarding formatting commands.
    value = re.sub(r"\\([A-Za-z]+)\*?(?:\{([^{}]*)\})?", lambda m: m.group(2) or "", value)
    value = re.sub(r"\\([{}%&#_$])", r"\1", value)
    value = value.replace("{", "").replace("}", "").replace("$", " ")
    value = unicodedata.normalize("NFKD", value).casefold()
    value = "".join(ch for ch in value if not unicodedata.combining(ch))
    return " ".join(re.findall(r"[a-z0-9]+", value))


def title_matches(source_title: str | None, thesis_title: str | None) -> bool | None:
    a, b = normalize_title(source_title), normalize_title(thesis_title)
    if not a or not b:
        return None
    return a == b


def load_aliases(path: Path) -> dict[str, str]:
    return json.loads(path.read_text(encoding="utf-8"))


def source_refs_for_paper(name: str, paper: dict[str, Any], tex_files: list[Path], tex_refs: dict[str, list[dict[str, Any]]]) -> tuple[dict[str, dict[str, Any]], dict[str, str]]:
    aliases = load_aliases(paper["alias_file"])
    bib = bib_entries(paper["bibliography"]) if paper["kind"] == "bibtex" else {}
    bbl = source_bbl_entries(paper["bibliography"]) if paper["kind"] == "bbl" else {}
    appbib: dict[str, str] = {}
    for path in tex_files:
        text = read_text(path)
        for match in re.finditer(r"\\appbibitem\s*\{", text):
            key, pos = balanced_group(text, match.end() - 1)
            value, _ = balanced_group(text, pos)
            if key and value:
                appbib[key.strip()] = value

    keys = set(tex_refs)
    if name == "playing_the_network_backward_v2":
        # The original v2 bibliography is the authoritative 72-item source list.
        keys.update(bbl)
    keys.update(appbib)
    result: dict[str, dict[str, Any]] = {}
    for source_key in sorted(keys):
        canonical_key = aliases.get(source_key, source_key)
        source_title = None
        title_source = None
        if source_key in bib:
            source_title = bib[source_key].get("title")
            title_source = relpath(paper["bibliography"])
        elif source_key in bbl:
            source_title = bbl[source_key]
            title_source = relpath(paper["bibliography"]) + " (rendered source bibliography title field)"
        elif source_key in appbib:
            # Manual appendix references are actual bibliography entries in this
            # paper, even though they are not represented in its BibTeX database.
            source_title = appbib[source_key]
            title_source = relpath(paper["root"]) + " (explicit appbibitem entry)"
        result[source_key] = {
            "canonical_thesis_key": canonical_key,
            "source_occurrences": tex_refs.get(source_key, []),
            "source_bibliography_item": source_key in bib or source_key in bbl or source_key in appbib,
            "source_title": source_title,
            "source_title_location": title_source,
        }
    return result, aliases


def balanced_group(text: str, open_pos: int) -> tuple[str | None, int]:
    """Return a brace-delimited argument and the position after its close."""
    if open_pos >= len(text) or text[open_pos] != "{":
        return None, open_pos
    depth = 0
    escaped = False
    for pos in range(open_pos, len(text)):
        ch = text[pos]
        if ch == "{" and not escaped:
            depth += 1
        elif ch == "}" and not escaped:
            depth -= 1
            if depth == 0:
                return text[open_pos + 1:pos], pos + 1
        escaped = ch == "\\" and not escaped
        if ch != "\\":
            escaped = False
    return None, len(text)


def build_report() -> tuple[dict[str, Any], bool]:
    thesis_files, thesis_unresolved = tex_closure(THESIS_ROOT, ROOT / "tex")
    main_files = list(thesis_files)
    supplement_files: list[Path] = []
    if SUPPLEMENT_ROOT.is_file():
        supplement_files, supplement_unresolved = tex_closure(SUPPLEMENT_ROOT, ROOT / "tex")
        thesis_files = list(dict.fromkeys(thesis_files + supplement_files))
        thesis_unresolved.extend(supplement_unresolved)
    thesis_refs = tex_include_manifest(thesis_files)
    thesis_bib = bib_entries(THESIS_BIB)
    thesis_keys = set(thesis_bib)
    # The thesis may have a stale BBL after a citation is restored; raw .bib is
    # authoritative for availability, while the cached BBL is reported only.
    thesis_canonical_cites = set(thesis_refs)

    paper_reports: dict[str, Any] = {}
    all_missing: list[dict[str, str]] = []
    title_review: list[dict[str, Any]] = []
    unverified_aliases: list[dict[str, Any]] = []
    hash_paths: set[Path] = {THESIS_BIB, THESIS_ROOT}
    hash_paths.update(thesis_files)
    all_checks_pass = not thesis_unresolved

    for name, paper in PAPERS.items():
        source_files, unresolved = tex_closure(paper["root"], paper["root"].parent)
        source_refs = tex_include_manifest(source_files)
        refs, aliases = source_refs_for_paper(name, paper, source_files, source_refs)
        source_bib = paper["bibliography"]
        hash_paths.update(source_files)
        hash_paths.add(source_bib)
        if paper["alias_file"].is_file():
            hash_paths.add(paper["alias_file"])

        rows: list[dict[str, Any]] = []
        for source_key, item in refs.items():
            canonical = item["canonical_thesis_key"]
            thesis_cited = canonical in thesis_canonical_cites
            thesis_has_bib = canonical in thesis_keys
            thesis_title = thesis_bib.get(canonical, {}).get("title")
            source_title = item["source_title"]
            title_ok = title_matches(source_title, thesis_title)
            # App bibliography text may include author/venue as well as title;
            # require the canonical database title to be present in that actual
            # entry, rather than treating a display label as title metadata.
            if source_key.startswith("App") and source_title and thesis_title:
                s_norm = normalize_title(source_title) or ""
                t_norm = normalize_title(thesis_title) or ""
                title_ok = bool(t_norm and t_norm in s_norm)
            row = {
                "source_key": source_key,
                "canonical_thesis_key": canonical,
                "alias": aliases.get(source_key),
                "source_commands": sorted({x["command"] for x in item["source_occurrences"]}),
                "source_locations": sorted({x["file"] for x in item["source_occurrences"]}),
                "source_bibliography_item": item["source_bibliography_item"],
                "thesis_cited": thesis_cited,
                "thesis_bibliography_entry": thesis_has_bib,
                "source_title": source_title,
                "thesis_bibliography_title": thesis_title,
                "title_match": title_ok,
                "title_verification_source": item["source_title_location"],
            }
            rows.append(row)
            failures = []
            if not thesis_cited:
                failures.append("not_cited_in_thesis")
            if not thesis_has_bib:
                failures.append("missing_thesis_bibliography_entry")
            if not item["source_bibliography_item"]:
                failures.append("not_in_source_bibliography")
            if failures:
                missing = {"paper": name, "source_key": source_key, "canonical_thesis_key": canonical, "failures": failures}
                all_missing.append(missing)
            if title_ok is False:
                review = {
                    "paper": name,
                    "source_key": source_key,
                    "canonical_thesis_key": canonical,
                    "source_title": source_title,
                    "thesis_title": thesis_title,
                    "same_key_identity": source_key == canonical,
                }
                title_review.append(review)
                if source_key != canonical:
                    unverified_aliases.append(review)

        source_citation_keys = set(source_refs)
        source_ref_keys = set(refs)
        paper_report = {
            "source_tex_root": relpath(paper["root"]),
            "active_tex_files": [relpath(path) for path in source_files],
            "unresolved_includes": unresolved,
            "active_source_citation_key_count": len(source_citation_keys),
            "source_reference_count": len(rows),
            "source_bibliography_item_count": sum(bool(row["source_bibliography_item"]) for row in rows),
            "alias_file": relpath(paper["alias_file"]),
            "reference_checks": rows,
        }
        if name == "playing_the_network_backward_v2":
            paper_report["source_bbl_item_count"] = len(source_bbl_entries(source_bib))
            paper_report["source_bbl_all_represented"] = all(key in source_ref_keys for key in source_bbl_entries(source_bib))
        paper_reports[name] = paper_report
        if unresolved:
            all_checks_pass = False

    # Confirm the historic HM citation not cited inline in the body is still
    # present through its declared main-file nocite; this naturally appears in
    # source citation occurrences and is checked like every other citation.
    hm_ziegler = next(
        (row for row in paper_reports["hidden_monotonicity"]["reference_checks"] if row["canonical_thesis_key"] == "Ziegler1995"),
        None,
    )

    for row in all_missing:
        all_checks_pass = False
    if unverified_aliases:
        all_checks_pass = False
    bbl_path = ROOT / "tex/main.bbl"
    report = {
        "schema_version": 1,
        "title": "Active paper reference coverage against thesis and technical supplement",
        "offline": True,
        "source_projects": ["Hidden Monotonicity", "Playing the Network Backward v2"],
        "thesis_tex_root": relpath(THESIS_ROOT),
        "companion_tex_root": relpath(SUPPLEMENT_ROOT) if supplement_files else None,
        "reference_scope": "Main thesis and companion technical supplement together",
        "main_cited_key_count": len(tex_include_manifest(main_files)),
        "supplement_cited_key_count": len(tex_include_manifest(supplement_files)),
        "thesis_active_tex_files": [relpath(path) for path in thesis_files],
        "thesis_unresolved_includes": thesis_unresolved,
        "thesis_cited_key_count": len(thesis_canonical_cites),
        "thesis_bibliography_entry_count": len(thesis_keys),
        "cached_thesis_bbl": {
            "path": relpath(bbl_path),
            "present": bbl_path.is_file(),
            "entry_count": len(re.findall(r"^\s*\\entry\{([^}]+)\}", bbl_path.read_text(encoding="utf-8", errors="replace"), re.M)) if bbl_path.is_file() else 0,
            "note": "Informational only; a stale BBL does not override the active .bib source.",
        },
        "papers": paper_reports,
        "bibliography_title_review": title_review,
        "unverified_aliases": unverified_aliases,
        "source_hashes_sha256": {relpath(path): sha256(path) for path in sorted(hash_paths) if path.is_file()},
        "genuinely_missing_references": all_missing,
        "missing_count": len(all_missing),
        "hm_ziegler1995_check": {
            "canonical_key": "Ziegler1995",
            "source_key_present": hm_ziegler is not None,
            "source_commands": hm_ziegler["source_commands"] if hm_ziegler else [],
            "thesis_cited": hm_ziegler["thesis_cited"] if hm_ziegler else False,
            "thesis_bibliography_entry": hm_ziegler["thesis_bibliography_entry"] if hm_ziegler else False,
        },
        "check_passed": all_checks_pass,
    }
    return report, all_checks_pass


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="write the deterministic report and exit nonzero on missing references or unresolved active inputs")
    parser.add_argument("--report", type=Path, default=REPORT, help="report path (default: reports/paper-reference-coverage.json)")
    args = parser.parse_args()

    report, passed = build_report()
    output = args.report if args.report.is_absolute() else ROOT / args.report
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {relpath(output)}")
    print(f"HM references: {report['papers']['hidden_monotonicity']['source_reference_count']}; "
          f"PTNB v2 references: {report['papers']['playing_the_network_backward_v2']['source_reference_count']} "
          f"({report['papers']['playing_the_network_backward_v2'].get('source_bbl_item_count', 0)} source BBL items)")
    print(f"Genuinely missing references: {report['missing_count']}")
    if report["hm_ziegler1995_check"]["source_key_present"]:
        z = report["hm_ziegler1995_check"]
        print(f"HM Ziegler1995: cited via {', '.join(z['source_commands'])}; thesis cited={z['thesis_cited']}, bibliography={z['thesis_bibliography_entry']}")
    if not passed:
        for item in report["genuinely_missing_references"]:
            print(f"MISSING {item['paper']} {item['source_key']} -> {item['canonical_thesis_key']}: {', '.join(item['failures'])}", file=sys.stderr)
        for item in report["unverified_aliases"]:
            print(f"UNVERIFIED ALIAS {item['paper']} {item['source_key']} -> {item['canonical_thesis_key']}: bibliography titles differ", file=sys.stderr)
        return 1 if args.check else 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
