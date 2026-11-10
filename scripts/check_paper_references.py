#!/usr/bin/env python3
"""Audit active references in the two source papers against the thesis.

The checker follows recursive TeX input/include files (including the generated
longtable helpers), strips TeX comments before collecting commands, applies only
the explicit aliases recorded in reports/*-citation-aliases.json, and checks
both active thesis citations and bibliography records. It is offline and writes
a deterministic JSON report. Explicit editorial omissions waive only active
citation requirements. Reviewed corrections pin exact old source titles and new
bibliography identity fields; withdrawals must be absent from active citations.

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
EDITORIAL_OMISSIONS_FILE = ROOT / "reports" / "paper-reference-editorial-omissions.json"
CORRECTIONS_FILE = ROOT / "reports" / "paper-reference-reviewed-corrections.json"
IDENTITY_FIELDS = ("title", "doi", "url", "eprint")

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
THESIS_BIB = ROOT / "tex/bibliography/references.bib"

CITATION_COMMANDS = {
    "cite", "citep", "citet", "citealp", "citealt", "citeauthor",
    "citeyear", "citeyearpar", "textcite", "parencite", "autocite",
    "nocite", "citeapp", "citepapp", "citetapp",
}
INCLUDE_COMMANDS = {"input", "include", "appinputgen", "appinputgenlt", "appinputgenci", "appfitgen"}


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
    # TeX accents and Unicode accents must have the same word boundaries.
    value = re.sub(r'''\\["'`^~=.]\s*(?:\{([^{}]*)\}|([A-Za-z]))''',
                   lambda m: m.group(1) or m.group(2), value)
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


def manual_reference_title(reference: str) -> str | None:
    """Extract the title sentence from the archived HM appbibitem format.

    These entries have author, title, then optional venue sentences. A single
    capital before a period is an author initial, not the end of the authors.
    The title-only comparison prevents an arbitrary substring from matching.
    """
    sentences = re.split(r"(?<!\b[A-Z])\.\s+", reference, maxsplit=2)
    return sentences[1] if len(sentences) > 1 else None


def load_aliases(path: Path) -> dict[str, str]:
    return json.loads(path.read_text(encoding="utf-8"))


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def reviewed_corrections(thesis_bib: dict[str, dict[str, str]], thesis_cites: set[str]) -> tuple[dict[str, Any], dict[tuple[str, str], str], list[dict[str, str]]]:
    """Validate exact reviewed identities, without granting general exemptions."""
    ledger = load_json(CORRECTIONS_FILE)
    if ledger.get("schema_version") != 1 or not ledger.get("source_checkpoint"):
        raise ValueError("Reviewed corrections require schema version 1 and a source checkpoint")
    records = ledger["records"]
    source_index: dict[tuple[str, str], str] = {}
    errors: list[dict[str, str]] = []
    for key, record in records.items():
        action = record.get("action")
        if (action not in {"bibliography_correction", "bibliography_withdrawal", "citation_withdrawal"}
                or not record.get("reason") or not record.get("old_identity", {}).get("title")
                or not record.get("audit_record") or not record.get("evidence_sources")):
            raise ValueError("Incomplete reviewed correction: " + key)
        expected = record.get("new_identity")
        if action == "bibliography_withdrawal":
            if expected is not None or record.get("source_references"):
                raise ValueError("Bibliography withdrawals cannot waive inherited references: " + key)
            if key in thesis_bib:
                errors.append({"key": key, "error": "Withdrawn bibliography entry is present"})
        else:
            if not isinstance(expected, dict) or set(expected) != set(IDENTITY_FIELDS) or not expected["title"]:
                raise ValueError("Reviewed identity requires exact title, DOI, URL and eprint values: " + key)
            actual = thesis_bib.get(key)
            if actual is None:
                errors.append({"key": key, "error": "Reviewed bibliography entry is missing"})
            else:
                changed = [field for field in IDENTITY_FIELDS if actual.get(field) != expected[field]]
                if changed:
                    errors.append({"key": key, "error": "Reviewed identity changed: " + ", ".join(changed)})
        if action.endswith("withdrawal") and key in thesis_cites:
            errors.append({"key": key, "error": "Withdrawn reference is actively cited"})
        replacement = record.get("replacement_citation")
        if replacement and (replacement not in thesis_bib or replacement not in thesis_cites):
            errors.append({"key": key, "error": "Reviewed replacement citation is missing: " + replacement})
        for source in record.get("source_references", []):
            pair = (source["paper"], source["source_key"])
            if (action not in {"bibliography_correction", "citation_withdrawal"} or pair[0] not in PAPERS
                    or pair in source_index or not source.get("old_title")):
                raise ValueError("Invalid or duplicate reviewed source correction: " + str(pair))
            source_index[pair] = key
    return records, source_index, errors


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
    thesis_refs = tex_include_manifest(thesis_files)
    thesis_bib = bib_entries(THESIS_BIB)
    thesis_keys = set(thesis_bib)
    # The thesis may have a stale BBL after a citation is restored; raw .bib is
    # authoritative for availability, while the cached BBL is reported only.
    thesis_canonical_cites = set(thesis_refs)
    editorial_record = load_json(EDITORIAL_OMISSIONS_FILE)
    editorial_omissions = {}
    if not editorial_record.get("reason") or not editorial_record.get("editorial_source_commit"):
        raise ValueError("Editorial citation omissions require a reason and source commit")
    for omission in editorial_record["omissions"]:
        key = (omission["paper"], omission["canonical_thesis_key"])
        if key in editorial_omissions or key[0] not in PAPERS or not omission.get("reason"):
            raise ValueError("Invalid or duplicate editorial citation omission: " + str(key))
        editorial_omissions[key] = omission
    seen_editorial_omissions = set()
    corrections, correction_sources, correction_errors = reviewed_corrections(thesis_bib, thesis_canonical_cites)
    seen_correction_sources: set[tuple[str, str]] = set()
    invalid_corrections = {error["key"] for error in correction_errors}
    missing_active_bib = [
        {"key": key, "locations": sorted({item["file"] for item in thesis_refs[key]})}
        for key in sorted(thesis_canonical_cites - thesis_keys)
    ]

    paper_reports: dict[str, Any] = {}
    all_missing: list[dict[str, str]] = []
    intentional_omissions: list[dict[str, Any]] = []
    title_review: list[dict[str, Any]] = []
    applied_corrections: list[dict[str, str]] = []
    unverified_aliases: list[dict[str, Any]] = []
    hash_paths: set[Path] = {THESIS_BIB, THESIS_ROOT, EDITORIAL_OMISSIONS_FILE, CORRECTIONS_FILE}
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
            omission = editorial_omissions.get((name, canonical)) if not thesis_cited else None
            if omission:
                seen_editorial_omissions.add((name, canonical))
                intentional_omissions.append({**omission, "source_key": source_key})
            # Compare the complete title sentence in manual appendix entries.
            if source_key.startswith("App") and source_title and thesis_title:
                title_ok = title_matches(manual_reference_title(source_title), thesis_title)
            correction_key = correction_sources.get((name, source_key))
            correction_ok = False
            if correction_key:
                seen_correction_sources.add((name, source_key))
                expected_source = next(source for source in corrections[correction_key]["source_references"]
                                       if (source["paper"], source["source_key"]) == (name, source_key))
                if canonical != correction_key or source_title != expected_source["old_title"]:
                    correction_errors.append({"key": correction_key, "error": "Archived source identity or alias changed: " + name + "/" + source_key})
                elif correction_key not in invalid_corrections:
                    correction_ok = True
                    reviewed = corrections[correction_key]
                    applied_corrections.append({"paper": name, "source_key": source_key, "canonical_thesis_key": canonical,
                                                "action": reviewed["action"]})
                    if reviewed["action"] == "citation_withdrawal" and not thesis_cited:
                        omission = {"paper": name, "canonical_thesis_key": canonical,
                                    "reason": reviewed["reason"], "reviewed_correction_key": correction_key}
                        intentional_omissions.append({**omission, "source_key": source_key})
            row = {
                "source_key": source_key,
                "canonical_thesis_key": canonical,
                "alias": aliases.get(source_key),
                "source_commands": sorted({x["command"] for x in item["source_occurrences"]}),
                "source_locations": sorted({x["file"] for x in item["source_occurrences"]}),
                "source_bibliography_item": item["source_bibliography_item"],
                "thesis_cited": thesis_cited,
                "citation_status": ("retained" if thesis_cited else
                                    "intentionally_omitted" if omission else "missing"),
                "editorial_omission_reason": omission["reason"] if omission else None,
                "thesis_bibliography_entry": thesis_has_bib,
                "source_title": source_title,
                "thesis_bibliography_title": thesis_title,
                "title_match": title_ok,
                "title_status": ("matched" if title_ok else
                                 "reviewed_correction" if correction_ok else "unverified"),
                "reviewed_correction_key": correction_key,
                "title_verification_source": item["source_title_location"],
            }
            rows.append(row)
            failures = []
            if not thesis_cited and not omission:
                failures.append("not_cited_in_thesis")
            if not thesis_has_bib:
                failures.append("missing_thesis_bibliography_entry")
            if not item["source_bibliography_item"]:
                failures.append("not_in_source_bibliography")
            if failures:
                missing = {"paper": name, "source_key": source_key, "canonical_thesis_key": canonical, "failures": failures}
                all_missing.append(missing)
            if title_ok is not True and not correction_ok:
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
            "retained_source_reference_count": sum(row["thesis_cited"] for row in rows),
            "retained_unique_reference_count": len({row["canonical_thesis_key"] for row in rows if row["thesis_cited"]}),
            "intentionally_omitted_source_reference_count": sum(row["citation_status"] == "intentionally_omitted" for row in rows),
            "intentionally_omitted_unique_reference_count": len({row["canonical_thesis_key"] for row in rows if row["citation_status"] == "intentionally_omitted"}),
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

    # Retain the dedicated source-provenance check for the historic HM polytope
    # reference, distinguishing editorial omission from accidental loss.
    hm_ziegler = next(
        (row for row in paper_reports["hidden_monotonicity"]["reference_checks"] if row["canonical_thesis_key"] == "Ziegler1995"),
        None,
    )

    if all_missing or missing_active_bib or title_review:
        all_checks_pass = False
    correction_errors.extend(
        {"key": correction_sources[(paper, source_key)],
         "error": "Reviewed source reference is no longer present: " + paper + "/" + source_key}
        for paper, source_key in sorted(set(correction_sources) - seen_correction_sources)
    )
    if correction_errors:
        all_checks_pass = False
    omission_errors = [
        {"paper": paper, "canonical_thesis_key": canonical,
         "error": "Omission does not match an uncited source reference"}
        for paper, canonical in sorted(set(editorial_omissions) - seen_editorial_omissions)
    ]
    if omission_errors:
        all_checks_pass = False
    bbl_path = ROOT / "tex/main.bbl"
    report = {
        "schema_version": 4,
        "title": "Active paper reference coverage against the single thesis document",
        "offline": True,
        "source_projects": ["Hidden Monotonicity", "Playing the Network Backward v2"],
        "thesis_tex_root": relpath(THESIS_ROOT),
        "active_tex_roots": [relpath(THESIS_ROOT)],
        "reference_scope": "Recursive inputs of tex/main.tex only; orphan TeX files do not contribute",
        "main_cited_key_count": len(tex_include_manifest(main_files)),
        "thesis_active_tex_files": [relpath(path) for path in thesis_files],
        "thesis_unresolved_includes": thesis_unresolved,
        "thesis_cited_key_count": len(thesis_canonical_cites),
        "thesis_bibliography_entry_count": len(thesis_keys),
        "active_citations_missing_bibliography": missing_active_bib,
        "cached_thesis_bbl": {
            "path": relpath(bbl_path),
            "present": bbl_path.is_file(),
            "entry_count": len(re.findall(r"^\s*\\entry\{([^}]+)\}", bbl_path.read_text(encoding="utf-8", errors="replace"), re.M)) if bbl_path.is_file() else 0,
            "note": "Informational only; a stale BBL does not override the active .bib source.",
        },
        "papers": paper_reports,
        "bibliography_title_review": title_review,
        "unverified_aliases": unverified_aliases,
        "reviewed_corrections_file": relpath(CORRECTIONS_FILE),
        "reviewed_source_corrections": applied_corrections,
        "reviewed_bibliography_withdrawals": sorted(key for key, item in corrections.items() if item["action"] == "bibliography_withdrawal"),
        "reviewed_citation_withdrawals": sorted(key for key, item in corrections.items() if item["action"] == "citation_withdrawal"),
        "reviewed_correction_errors": correction_errors,
        "source_hashes_sha256": {relpath(path): sha256(path) for path in sorted(hash_paths) if path.is_file()},
        "genuinely_missing_references": all_missing,
        "missing_count": len(all_missing),
        "editorial_omissions_file": relpath(EDITORIAL_OMISSIONS_FILE),
        "intentionally_omitted_references": intentional_omissions,
        "intentional_omission_source_reference_count": len(intentional_omissions),
        "intentional_omission_unique_reference_count": len({row["canonical_thesis_key"] for row in intentional_omissions}),
        "editorial_omission_errors": omission_errors,
        "hm_ziegler1995_check": {
            "canonical_key": "Ziegler1995",
            "source_key_present": hm_ziegler is not None,
            "source_commands": hm_ziegler["source_commands"] if hm_ziegler else [],
            "thesis_cited": hm_ziegler["thesis_cited"] if hm_ziegler else False,
            "citation_status": hm_ziegler["citation_status"] if hm_ziegler else "absent_from_source",
            "thesis_bibliography_entry": hm_ziegler["thesis_bibliography_entry"] if hm_ziegler else False,
        },
        "check_passed": all_checks_pass,
    }
    return report, all_checks_pass


def self_test() -> None:
    """Exercise rejection paths in memory; never mutate the thesis or report."""
    from copy import deepcopy
    from unittest.mock import patch

    baseline, passed = build_report()
    if not passed:
        raise AssertionError("The unmodified repository must pass before running negative checks")
    module = sys.modules[__name__]
    original_bib_entries = bib_entries
    original_load_json = load_json
    bibliography = bib_entries(THESIS_BIB)
    ledger = load_json(CORRECTIONS_FILE)
    checks: list[str] = []

    def reject_bib_change(label: str, changed: dict[str, dict[str, str]], error_field: str) -> None:
        def substituted(path: Path) -> dict[str, dict[str, str]]:
            return changed if path == THESIS_BIB else original_bib_entries(path)
        with patch.object(module, "bib_entries", side_effect=substituted):
            report, passed = build_report()
        if passed or not report[error_field]:
            raise AssertionError("Mutation escaped detection: " + label)
        checks.append(label)

    changed = deepcopy(bibliography)
    changed["Amos2017"]["title"] = "An unexpected replacement title"
    reject_bib_change("unexpected same-key source title", changed, "bibliography_title_review")
    changed = deepcopy(bibliography)
    changed["hertrich2025neuralnetworksvirtualextended"]["title"] = "Neural"
    reject_bib_change("truncated manual appendix title", changed, "bibliography_title_review")

    inherited = {row["canonical_thesis_key"] for paper in baseline["papers"].values()
                 for row in paper["reference_checks"]}
    active_files = [ROOT / name for name in baseline["thesis_active_tex_files"]]
    independent_key = sorted(set(tex_include_manifest(active_files)) - inherited)[0]
    changed = deepcopy(bibliography)
    del changed[independent_key]
    reject_bib_change("missing active bibliography outside inherited sources", changed, "active_citations_missing_bibliography")

    changed = deepcopy(bibliography)
    changed["gao2022luss"]["title"] = "A different dataset paper"
    reject_bib_change("reviewed title changed again", changed, "reviewed_correction_errors")
    changed = deepcopy(bibliography)
    changed["gao2022luss"]["doi"] = "10.0000/unreviewed"
    reject_bib_change("reviewed source identifier changed", changed, "reviewed_correction_errors")
    changed = deepcopy(bibliography)
    del changed["gao2022luss"]
    reject_bib_change("reviewed correction has no bibliography entry", changed, "active_citations_missing_bibliography")

    changed = deepcopy(bibliography)
    changed["Misiakos2022"] = {field: value for field, value in ledger["records"]["Misiakos2022"]["old_identity"].items() if value}
    reject_bib_change("withdrawn bibliography record restored", changed, "reviewed_correction_errors")

    omissions = deepcopy(load_json(EDITORIAL_OMISSIONS_FILE))
    omissions["omissions"][0]["canonical_thesis_key"] = "Amos2017"
    with patch.object(module, "load_json", side_effect=lambda path: omissions if path == EDITORIAL_OMISSIONS_FILE else original_load_json(path)):
        report, passed = build_report()
    if passed or not report["editorial_omission_errors"]:
        raise AssertionError("A stale editorial omission escaped detection")
    checks.append("stale editorial omission")

    changed_ledger = deepcopy(ledger)
    changed_ledger["records"]["gao2022luss"]["source_references"][0]["old_title"] = "An unreviewed archived title"
    with patch.object(module, "load_json", side_effect=lambda path: changed_ledger if path == CORRECTIONS_FILE else original_load_json(path)):
        report, passed = build_report()
    if passed or not report["reviewed_correction_errors"]:
        raise AssertionError("An unmatched archived source title escaped detection")
    checks.append("review no longer matches archived source title")

    original_manifest = tex_include_manifest
    def recited(paths: list[Path]) -> dict[str, list[dict[str, Any]]]:
        manifest = original_manifest(paths)
        if THESIS_ROOT in paths:
            manifest["Dayan2001_TheoreticalNeuroscience"] = [{"file": relpath(THESIS_ROOT), "command": "cite"}]
        return manifest
    with patch.object(module, "tex_include_manifest", side_effect=recited):
        report, passed = build_report()
    if passed or not report["reviewed_correction_errors"]:
        raise AssertionError("A stale reviewed citation withdrawal escaped detection")
    checks.append("reviewed citation withdrawal is cited again")
    print(f"Passed baseline and {len(checks)} negative checks: " + "; ".join(checks))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="write the deterministic report and exit nonzero on missing references or unresolved active inputs")
    parser.add_argument("--report", type=Path, default=REPORT, help="report path (default: reports/paper-reference-coverage.json)")
    parser.add_argument("--self-test", action="store_true", help="run in-memory negative checks without writing files")
    args = parser.parse_args()

    if args.self_test:
        self_test()
        return 0

    report, passed = build_report()
    output = args.report if args.report.is_absolute() else ROOT / args.report
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {relpath(output)}")
    print(f"HM references: {report['papers']['hidden_monotonicity']['source_reference_count']}; "
          f"PTNB v2 references: {report['papers']['playing_the_network_backward_v2']['source_reference_count']} "
          f"({report['papers']['playing_the_network_backward_v2'].get('source_bbl_item_count', 0)} source BBL items)")
    print(f"Genuinely missing references: {report['missing_count']}")
    for name, paper in report["papers"].items():
        print(f"{name}: retained {paper['retained_source_reference_count']}/{paper['source_reference_count']} source labels "
              f"({paper['retained_unique_reference_count']} unique references); intentionally omitted "
              f"{paper['intentionally_omitted_source_reference_count']} source labels "
              f"({paper['intentionally_omitted_unique_reference_count']} unique references)")
    if report["hm_ziegler1995_check"]["source_key_present"]:
        z = report["hm_ziegler1995_check"]
        print(f"HM Ziegler1995: cited via {', '.join(z['source_commands'])}; thesis cited={z['thesis_cited']}, bibliography={z['thesis_bibliography_entry']}")
    if not passed:
        for item in report["active_citations_missing_bibliography"]:
            print(f"MISSING ACTIVE BIBLIOGRAPHY {item['key']}", file=sys.stderr)
        for item in report["genuinely_missing_references"]:
            print(f"MISSING {item['paper']} {item['source_key']} -> {item['canonical_thesis_key']}: {', '.join(item['failures'])}", file=sys.stderr)
        for item in report["unverified_aliases"]:
            print(f"UNVERIFIED ALIAS {item['paper']} {item['source_key']} -> {item['canonical_thesis_key']}: bibliography titles differ", file=sys.stderr)
        for item in report["bibliography_title_review"]:
            print(f"UNREVIEWED TITLE {item['paper']} {item['source_key']} -> {item['canonical_thesis_key']}", file=sys.stderr)
        for item in report["reviewed_correction_errors"]:
            print(f"INVALID CORRECTION {item['key']}: {item['error']}", file=sys.stderr)
        for item in report["editorial_omission_errors"]:
            print(f"INVALID OMISSION {item['paper']} {item['canonical_thesis_key']}: {item['error']}", file=sys.stderr)
        return 1 if args.check else 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
