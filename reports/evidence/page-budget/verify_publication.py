#!/usr/bin/env python3
"""Check the single thesis PDF, internal destinations and pinned proof closure.

Two-document receipts remain historical. This guard writes its current evidence
under reports/single-pdf and retains the 150-page publication limit.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "reports/single-pdf"
sys.path.insert(0, str(ROOT / "scripts"))
from tex_lean_inventory import published_link_details


def command(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pdf_links(objects, page_objects):
    """Parse MuPDF's one-object-per-line PDF syntax; preserve PDF name escaping."""
    string = r"\(((?:\\.|[^\\()])*)\)"
    names = set()
    for line in objects.splitlines():
        if "/Names[" in line:
            names.update(re.findall(string + r"\s*\d+\s+\d+\s+R", line))
    remote, internal, uris = [], [], []
    for line in objects.splitlines():
        if "/S/GoToR" in line:
            remote.append(line[:800])
        elif re.search(r"/S/GoTo(?:[/\s>])", line):
            named = re.search(r"/D" + string, line)
            explicit = re.search(r"/D\[\s*(\d+)\s+\d+\s+R", line)
            if named:
                internal.append({"kind": "named", "target": named[1], "resolved": named[1] in names})
            elif explicit:
                internal.append({"kind": "page", "target": int(explicit[1]), "resolved": int(explicit[1]) in page_objects})
            else:
                internal.append({"kind": "unparsed", "target": line[:800], "resolved": False})
        # Direct annotation/bookmark destinations use /Dest without an action.
        direct = re.search(r"/Dest" + string, line)
        if direct:
            internal.append({"kind": "named", "target": direct[1], "resolved": direct[1] in names})
        explicit_dest = re.search(r"/Dest\[\s*(\d+)\s+\d+\s+R", line)
        if explicit_dest:
            internal.append({"kind": "page", "target": int(explicit_dest[1]), "resolved": int(explicit_dest[1]) in page_objects})
        uris.extend(re.findall(r"/URI" + string, line))
    return names, remote, internal, uris


def inspect_pdf():
    path = ROOT / "docs/thesis.pdf"
    objects = command("mutool", "show", str(path), "grep")
    pages_listing = command("mutool", "show", str(path), "pages")
    page_objects = {int(value) for value in re.findall(r"page\s+\d+\s*=\s*(\d+)\s+\d+\s+R", pages_listing)}
    names, remote, internal, uris = pdf_links(objects, page_objects)
    lean = [uri for uri in uris if "/formalization/" in uri and ".lean#L" in uri]
    log = (ROOT / "tex/main.log").read_text()
    warnings = [line for line in log.splitlines() if re.search(r"\bWarning\b|Overfull \\[hv]box|Underfull \\[hv]box", line)]
    biber_log = ROOT / "tex/main.blg"
    biber_warnings = [line for line in biber_log.read_text().splitlines()
                      if re.search(r"\b(?:WARN|ERROR)\b", line)] if biber_log.exists() else []
    info = {
        "path": "docs/thesis.pdf", "sha256": sha(path),
        "matches_compiled_pdf": sha(path) == sha(ROOT / "tex/main.pdf"),
        "pages": int(re.search(r"^Pages:\s+(\d+)", command("pdfinfo", str(path)), re.M)[1]),
        "overfull_boxes": len(re.findall(r"Overfull \\[hv]box", log)),
        "underfull_boxes": len(re.findall(r"Underfull \\[hv]box", log)),
        "warnings": warnings, "biber_warnings_or_errors": biber_warnings,
        "unresolved_reference_or_citation": bool(re.search(
            r"(?:Reference|Citation).*undefined|There were undefined|multiply defined", log)),
        "lean_uri_count": len(lean), "unique_lean_uris": len(set(lean)),
        "remote_link_count": len(remote), "internal_link_count": len(internal),
        "named_destinations": len(names), "page_object_count": len(page_objects),
    }
    return info, remote, internal, lean


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=OUT/'publication-checks.json')
    args = parser.parse_args()
    info, remote, internal, all_lean = inspect_pdf()
    generated = (ROOT / "tex/preamble/lean_links_generated.tex").read_text()
    config = json.loads((ROOT / "formalization/tex_links.json").read_text())
    details = published_link_details(config)
    uses, retired = details['uses'], details['retired']
    urls = {label: uri.replace(r"\#", "#") for label, uri in
            re.findall(r"\\DeclareLeanResult\{([^}]+)\}\{([^}]+)\}", generated)}
    if set(urls) != set(config):
        raise ValueError("Generated Lean declarations do not match the pinned link map")
    expected = Counter()
    for label, count in uses.items(): expected[urls[label]] += count
    receipt = json.loads((ROOT / "reports/verification/current/receipt.json").read_text())
    changed = [name for name, digest in receipt["source"]["sha256"].items()
               if not (ROOT / name).is_file() or sha(ROOT / name) != digest]
    broken = [link for link in internal if not link['resolved']]
    checks = {
        "main_pdf_within_150_pages": info['pages'] <= 150,
        "publication_log_clean": not info['warnings'] and not info['biber_warnings_or_errors'] and not info['unresolved_reference_or_citation'],
        "published_pdf_matches_build": info['matches_compiled_pdf'],
        "no_remote_document_links": not remote,
        "internal_links_present": bool(internal), "broken_internal_links": broken,
        "all_internal_destinations_resolve": not broken,
        "published_lean_uri_count": len(all_lean), "unique_lean_uris": len(set(all_lean)),
        "expected_published_lean_link_count": sum(expected.values()),
        "physical_lean_labels": len(uses), "aliased_lean_mappings": details['alias_coverage'],
        "retired_lean_labels": sorted(retired),
        "represented_unique_lean_declarations": len(details['represented_declarations']),
        "all_expected_lean_uris_present": set(all_lean) == set(expected),
        "all_expected_lean_link_occurrences_present": Counter(all_lean) == expected,
        "all_lean_uris_at_verified_revision": all(
            "/blob/" + receipt["source"]["commit"] + "/" in uri for uri in all_lean),
        "verified_proof_files_checked": len(receipt["source"]["sha256"]),
        "changed_verified_proof_files": changed,
    }
    required = ['main_pdf_within_150_pages', 'publication_log_clean', 'published_pdf_matches_build',
                'no_remote_document_links', 'internal_links_present', 'all_internal_destinations_resolve',
                'all_expected_lean_uris_present', 'all_expected_lean_link_occurrences_present',
                'all_lean_uris_at_verified_revision']
    passed = all(checks[key] for key in required) and not changed
    result = {"status": "passed" if passed else "failed", "publication_mode": "single_pdf",
              "active_root": "tex/main.tex", "documents": {"thesis.pdf": info},
              "proof_source_commit": receipt["source"]["commit"], "checks": checks,
              "active_source_files": [str(p.relative_to(ROOT)) for p in details['sources']],
              "remote_document_links": remote,
              "missing_lean_uri_occurrences": dict(expected-Counter(all_lean)),
              "unexpected_lean_uri_occurrences": dict(Counter(all_lean)-expected)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if not passed: raise SystemExit(1)


if __name__ == '__main__': main()
