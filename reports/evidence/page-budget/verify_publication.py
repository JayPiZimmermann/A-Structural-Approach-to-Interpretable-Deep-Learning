#!/usr/bin/env python3
"""Check the two published PDFs, their cross-links, and the unchanged proof closure."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent


def command(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inspect_pdf(name, tex_name):
    path = ROOT / "docs" / name
    objects = command("mutool", "show", str(path), "grep")
    names = set()
    for line in objects.splitlines():
        if "/Names[" in line:
            names.update(re.findall(r"\(([^()]*)\)\d+ 0 R", line))
    remote = []
    for line in objects.splitlines():
        if "/S/GoToR" in line:
            remote.append({"file": re.search(r"/F\(([^()]*)\)", line)[1],
                           "destination": re.search(r"/D\(([^()]*)\)", line)[1]})
    uris = re.findall(r"/URI\(([^()]*)\)", objects)
    lean = [uri for uri in uris if "/formalization/" in uri and ".lean#L" in uri]
    log = (ROOT / "tex" / (tex_name + ".log")).read_text()
    return {
        "path": str(path.relative_to(ROOT)), "sha256": sha(path),
        "matches_compiled_pdf": sha(path) == sha(ROOT / "tex" / (tex_name + ".pdf")),
        "pages": int(re.search(r"^Pages:\s+(\d+)", command("pdfinfo", str(path)), re.M)[1]),
        "overfull_boxes": len(re.findall(r"Overfull \\[hv]box", log)),
        "unresolved_reference_or_citation": bool(re.search(
            r"(?:Reference|Citation).*undefined|There were undefined|multiply defined", log)),
        "lean_uri_count": len(lean), "unique_lean_uris": len(set(lean)),
        "remote_link_count": len(remote),
    }, names, remote, lean


def main():
    documents = {}
    destinations = {}
    remote_links = {}
    all_lean = []
    for name, tex_name in [("thesis.pdf", "main"), ("thesis-supplement.pdf", "supplement")]:
        info, names, remote, lean = inspect_pdf(name, tex_name)
        documents[name] = info
        destinations[name] = names
        remote_links[name] = remote
        all_lean.extend(lean)
    broken = [{"source": name, **link} for name, links in remote_links.items()
              for link in links
              if link["file"] not in destinations
              or link["destination"] not in destinations[link["file"]]]
    generated = (ROOT / "tex/preamble/lean_links_generated.tex").read_text()
    expected = {uri.replace(r"\#", "#") for uri in
                re.findall(r"\\DeclareLeanResult\{[^}]+\}\{([^}]+)\}", generated)}
    receipt = json.loads((ROOT / "reports/verification/current/receipt.json").read_text())
    changed = [name for name, digest in receipt["source"]["sha256"].items()
               if sha(ROOT / name) != digest]
    checks = {
        "main_pdf_within_150_pages": documents["thesis.pdf"]["pages"] <= 150,
        "both_logs_clean": all(not doc["overfull_boxes"] and
                               not doc["unresolved_reference_or_citation"]
                               for doc in documents.values()),
        "both_published_pdfs_match_builds": all(doc["matches_compiled_pdf"]
                                               for doc in documents.values()),
        "both_documents_have_remote_links": all(doc["remote_link_count"] > 0
                                                for doc in documents.values()),
        "broken_remote_links": broken,
        "combined_lean_uri_count": len(all_lean),
        "combined_unique_lean_uris": len(set(all_lean)),
        "all_expected_lean_uris_present": set(all_lean) == expected,
        "all_lean_uris_at_verified_revision": all(
            "/blob/" + receipt["source"]["commit"] + "/" in uri for uri in all_lean),
        "verified_proof_files_checked": len(receipt["source"]["sha256"]),
        "changed_verified_proof_files": changed,
    }
    passed = (checks["main_pdf_within_150_pages"] and checks["both_logs_clean"]
              and checks["both_published_pdfs_match_builds"]
              and checks["both_documents_have_remote_links"]
              and not broken and len(all_lean) == 216
              and checks["all_expected_lean_uris_present"]
              and checks["all_lean_uris_at_verified_revision"] and not changed)
    result = {"status": "passed" if passed else "failed", "documents": documents,
              "proof_source_commit": receipt["source"]["commit"], "checks": checks}
    (OUT / "publication-checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
