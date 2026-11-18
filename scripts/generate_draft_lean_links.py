#!/usr/bin/env python3
"""Link locally checked, unpublished Lean additions without changing pinned links.

The source snapshot is kept beside the PDF, under a content-addressed path.
The separate build receipt must bind the source, audit logs and reviewed scope.
"""
import argparse
import hashlib
import html
import json
from pathlib import Path

from generate_lean_links import declarations

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_file(root, name):
    path = (root / name).resolve()
    if not path.is_relative_to(root.resolve()) or not path.is_file():
        raise ValueError(f"Missing or external draft proof artifact: {name}")
    return path


def draft_outputs(root=ROOT):
    manifest = json.loads((root / "formalization/draft_tex_links.json").read_text())
    pinned = json.loads((root / "formalization/tex_links.json").read_text())
    if set(manifest) & set(pinned):
        raise ValueError("Draft proof links cannot replace pinned labels")
    output, links = {}, {}
    tex = ["% Generated locally checked additions; published proof links remain pinned."]
    for label, spec in manifest.items():
        source = checked_file(root, spec["path"])
        receipt_path = checked_file(root, spec["receipt"])
        receipt = json.loads(receipt_path.read_text())
        if receipt.get("status") != "passed" or receipt.get("mode") != "local-development":
            raise ValueError("A successful local-development proof receipt is required")
        if not receipt.get("commands") or any(c["exit_code"] != 0 for c in receipt["commands"]):
            raise ValueError("Draft Lean build or audit did not pass")
        bound = receipt.get("source_sha256", {})
        artifacts = receipt.get("artifact_sha256", {})
        if spec["path"] not in bound:
            raise ValueError("Draft proof source is not bound by its receipt")
        for command in receipt["commands"]:
            if command.get("log") not in artifacts:
                raise ValueError("Draft build and audit logs must be bound by the receipt")
        for hashes in (bound, artifacts):
            for name, expected in hashes.items():
                if digest(checked_file(root, name)) != expected:
                    raise ValueError(f"Stale draft proof evidence: {name}")
        target = spec["declaration"]
        contract = receipt.get("targets", {}).get(target, {})
        if not contract.get("type_checked") or not contract.get("scope_reviewed"):
            raise ValueError("The linked theorem needs a type and scope review")
        if "axioms" not in contract or not set(contract["axioms"]) <= ALLOWED_AXIOMS:
            raise ValueError("Unapproved or missing theorem axiom audit")
        review_path = receipt.get("scope_review")
        if review_path not in receipt.get("artifact_sha256", {}):
            raise ValueError("Scope review is not bound by the draft receipt")
        review = json.loads(checked_file(root, review_path).read_text())
        if review.get("verdict") != "PASS" or review.get("declaration") != target:
            raise ValueError("Draft theorem scope review did not pass")
        reviewed = review.get("source_sha256", {})
        if spec["path"] not in reviewed:
            raise ValueError("Scope review must bind the linked proof source")
        for name, expected in reviewed.items():
            if digest(checked_file(root, name)) != expected:
                raise ValueError(f"Stale draft scope review: {name}")
        text = source.read_text()
        found = declarations(text, spec["path"])
        if target not in found or found[target]["kind"] not in {"theorem", "lemma"}:
            raise ValueError(f"Missing theorem declaration: {target}")
        line = found[target]["line"]
        source_hash = digest(source)
        relative = f"draft-proofs/{source_hash}/{source.name}.html"
        url = f"{relative}#L{line}"
        rows = "\n".join(
            f'<span class="line" id="L{n}"><a href="#L{n}" class="number">{n}</a>'
            f'<code>{html.escape(value)}</code></span>'
            for n, value in enumerate(text.splitlines(), 1)
        )
        title = html.escape(target)
        page = f'''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width">
<title>{title} — locally checked Lean proof</title>
<style>
body{{margin:2rem;color:#202124;background:#fff;font:16px/1.5 system-ui,sans-serif}}
h1{{font-size:1.2rem;overflow-wrap:anywhere}} .metadata{{max-width:85ch}}
pre{{overflow:auto;padding:1rem 0;border-top:1px solid #ccc;font:14px/1.5 monospace}}
.line{{display:block;min-height:1.5em}} .line:target{{background:#fff2bd}}
.number{{display:inline-block;width:4em;padding-right:1em;text-align:right;color:#666}}
code{{font:inherit}} .hash{{overflow-wrap:anywhere}}
</style><main>
<h1>{title}</h1>
<div class="metadata"><p>Locally checked, unpublished Lean source. This is an addition to the
pinned thesis formalization; it has not been committed or published as a GitHub revision.</p>
<p>{html.escape(spec['scope'])}</p>
<p>Source: <code>{html.escape(spec['path'])}</code><br>
SHA-256: <code class="hash">{source_hash}</code><br>
Permitted axioms used: <code>{html.escape(', '.join(contract['axioms']) or 'none')}</code>.</p>
<p>The separate local build, theorem type, axiom audit and scope review passed.
Keep this <code>draft-proofs</code> directory beside the thesis PDF.</p></div>
<pre>{rows}</pre></main></html>
'''
        html_path = root / "docs" / relative
        if html_path in output:
            raise ValueError("Multiple draft targets cannot overwrite the same source snapshot")
        output[html_path] = page
        tex.append(r"\DeclareLeanEquationURL{" + label + "}{" + url.replace("#", r"\#") + "}")
        links[label] = {
            **spec, "line": line, "url": url, "source_sha256": source_hash,
            "html_path": "docs/" + relative,
            "html_sha256": hashlib.sha256(page.encode()).hexdigest(),
            "receipt_sha256": digest(receipt_path),
        }
    output[root / "tex/preamble/lean_links_draft.tex"] = "\n".join(tex) + "\n"
    return output, links


def validate_draft_links(root=ROOT):
    output, links = draft_outputs(root)
    for path, text in output.items():
        if not path.is_file() or path.read_text() != text:
            raise ValueError(f"Missing or stale draft proof link artifact: {path}")
    return links


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.check:
        links = validate_draft_links()
    else:
        output, links = draft_outputs()
        for path, text in output.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
    print(f"{len(links)} locally verified equation links; pinned links unchanged")


if __name__ == "__main__":
    main()
