#!/usr/bin/env python3
"""Compare pre-compression TeX payload with the union of both current documents.

This is a text-retention diagnostic, not a mathematical equivalence checker.
Unmatched substantive paragraphs require the manual dispositions in the report.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
from difflib import SequenceMatcher

ROOT = Path(__file__).resolve().parents[3]
BASE = "91d4d27"
spec = importlib.util.spec_from_file_location("reference_checker", ROOT / "scripts/check_paper_references.py")
ref = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ref)
old_paths = set(subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE], cwd=ROOT, text=True).splitlines())
old_cache = {}


def old_text(path):
    if path not in old_cache:
        old_cache[path] = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=ROOT, text=True)
    return old_cache[path]


def old_closure(root):
    visited = []
    unresolved = []
    pattern = re.compile(r"\\([A-Za-z]+)\*?(?:\s*\[[^]]*\])*\s*\{([^{}]+)\}")

    def visit(path):
        if path in visited:
            return
        visited.append(path)
        for match in pattern.finditer(ref.strip_comments(old_text(path))):
            command, raw = match.groups()
            if command not in ref.INCLUDE_COMMANDS or "#" in raw:
                continue
            candidate = None
            for name in [raw] if Path(raw).suffix else [raw + ".tex", raw]:
                for base in [Path("tex"), Path(path).parent]:
                    name_path = str(base / name)
                    if name_path in old_paths:
                        candidate = name_path
                        break
                if candidate:
                    break
            if candidate:
                visit(candidate)
            else:
                unresolved.append({"source": path, "include": raw})

    visit(root)
    return visited, unresolved


def remove_headings(text):
    pattern = re.compile(r"\\(?:chapter|section|subsection|subsubsection|paragraph|subparagraph)\*?(?:\[[^]]*\])?\s*\{")
    while match := pattern.search(text):
        _, end = ref.balanced_group(text, match.end() - 1)
        text = text[:match.start()] + " " + text[end:]
    return text


def normalize(text):
    text = ref.strip_comments(text)
    text = remove_headings(text)
    text = re.sub(r"(\\caption(?:of\{[^}]+\})?)\[[^]]*\]", r"\1", text)
    text = text.replace("~", " ")
    text = re.sub(r"\\(?:allowbreak|begingroup|endgroup|clearpage|cleardoublepage|FloatBarrier|appendix)\b", "", text)
    text = re.sub(r"\\emergencystretch\s*=\s*[\d.]+em", "", text)
    return re.sub(r"\s+", " ", text).strip()


def substantial(text):
    text = re.sub(r"\\(?:label|input|include)\{[^}]*\}", "", text)
    text = re.sub(r"\\(?:begin|end)\{[^}]*\}(?:\[[^]]*\])?", "", text)
    return len(re.findall(r"[A-Za-z0-9]+", text)) >= 1


def math_payloads(text):
    text = ref.strip_comments(text)
    pattern = re.compile(r"\\begin\{(equation\*?|align\*?|gather\*?|multline\*?|displaymath)\}(.*?)\\end\{\1\}|\\\[(.*?)\\\]", re.S)
    return [normalize(m[2] if m[1] else m[3]) for m in pattern.finditer(text)]


def main():
    old_files, old_unresolved = old_closure("tex/main.tex")
    main_files, unresolved_main = ref.tex_closure(ROOT / "tex/main.tex", ROOT / "tex")
    supp_files, unresolved_supp = ref.tex_closure(ROOT / "tex/supplement.tex", ROOT / "tex")
    new_files = list(dict.fromkeys(main_files + supp_files))
    current = {str(p.relative_to(ROOT)): p.read_text() for p in new_files}
    normalized = {p: normalize(t) for p, t in current.items()}
    body_files = [p for p in old_files if p.startswith(("tex/chapters/", "tex/frontmatter/", "tex/figures/", "tex/tables/"))]
    paragraph_records = []
    unmatched = []
    old_math = []
    new_math = {value for text in current.values() for value in math_payloads(text)}
    for path in body_files:
        text = old_text(path)
        for match in re.finditer(r"\S(?:.*?\S)?(?=\n\s*\n|\Z)", text, re.S):
            payload = normalize(match[0])
            if not substantial(payload):
                continue
            destinations = [p for p, value in normalized.items() if payload in value]
            record = {"source": path, "line": text.count("\n", 0, match.start()) + 1,
                      "words": len(payload.split()), "destinations": destinations}
            paragraph_records.append(record)
            if not destinations:
                unmatched.append({**record, "old_payload": payload})
        for payload in math_payloads(text):
            old_math.append({"source": path, "payload": payload, "preserved": payload in new_math})
    new_paragraphs = [(p, normalize(m[0])) for p, text in current.items()
                      for m in re.finditer(r"\S(?:.*?\S)?(?=\n\s*\n|\Z)", text, re.S)]
    candidates = [(p, value, value.split(), set(value.split())) for p, value in new_paragraphs]
    for row in unmatched:
        old_tokens = row["old_payload"].split()
        old_set = set(old_tokens)
        nearest = sorted(candidates, key=lambda p: len(old_set & p[3]) / max(1, len(old_set | p[3])), reverse=True)[:20]
        best = max(nearest, key=lambda p: SequenceMatcher(None, old_tokens, p[2], autojunk=False).ratio())
        matcher = SequenceMatcher(None, old_tokens, best[2], autojunk=False)
        row["closest_current_file"] = best[0]
        row["closest_current_payload"] = best[1]
        row["similarity"] = matcher.ratio()
        row["old_changed_spans"] = [" ".join(old_tokens[a:b]) for kind, a, b, _, _ in matcher.get_opcodes() if kind in {"delete", "replace"}]
    report = {
        "baseline_commit": BASE,
        "scope": "All active substantive source paragraphs and display-math payloads in old main closure versus current main+supplement union.",
        "normalization": "Remove comments, headings, optional short-caption titles and specified layout commands; collapse whitespace and nonbreaking spaces. Retain prose, math, captions and citation/reference payloads.",
        "old_active_files": len(old_files), "current_active_files": len(new_files),
        "old_active_files_absent_from_current_closure": sorted(set(old_files) - set(current)),
        "unresolved_old_includes": old_unresolved,
        "unresolved_current_includes": unresolved_main + unresolved_supp,
        "old_content_blocks": len(paragraph_records),
        "verbatim_normalized_content_blocks": len(paragraph_records) - len(unmatched),
        "content_block_definition": "A blank-line-delimited source block with nonempty content after heading/layout/comment normalization; pure labels and input directives are excluded. Very short blocks are included.",
        "unmatched_paragraphs": unmatched,
        "old_display_math_payloads": len(old_math),
        "verbatim_display_math_payloads": sum(row["preserved"] for row in old_math),
        "unmatched_display_math": [row for row in old_math if not row["preserved"]],
        "paragraph_crosswalk": paragraph_records,
        "current_source_sha256": {p: hashlib.sha256(t.encode()).hexdigest() for p, t in current.items()},
        "status": "requires_manual_disposition_of_unmatched_paragraphs",
    }
    output = Path(__file__).with_suffix(".json")
    if output.exists():
        previous = json.loads(output.read_text())
        if (previous.get("current_source_sha256") == report["current_source_sha256"]
                and previous.get("baseline_commit") == BASE
                and "manual_review" in previous):
            report["manual_review"] = previous["manual_review"]
            report["status"] = previous["status"]
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in {"paragraph_crosswalk", "current_source_sha256", "unmatched_paragraphs"}}, indent=2))
    print("UNMATCHED PARAGRAPHS")
    for i, row in enumerate(unmatched):
        print(i, row["source"], row["line"], row["words"], round(row["similarity"], 3), row["old_changed_spans"])


if __name__ == "__main__":
    main()
