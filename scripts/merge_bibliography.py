#!/usr/bin/env python3
"""Merge the two papers' bibliographies into tex/bibliography/references.bib.

Sources (in key-priority order, per THESIS_PLAN.md §3):
  1. arxive/hiddenMonotonicity/references.bib          (Paper 1, has .bib)
  2. tex/bibliography/references.bib                   (existing file, kept via union)
  3. arxive/playingTheNetworkBackward/main.bbl         (Paper 2, .bbl only)

Paper 2 entries are recovered by resolving each \\bibitem to canonical BibTeX:
DOI content negotiation -> arXiv bibtex endpoint -> DBLP title search ->
Crossref title search.  Unresolved entries become @misc stubs flagged TODO.

Duplicates are detected by normalized title; the surviving key follows the
priority above and every alias is recorded in the merge report.

Usage:
  python3 scripts/merge_bibliography.py merge      # build merged references.bib + report
  python3 scripts/merge_bibliography.py download   # fetch missing PDFs into literature/references/
"""

import json
import re
import sys
import time
import difflib
import urllib.request
import urllib.parse
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
P1_BIB = ROOT / "arxive/hiddenMonotonicity/references.bib"
P2_BBL = ROOT / "arxive/playingTheNetworkBackward/main.bbl"
OUT_BIB = ROOT / "tex/bibliography/references.bib"
REPORT = ROOT / "tex/bibliography/bib_merge_report.md"
LIT_DIR = ROOT / "literature/references"
MAILTO = "jakob.paul.zimmermann@gmail.com"
UA = {"User-Agent": f"master-thesis-bib-merge (mailto:{MAILTO})"}


def http_get(url, accept=None, timeout=30):
    headers = dict(UA)
    if accept:
        headers["Accept"] = accept
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read().decode("utf-8", errors="replace")


# ---------------------------------------------------------------- .bib parsing

def parse_bib(text):
    """Return list of dicts with keys: type, key, body (raw field text)."""
    entries = []
    for m in re.finditer(r"@(\w+)\s*\{", text):
        etype = m.group(1)
        if etype.lower() in ("comment", "preamble", "string"):
            continue
        start = m.end()
        depth = 1
        i = start
        while i < len(text) and depth:
            depth += {"{": 1, "}": -1}.get(text[i], 0)
            i += 1
        inner = text[start:i - 1]
        key, _, body = inner.partition(",")
        entries.append({"type": etype, "key": key.strip(), "body": body.strip()})
    return entries


def get_field(body, name):
    m = re.search(name + r"\s*=\s*[{\"]", body, re.I)
    if not m:
        return ""
    i = m.end()
    if body[i - 1] == '"':
        j = body.find('"', i)
        return body[i:j] if j > 0 else ""
    depth = 1
    j = i
    while j < len(body) and depth:
        depth += {"{": 1, "}": -1}.get(body[j], 0)
        j += 1
    return body[i:j - 1]


def norm_title(t):
    return re.sub(r"[^a-z0-9]", "", t.lower())


def entry_str(e):
    return "@%s{%s,\n%s\n}\n" % (e["type"], e["key"], e["body"].rstrip().rstrip(","))


# ---------------------------------------------------------------- .bbl parsing

def strip_tex(s):
    s = s.replace("~", " ").replace("\\&", "&").replace("--", "-")
    s = re.sub(r"\\(emph|textit|textbf|texttt|url|doi)\s*", "", s)
    s = re.sub(r"\\[a-zA-Z]+", " ", s)
    s = re.sub(r"[{}]", "", s)
    return re.sub(r"\s+", " ", s).strip()


def parse_bbl(text):
    items = []
    chunks = re.split(r"\\bibitem", text)[1:]
    for chunk in chunks:
        chunk = chunk.split("\\end{thebibliography}")[0]
        m = re.match(r"\[(.*?)\]\{([^}]*)\}", chunk, re.S)
        if not m:
            continue
        label, key = m.group(1), m.group(2)
        rest = chunk[m.end():]
        blocks = [b.strip() for b in rest.split("\\newblock")]
        authors = strip_tex(blocks[0]).rstrip(".") if blocks else ""
        title = strip_tex(blocks[1]).rstrip(".") if len(blocks) > 1 else ""
        tail = " ".join(blocks[2:])
        ym = re.search(r"\((\d{4})\)", label) or re.search(r"\b(19|20)\d{2}\b", tail)
        year = ym.group(1) if ym and len(ym.group(1)) == 4 else (ym.group(0) if ym else "")
        doi_m = re.search(r"\\doi\{([^}]*)\}", rest)
        url_m = re.search(r"\\url\{([^}]*)\}", rest)
        arxiv_m = re.search(r"ar[xX]iv[:./ ]+(?:abs/)?(\d{4}\.\d{4,5})", rest)
        items.append({
            "key": key, "authors": authors, "title": title, "year": year,
            "doi": doi_m.group(1) if doi_m else "",
            "url": url_m.group(1) if url_m else "",
            "arxiv": arxiv_m.group(1) if arxiv_m else "",
            "raw": strip_tex(rest)[:400],
        })
    return items


# ------------------------------------------------------------- bibtex fetchers

def fetch_doi(doi):
    return http_get("https://doi.org/" + urllib.parse.quote(doi),
                    accept="application/x-bibtex")


def fetch_arxiv(arxiv_id):
    return http_get(f"https://arxiv.org/bibtex/{arxiv_id}")


def fetch_dblp(title):
    q = urllib.parse.quote(title)
    data = json.loads(http_get(
        f"https://dblp.org/search/publ/api?q={q}&format=json&h=5"))
    hits = data.get("result", {}).get("hits", {}).get("hit", []) or []
    best, best_r = None, 0.0
    for h in hits:
        info = h.get("info", {})
        r = difflib.SequenceMatcher(
            None, norm_title(title), norm_title(info.get("title", ""))).ratio()
        if r > best_r:
            best, best_r = info, r
    if best and best_r >= 0.85:
        return http_get(best["url"] + ".bib?param=0")
    return None


def fetch_crossref(title):
    q = urllib.parse.quote(title)
    data = json.loads(http_get(
        f"https://api.crossref.org/works?query.title={q}&rows=5&mailto={MAILTO}"))
    for item in data.get("message", {}).get("items", []):
        cand = (item.get("title") or [""])[0]
        r = difflib.SequenceMatcher(
            None, norm_title(title), norm_title(cand)).ratio()
        if r >= 0.9 and item.get("DOI"):
            return fetch_doi(item["DOI"])
    return None


def resolve_bbl_item(it):
    """Return (bibtex_text, source) or (None, None)."""
    attempts = []
    if it["doi"]:
        attempts.append(("doi", lambda: fetch_doi(it["doi"])))
    if it["arxiv"]:
        attempts.append(("arxiv", lambda: fetch_arxiv(it["arxiv"])))
    if it["title"]:
        attempts.append(("dblp", lambda: fetch_dblp(it["title"])))
        attempts.append(("crossref", lambda: fetch_crossref(it["title"])))
    for source, fn in attempts:
        try:
            bib = fn()
            if bib and "@" in bib:
                return bib, source
        except Exception:
            pass
        time.sleep(1.0)
    return None, None


def stub_entry(it):
    fields = [f'  title = {{{it["title"]}}}', f'  author = {{{it["authors"]}}}']
    if it["year"]:
        fields.append(f'  year = {{{it["year"]}}}')
    if it["url"]:
        fields.append(f'  url = {{{it["url"]}}}')
    fields.append(f'  note = {{TODO: unresolved .bbl entry; raw: {it["raw"][:200]}}}')
    return {"type": "misc", "key": it["key"], "body": ",\n".join(fields)}


# ------------------------------------------------------------------- commands

def cmd_merge():
    p1 = parse_bib(P1_BIB.read_text())
    existing = parse_bib(OUT_BIB.read_text()) if OUT_BIB.exists() else []
    bbl_items = parse_bbl(P2_BBL.read_text())
    print(f"Paper 1: {len(p1)} entries | existing: {len(existing)} | Paper 2 .bbl: {len(bbl_items)}")

    p2, unresolved, sources = [], [], {}
    for i, it in enumerate(bbl_items, 1):
        bib, source = resolve_bbl_item(it)
        if bib:
            parsed = parse_bib(bib)
            if parsed:
                e = parsed[0]
                e["key"] = it["key"]  # keep Paper 2's key (Q10: B)
                p2.append(e)
                sources[it["key"]] = source
                print(f"  [{i}/{len(bbl_items)}] {it['key']} <- {source}")
                continue
        unresolved.append(it)
        p2.append(stub_entry(it))
        print(f"  [{i}/{len(bbl_items)}] {it['key']} UNRESOLVED (stub written)")
        time.sleep(0.5)

    # Union with dedup by normalized title; priority: Paper1 > existing > Paper2.
    merged, seen_titles, seen_keys, aliases = [], {}, set(), []
    for origin, entries in (("paper1", p1), ("existing", existing), ("paper2", p2)):
        for e in entries:
            t = norm_title(get_field(e["body"], "title"))
            if t and t in seen_titles:
                if seen_titles[t] != e["key"]:
                    aliases.append((e["key"], seen_titles[t], origin))
                continue
            if e["key"] in seen_keys:  # same key, different work: rename collision
                new_key = e["key"] + "_" + origin
                aliases.append((e["key"], new_key, origin + " KEY COLLISION"))
                e["key"] = new_key
            seen_keys.add(e["key"])
            if t:
                seen_titles[t] = e["key"]
            merged.append(e)

    if OUT_BIB.exists():
        OUT_BIB.rename(OUT_BIB.with_suffix(".bib.bak"))
    merged.sort(key=lambda e: e["key"].lower())
    OUT_BIB.write_text(
        "% Merged bibliography (scripts/merge_bibliography.py). Do not edit the .bak.\n\n"
        + "\n".join(entry_str(e) for e in merged))

    lines = ["# Bibliography merge report\n",
             f"- Paper 1 entries: {len(p1)}",
             f"- Existing entries: {len(existing)}",
             f"- Paper 2 .bbl entries resolved: {len(p2) - len(unresolved)}/{len(bbl_items)}",
             f"- Merged total (after dedup): {len(merged)}\n",
             "## Alias map (cite-key -> surviving key)\n"]
    lines += [f"- `{a}` -> `{b}`  ({c})" for a, b, c in aliases] or ["(none)"]
    lines.append("\n## Unresolved .bbl entries (stub @misc written, fix manually)\n")
    lines += [f"- `{it['key']}`: {it['title']}" for it in unresolved] or ["(none)"]
    lines.append("\n## Resolution sources\n")
    lines += [f"- `{k}`: {v}" for k, v in sorted(sources.items())]
    REPORT.write_text("\n".join(lines) + "\n")
    print(f"\nWrote {OUT_BIB} ({len(merged)} entries) and {REPORT}")


def existing_pdf_titles():
    titles = set()
    md = LIT_DIR / "downloaded_papers.md"
    if md.exists():
        for m in re.finditer(r"\|\s*[^|]+\.pdf\s*\|\s*([^|]+)\|", md.read_text()):
            titles.add(norm_title(m.group(1)))
    for pdf in LIT_DIR.rglob("*.pdf"):
        titles.add(norm_title(pdf.stem))
    return titles


TOPIC_RULES = [
    ("lrp_and_propagation", ["relevance propagation", "lrp", "deep taylor", "deeplift"]),
    ("gradient_and_cam_methods", ["grad-cam", "cam", "integrated gradients", "smoothgrad", "saliency map"]),
    ("transformer_explainability", ["transformer", "attention", "vit", "bert"]),
    ("saliency_metrics", ["metric", "evaluat", "sanity", "quantus", "benchmark"]),
    ("ICNNs_DCopt", ["input convex", "difference of convex", "dc program", "convex neural"]),
    ("monotonicity", ["monotone", "monotonic"]),
    ("polyhedral_theory_NNs", ["tropical", "polytope", "polyhedral", "linear region"]),
    ("ReLUNetGame", ["game", "stopping", "shapley"]),
    ("architectures", ["resnet", "vgg", "imagenet classification", "vision transformer"]),
    ("datasets_and_benchmarks", ["dataset", "pascal voc", "imagenet"]),
]


def guess_topic(title):
    t = title.lower()
    for folder, kws in TOPIC_RULES:
        if any(k in t for k in kws):
            return folder
    return "xai_general"


def cmd_download():
    entries = parse_bib(OUT_BIB.read_text())
    have = existing_pdf_titles()
    log, unreachable = [], []
    for e in entries:
        title = strip_tex(get_field(e["body"], "title"))
        if not title or norm_title(title) in have:
            continue
        body = e["body"]
        arxiv_m = (re.search(r"(\d{4}\.\d{4,5})", get_field(body, "eprint") or "")
                   or re.search(r"arxiv\.org/(?:abs|pdf)/(\d{4}\.\d{4,5})",
                                get_field(body, "url") or ""))
        if not arxiv_m:
            unreachable.append((e["key"], title))
            continue
        folder = LIT_DIR / guess_topic(title)
        folder.mkdir(exist_ok=True)
        safe = re.sub(r"[^A-Za-z0-9]+", "", title.title())[:60]
        year = get_field(body, "year") or "0000"
        dest = folder / f"{year}_{safe}.pdf"
        try:
            url = f"https://arxiv.org/pdf/{arxiv_m.group(1)}"
            data = urllib.request.urlopen(
                urllib.request.Request(url, headers=UA), timeout=60).read()
            if data[:4] == b"%PDF":
                dest.write_bytes(data)
                log.append((dest.relative_to(LIT_DIR), title, year))
                print(f"  downloaded {dest.name}")
            else:
                unreachable.append((e["key"], title))
        except Exception:
            unreachable.append((e["key"], title))
        time.sleep(2.0)

    if log:
        with (LIT_DIR / "downloaded_papers.md").open("a") as f:
            f.write(f"\n## Added by merge_bibliography.py\n\n| File | Title | Year |\n|------|-------|------|\n")
            f.writelines(f"| {p} | {t} | {y} |\n" for p, t, y in log)
    if unreachable:
        with (LIT_DIR / "unreachable_papers.md").open("a") as f:
            f.write("\n## Not auto-downloadable (merge_bibliography.py; no arXiv id)\n\n")
            f.writelines(f"- **{k}** — {t}\n" for k, t in unreachable)
    print(f"\nDownloaded {len(log)}; not auto-downloadable: {len(unreachable)} (appended to tracking files)")


if __name__ == "__main__":
    {"merge": cmd_merge, "download": cmd_download}.get(
        sys.argv[1] if len(sys.argv) > 1 else "", lambda: print(__doc__))()
