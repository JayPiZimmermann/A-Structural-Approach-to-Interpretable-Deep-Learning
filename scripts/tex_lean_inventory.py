"""Inventory the single active thesis and editorial aliases of its pinned Lean map.

The proof map remains immutable. A removed duplicate may use AliasLabel, but every
non-retired mapped declaration must still have a physical source link. Actual
links, rather than historical duplicate occurrences, determine the PDF count.
"""
from collections import Counter
import json
import hashlib
from pathlib import Path
import re

from check_paper_references import strip_comments, tex_closure

ROOT = Path(__file__).resolve().parents[1]
RETIREMENTS = ROOT / "tex/preamble/lean_links_retired.json"
ALIAS_REVIEWS = ROOT / "reports/single-pdf/lean-alias-reviews.json"
LABEL_RE = re.compile(r"\\label\s*\{([^}]+)\}")
BADGE_RE = re.compile(r"\\(?:LeanResult|leandecl)\s*\{([^}]+)\}")
ALIAS_RE = re.compile(r"\\AliasLabel\s*\{([^}]+)\}\s*\{([^}]+)\}")


def active_tex_sources(root=ROOT):
    sources, unresolved = tex_closure(root / "tex/main.tex", root / "tex")
    if unresolved:
        raise ValueError("Unresolved active thesis inputs: " + str(unresolved))
    return sources


def retired_labels(config):
    record = json.loads(RETIREMENTS.read_text())
    labels = record["retired_labels"]
    if len(labels) != len(set(labels)):
        raise ValueError("Duplicate retired Lean labels")
    unknown = set(labels) - set(config)
    if unknown:
        raise ValueError("Retired labels absent from pinned Lean map: " + str(sorted(unknown)))
    if not record.get("reason") or not record.get("editorial_source_commit"):
        raise ValueError("Lean label retirement requires an editorial reason and source commit")
    return set(labels)


def source_label_inventory(sources):
    labels, badges, aliases, locations = Counter(), Counter(), {}, {}
    for path in sources:
        text = strip_comments(path.read_text())
        # Preamble macro parameters are definitions, not concrete published uses.
        for regex, counter in ((LABEL_RE, labels), (BADGE_RE, badges)):
            for match in regex.finditer(text):
                key = match[1]
                if "#" in key:
                    continue
                counter[key] += 1
                locations.setdefault(key, []).append(str(path))
        for match in ALIAS_RE.finditer(text):
            alias, target = match.groups()
            if "#" in alias or "#" in target:
                continue
            if alias in aliases:
                raise ValueError("Duplicate AliasLabel definition: " + alias)
            aliases[alias] = target
    duplicates = {key: n for key, n in labels.items() if n != 1}
    if duplicates:
        raise ValueError("Duplicate physical labels in active thesis: " + str(duplicates))
    collisions = set(labels) & set(aliases)
    if collisions:
        raise ValueError("Aliases also defined as physical labels: " + str(sorted(collisions)))
    resolved = {}
    for alias in aliases:
        visited, target = {alias}, aliases[alias]
        while target in aliases:
            if target in visited:
                raise ValueError("Cyclic AliasLabel chain: " + alias)
            visited.add(target)
            target = aliases[target]
        if target not in labels:
            raise ValueError("AliasLabel target absent from active thesis: " + alias + " -> " + target)
        resolved[alias] = target
    return labels, badges, aliases, resolved, locations


def published_link_details(config):
    retired = retired_labels(config)
    sources = active_tex_sources()
    labels, uses, aliases, resolved, locations = source_label_inventory(sources)
    unknown = set(uses) - set(config)
    if unknown:
        raise ValueError("Unmapped Lean badges: " + str(sorted(unknown)))
    # AliasLabel creates a cross-reference, not another equation tag or Lean URI.
    for label, spec in config.items():
        if spec.get("equation") and labels[label]:
            uses[label] += labels[label]
    reintroduced = retired & (set(labels) | set(uses) | set(aliases))
    if reintroduced:
        raise ValueError("Retired Lean labels still appear in active TeX: " + str(sorted(reintroduced)))
    represented = {config[key]["declaration"] for key in uses}
    required = {spec["declaration"] for key, spec in config.items() if key not in retired}
    missing_declarations = required - represented
    if missing_declarations:
        raise ValueError("Unique mapped Lean declarations lack a published link: " + str(sorted(missing_declarations)))
    review_file = json.loads(ALIAS_REVIEWS.read_text()) if ALIAS_REVIEWS.exists() else {}
    reviews = review_file.get("aliases", {})
    if reviews and not review_file.get("baseline_commit"):
        raise ValueError("Lean alias reviews require a baseline commit")
    alias_coverage = {}
    unaccounted = []
    for key in set(config) - set(uses) - retired:
        target = resolved.get(key)
        if target is None:
            unaccounted.append(key)
            continue
        declaration = config[key]["declaration"]
        witnesses = [label for label in uses if config[label]["declaration"] == declaration]
        if not witnesses:
            unaccounted.append(key)
            continue
        same_declaration = target in config and config[target]["declaration"] == declaration
        if not same_declaration:
            review = reviews.get(key, {})
            expected = {"canonical_label": target, "declaration": declaration}
            if (any(review.get(k) != v for k, v in expected.items())
                    or not review.get("reason") or not review.get("reviewed_by")):
                raise ValueError("Different-target Lean alias needs explicit review: " + key + " -> " + target)
            files = review.get("source_sha256", {})
            if not files or any(not (ROOT / name).is_file() or hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != value
                                for name, value in files.items()):
                raise ValueError("Missing or stale source hashes in Lean alias review: " + key)
            target_locations = {str(path.relative_to(ROOT)) for path in sources
                                if str(path) in locations.get(target, [])}
            if not target_locations <= set(files):
                raise ValueError("Lean alias review does not bind its canonical target: " + key)
        alias_coverage[key] = {"canonical_label": target,
                              "declaration": declaration,
                              "physical_link_labels": sorted(witnesses),
                              "canonical_has_same_declaration": same_declaration,
                              "review": reviews.get(key) if not same_declaration else "same pinned declaration"}
    if unaccounted:
        raise ValueError("Mapped Lean labels neither published, aliased with retained proof coverage, nor explicitly retired: " + str(sorted(unaccounted)))
    return {"uses": uses, "retired": retired, "sources": sources,
            "labels": labels, "aliases": aliases, "resolved_aliases": resolved,
            "alias_coverage": alias_coverage, "represented_declarations": represented}


def published_link_inventory(config):
    details = published_link_details(config)
    return details["uses"], details["retired"]
