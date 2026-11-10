"""Account for published and explicitly retired labels in the pinned Lean map."""
from collections import Counter
import json
from pathlib import Path
import re

from check_paper_references import strip_comments

ROOT = Path(__file__).resolve().parents[1]
RETIREMENTS = ROOT / "tex/preamble/lean_links_retired.json"


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


def published_link_inventory(config):
    retired = retired_labels(config)
    sources = [path for directory in ("tex/chapters", "tex/supplement")
               for path in (ROOT / directory).rglob("*.tex")]
    text = "\n".join(strip_comments(path.read_text()) for path in sources)
    labels = Counter(re.findall(r"\\label\{([^}]+)\}", text))
    uses = Counter(re.findall(r"\\(?:LeanResult|leandecl)\{([^}]+)\}", text))
    unknown = set(uses) - set(config)
    if unknown:
        raise ValueError("Unmapped Lean badges: " + str(sorted(unknown)))
    for label, spec in config.items():
        if spec.get("equation") and labels[label]:
            uses[label] += labels[label]
    reintroduced = retired & (set(labels) | set(uses))
    if reintroduced:
        raise ValueError("Retired Lean labels still appear in TeX: " + str(sorted(reintroduced)))
    unaccounted = set(config) - set(uses) - retired
    if unaccounted:
        raise ValueError("Mapped Lean labels neither published nor explicitly retired: "
                         + str(sorted(unaccounted)))
    return uses, retired
