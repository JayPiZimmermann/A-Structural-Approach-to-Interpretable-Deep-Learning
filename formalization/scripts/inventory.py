#!/usr/bin/env python3
"""Inventory explicit theorem-like statements; no claim of automatic verification."""
import json
import re
from pathlib import Path
root = Path(__file__).resolve().parents[2]
claims = []
coverage = json.loads((root / "formalization/coverage_map.json").read_text())
for group, directory in [('hidden_monotonicity', 'arxive/hiddenMonotonicity'),
                         ('playing_backward', 'arxive/playingTheNetworkBackward'),
                         ('thesis', 'tex/chapters')]:
    for path in sorted((root / directory).rglob('*.tex')):
        text = path.read_text()
        for match in re.finditer(r'\\begin\{(theorem(?:env)?|lemma(?:env)?|proposition(?:env)?|corollary(?:env)?|claim|definition(?:env)?)\}(.*?)(?=\\end\{\1\})', text, re.S):
            label = re.search(r'\\label\{([^}]+)\}', match.group(2))
            entry = {'source_group': group, 'file': str(path.relative_to(root)),
                           'line': text[:match.start()].count('\n') + 1,
                           'environment': match.group(1),
                           'label': label.group(1) if label else None,
                           'status': 'not_formalized',
                           'statement_tex': match.group(2).strip()}
            canonical_label = entry['label'].removeprefix('ptnb:') if entry['label'] else None
            entry.update(coverage.get(canonical_label, {}))
            claims.append(entry)
output = root / 'formalization/claim_inventory.json'
output.write_text(json.dumps(claims, indent=2) + '\n')
print(f'{len(claims)} statements inventoried in {output}')
