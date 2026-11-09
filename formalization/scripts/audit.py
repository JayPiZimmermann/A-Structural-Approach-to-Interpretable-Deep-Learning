#!/usr/bin/env python3
"""Generate explicit checks of every project theorem's transitive axioms."""
import json
import importlib.util
from pathlib import Path
root = Path(__file__).resolve().parents[1]
lines = ['import All', '']
spec = importlib.util.spec_from_file_location('lean_links', root.parent / 'scripts/generate_lean_links.py')
links = importlib.util.module_from_spec(spec)
spec.loader.exec_module(links)
for folder in ['HiddenMonotonicity', 'Thesis']:
    for path in sorted((root / folder).rglob('*.lean')):
        for name, declaration in links.declarations(path.read_text(), str(path.relative_to(root))).items():
            if declaration['kind'] in {'theorem', 'lemma'}:
                lines.append(f'#print axioms {name}')
coverage = json.loads((root / 'coverage_map.json').read_text())
refs = sorted({name for claim in coverage.values() for name in claim.get('lean', [])})
config = root / 'tex_links.json'
if config.exists():
    refs = sorted(set(refs) | {v['declaration'] for v in json.loads(config.read_text()).values()})
lines += ['', '-- Verify that all mapped Lean identifiers exist.']
lines += [f'#check {name}' for name in refs]
(root / 'Audit.lean').write_text('\n'.join(lines) + '\n')
print(f'Generated {len(lines)} audit/check commands in Audit.lean')
