"""Verify raw/adapted table agreement and mirror reviewed raw outputs to the paper."""
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
from generate_thesis_tables import canonical_tex, check_outputs
from table_presentation import present

manifest = json.loads((ROOT / 'scripts/table_sources.json').read_text())
source = manifest['repositories']['playing_backward']
names = source['table_generation']['generated_outputs']
provenance = json.loads((EVIDENCE / 'tables-pinned-check/provenance.json').read_text())
assert provenance['actual_commit'] == provenance['expected_commit'] == source['verified_commit']
assert not provenance['tracked_source_modified']
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
checks = []
for name in names:
    raw = EVIDENCE / 'tables-raw' / name
    adapted = EVIDENCE / 'tables-pinned-check' / name
    thesis = ROOT / 'tex/tables/ptnb_v2/generated' / name
    paper = ROOT / 'arxive/playingTheNetworkBackward/tables/generated' / name
    assert sha(raw) == provenance['raw_upstream_sha256'][name], name
    assert present(name, raw.read_text())[0] == adapted.read_text(), name
    assert canonical_tex(adapted) == canonical_tex(thesis), name
    shutil.copyfile(raw, paper)
    assert sha(raw) == sha(paper), name
    checks.append({'file': name, 'raw_sha256': sha(raw), 'adapted_sha256': sha(adapted),
                   'paper_equals_raw': True, 'thesis_equals_adapted': True})
matches, mismatches = check_outputs(EVIDENCE / 'tables-pinned-check', names)
assert not mismatches, mismatches
report = {
    'generation_source_commit': provenance['actual_commit'],
    'manifest_verified_commit_at_integration': source['verified_commit'],
    'results_only': True, 'fresh_model_evaluation': False, 'strict': True,
    'generated_outputs': len(names), 'checks': checks, 'mismatches': mismatches,
    'change_review': 'reports/evidence/voc-cluster-repair/table_change_review.json',
    'generation_provenance': 'reports/evidence/voc-cluster-repair/tables-pinned-check/provenance.json',
    'generation_log': 'reports/evidence/voc-cluster-repair/tables-pinned-check.log',
}
(EVIDENCE / 'table_integration.json').write_text(json.dumps(report, indent=2) + '\n')
current = {'source_commit': provenance['actual_commit'],
           'raw_generation_log': report['generation_log'],
           'updated_presentation_checks': matches, 'mismatches': [],
           'final_adaptation_changes': provenance['thesis_presentation_changes'],
           'experiments_rerun': False,
           'statistical_reaggregation_rerun': True,
           'note': 'Existing scores reaggregated with image-cluster VOC inference and all-pairs Holm correction. Point estimates and ImageNet intervals remain unchanged. Thirteen raw paper outputs and thirteen adapted thesis outputs verified.',
           'output_sha256': {name: sha(EVIDENCE / 'tables-pinned-check' / name) for name in names},
           'detailed_evidence': str((EVIDENCE / 'table_integration.json').relative_to(ROOT))}
(ROOT / 'reports/table-adapter-verification.json').write_text(json.dumps(current, indent=2) + '\n')
print(json.dumps({'n_outputs': len(names), 'mismatches': mismatches,
                  'paper_equals_raw': True, 'thesis_equals_adapted': True}, indent=2))
