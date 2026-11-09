"""Compare executed row-bootstrap and image-cluster reaggregations of VOC scores."""
import csv
import hashlib
import json
import platform
import subprocess
import sys
from collections import Counter
from pathlib import Path

import numpy as np
import scipy
import torch

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = Path(__file__).resolve().parent
CODE = ROOT / 'code/playing_backward'
sys.path.insert(0, str(CODE))
from reproduce.bootstrap_ci import load_scores, METRICS


def read_csv(path):
    with path.open() as stream:
        return list(csv.DictReader(stream))


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


before_ci = {(r['row'], r['metric']): r for r in read_csv(EVIDENCE / 'before/ci.csv')}
after_ci = {(r['row'], r['metric']): r for r in read_csv(EVIDENCE / 'after/ci.csv')}
assert before_ci.keys() == after_ci.keys()
ci_changes = []
for key, before in before_ci.items():
    after = after_ci[key]
    old, new = float(before['mean']), float(after['mean'])
    assert old == new or (np.isnan(old) and np.isnan(new))
    if not np.isfinite(new):
        continue
    old_width = float(before['hi']) - float(before['lo'])
    new_width = float(after['hi']) - float(after['lo'])
    ci_changes.append({'row': key[0], 'metric': key[1], 'mean': new,
                       'before_lo': float(before['lo']), 'before_hi': float(before['hi']),
                       'after_lo': float(after['lo']), 'after_hi': float(after['hi']),
                       'width_ratio': new_width / old_width if old_width else None})
with (EVIDENCE / 'interval_changes.csv').open('w', newline='') as stream:
    writer = csv.DictWriter(stream, fieldnames=list(ci_changes[0]))
    writer.writeheader()
    writer.writerows(ci_changes)

before_sig = {(r['metric'], r['best_row'], r['row']): r
              for r in read_csv(EVIDENCE / 'before/significance.csv')}
after_sig = {(r['metric'], r['best_row'], r['row']): r
             for r in read_csv(EVIDENCE / 'after/significance.csv')}
assert before_sig.keys() == after_sig.keys()
changed_sig = []
for key, before in before_sig.items():
    after = after_sig[key]
    if before['significant'] != after['significant']:
        changed_sig.append({'metric': key[0], 'best_row': key[1], 'row': key[2],
                            'before_p_holm': float(before['p_holm']),
                            'after_p_holm': float(after['p_holm']),
                            'before_significant': int(before['significant']),
                            'after_significant': int(after['significant'])})
(EVIDENCE / 'changed_significance.json').write_text(json.dumps(changed_sig, indent=2) + '\n')
rows, ids, scores = load_scores(CODE / 'results_summary/voc/test')
images = Counter(sample.rsplit('__', 1)[0] for sample in ids)
summary = {
    'execution': 'CPU reaggregation of existing stored evaluation scores; no fresh model inference or training',
    'n_rows': len(scores), 'n_image_class_records': len(ids), 'n_independent_images': len(images),
    'n_images_with_multiple_classes': sum(count > 1 for count in images.values()),
    'maximum_classes_per_image': max(images.values()),
    'n_boot': 10000, 'seed': 0,
    'all_point_means_unchanged': True,
    'all_observed_winner_labels_unchanged': True,
    'n_finite_intervals': len(ci_changes),
    'interval_width_ratio_median': float(np.median([r['width_ratio'] for r in ci_changes])),
    'interval_width_ratio_min': min(r['width_ratio'] for r in ci_changes),
    'interval_width_ratio_max': max(r['width_ratio'] for r in ci_changes),
    'n_changed_winner_comparison_significance_flags': len(changed_sig),
    'significant_winner_comparisons_by_metric': {
        m: {'before': sum(int(r['significant']) for r in before_sig.values() if r['metric'] == m),
            'after': sum(int(r['significant']) for r in after_sig.values() if r['metric'] == m)}
        for m in METRICS if any(r['metric'] == m for r in before_sig.values())},
    'changes_combine': ['image-cluster resampling', 'cluster-bootstrap PG test',
                        'plus-one Monte Carlo p-value correction for VOC',
                        'Holm over all eligible unordered method pairs'],
    'family_size_per_reported_metric': 210,
    'limitations': ['fixed released checkpoint and selected configurations',
                    'no uncertainty across independently trained models',
                    'bootstrap inference is asymptotic; non-rejection is not equivalence'],
}
(EVIDENCE / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
receipt = {
    'cwd': str(ROOT), 'python_executable': sys.executable, 'python_version': sys.version,
    'platform': platform.platform(),
    'packages': {'numpy': np.__version__, 'scipy': scipy.__version__, 'torch': torch.__version__},
    'official_repository': subprocess.check_output(['git', '-C', str(CODE), 'remote', 'get-url', 'origin'], text=True).strip(),
    'base_commit': subprocess.check_output(['git', '-C', str(CODE), 'rev-parse', 'HEAD'], text=True).strip(),
    'local_branch': subprocess.check_output(['git', '-C', str(CODE), 'branch', '--show-current'], text=True).strip(),
    'scores_sha256': sha256(CODE / 'results_summary/voc/test/per_image_scores.csv.gz'),
    'source_sha256': {str(p.relative_to(ROOT)): sha256(p) for p in
                      [CODE / 'reproduce/bootstrap_ci.py', CODE / 'reproduce/make_tables.py',
                       CODE / 'tests/test_bootstrap_ci.py', EVIDENCE / 'before/bootstrap_ci.py']},
    'summarize_command': [sys.executable, *sys.argv],
}
(EVIDENCE / 'execution_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(summary, indent=2))
