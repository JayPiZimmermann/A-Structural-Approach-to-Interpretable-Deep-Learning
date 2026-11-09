"""Audit table changes before copying deliberately reviewed outputs."""
import json
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
from table_presentation import cells
from generate_thesis_tables import canonical_tex

names = json.loads((ROOT / 'scripts/table_sources.json').read_text())['repositories']['playing_backward']['table_generation']['generated_outputs']
for name, source in [('tables-before-thesis', ROOT / 'tex/tables/ptnb_v2/generated'),
                     ('tables-before-paper', ROOT / 'arxive/playingTheNetworkBackward/tables/generated')]:
    destination = EVIDENCE / name
    destination.mkdir(exist_ok=True)
    for filename in names:
        if not (destination / filename).exists():
            shutil.copyfile(source / filename, destination / filename)

ci_re = re.compile(r'\\begin\{tabular\}\[t\]\{@\{\}c@\{\}\}(.*?)\\\\\[-1pt\]\{\\tiny\[([^,]+),([^]]+)\]\}\\end\{tabular\}')
number = re.compile(r'[-+]?\d+(?:\.\d+)?')

def rows(path):
    return [r[0] for line in path.read_text().splitlines() if (r := cells(line))]


def marker(cell):
    return 'best' if r'\cellbest{' in cell else 'non_rejected' if r'\cellapprox{' in cell else 'unmarked'


out = {'point_means_unchanged': True, 'row_descriptors_unchanged': True,
       'imagenet_intervals_unchanged': True, 'tables': [], 'marker_changes': [], 'voc_interval_changes': []}
for filename in names:
    before = EVIDENCE / 'tables-before-thesis' / filename
    after = EVIDENCE / 'tables-review' / filename
    same = canonical_tex(before) == canonical_tex(after)
    entry = {'file': filename, 'canonical_unchanged': same}
    out['tables'].append(entry)
    if same:
        continue
    assert filename == 'main_vit_tabular.tex' or filename.startswith('test_'), filename
    old_rows, new_rows = rows(before), rows(after)
    assert len(old_rows) == len(new_rows), filename
    for old, new in zip(old_rows, new_rows):
        assert old[:2] == new[:2], (filename, old[:2], new[:2])
        assert len(old) == len(new), filename
        for index, (old_cell, new_cell) in enumerate(zip(old[2:], new[2:]), 2):
            old_ci, new_ci = ci_re.search(old_cell), ci_re.search(new_cell)
            assert bool(old_ci) == bool(new_ci), (filename, old[0], index)
            if not old_ci:
                assert old_cell == new_cell, (filename, old[0], index)
                continue
            old_mean = number.findall(old_ci.group(1))
            new_mean = number.findall(new_ci.group(1))
            assert old_mean == new_mean, (filename, old[0], index, old_mean, new_mean)
            if old_ci.group(2, 3) != new_ci.group(2, 3):
                assert filename == 'test_voc_vit_b16_ci_longtable.tex', (filename, old[0], index)
                out['voc_interval_changes'].append({'row': old[0], 'column_index': index,
                    'before': old_ci.group(2, 3), 'after': new_ci.group(2, 3)})
            if marker(old_cell) != marker(new_cell):
                assert marker(old_cell) != 'best' and marker(new_cell) != 'best'
                out['marker_changes'].append({'file': filename, 'row': old[0], 'column_index': index,
                                             'before': marker(old_cell), 'after': marker(new_cell)})
    entry['changed_lines'] = sum(a != b for a, b in zip(before.read_text().splitlines(), after.read_text().splitlines()))
out['n_marker_changes'] = len(out['marker_changes'])
out['n_voc_intervals_changed_at_display_precision'] = len(out['voc_interval_changes'])
(EVIDENCE / 'table_change_review.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({k: v for k, v in out.items() if k not in ['voc_interval_changes']}, indent=2))
