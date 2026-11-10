#!/usr/bin/env python3
"""Read-only structural/word-count audit of a thesis concision proposal.

This is a mechanical comparison, not a semantic or mathematical equivalence proof.
The baseline is the frozen working tree (including the author's uncommitted intro
edit), not merely its Git parent. All outputs are written only to --output.
"""
from __future__ import annotations
import argparse
from collections import Counter
from datetime import datetime, timezone
from difflib import SequenceMatcher
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

CACHE = Path(__file__).resolve().parent
DEFAULT_REPO = Path(__file__).resolve().parents[2]
WEIGHTS = '1,1,1,0,0,0,0'
HEADINGS = {'chapter', 'section', 'subsection', 'subsubsection', 'paragraph', 'subparagraph'}
BADGES = {'LeanResult', 'leandecl'}
DISPLAYS = {'equation', 'equation*', 'align', 'align*', 'gather', 'gather*',
            'multline', 'multline*', 'displaymath', 'eqnarray', 'eqnarray*',
            'flalign', 'flalign*', 'alignat', 'alignat*', 'dmath', 'dmath*', 'mathpar'}
STATEMENTS = {'theoremenv', 'theorem', 'lemmaenv', 'lemma', 'proposition',
              'corollary', 'definition', 'observation', 'remark', 'proof'}
LAYOUT_NOARGS = {'tiny', 'scriptsize', 'footnotesize', 'small', 'normalsize',
                 'large', 'Large', 'LARGE', 'huge', 'Huge'}
LAYOUT_ARGS = {'vspace', 'hspace', 'linespread', 'setlength', 'addtolength', 'fontsize'}
REF_COMMANDS = {'ref', 'eqref', 'cref', 'Cref', 'autoref', 'pageref', 'nameref'}
COMMAND = re.compile(r'\\([A-Za-z@]+)(\*)?')
VERBATIM = re.compile(r'\\begin\{(verbatim\*?|lstlisting|minted)\}.*?\\end\{\1\}', re.S)
NUMBER = re.compile(r'(?<![A-Za-z0-9_])[-+]?\d+(?:[.,]\d+)*(?:[eE][-+]?\d+)?(?:\\%)?')


def digest(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()


def norm(s):
    return re.sub(r'\s+', ' ', s).strip()


def escaped(text, pos):
    n = 0
    while pos > 0 and text[pos - 1] == '\\':
        pos -= 1
        n += 1
    return n % 2 == 1


def mask_spans(text, spans):
    chars = list(text)
    for lo, hi in spans:
        for i in range(lo, hi):
            if chars[i] != '\n':
                chars[i] = ' '
    return ''.join(chars)


def group(text, pos, opener='{', closer='}'):
    if pos >= len(text) or text[pos] != opener:
        return None, pos
    depth, braces = 0, 0
    for i in range(pos, len(text)):
        c = text[i]
        if escaped(text, i):
            continue
        if opener == '[':
            if c == '{': braces += 1
            elif c == '}': braces -= 1
            if braces:
                continue
        if c == opener: depth += 1
        elif c == closer:
            depth -= 1
            if depth == 0:
                return text[pos + 1:i], i + 1
    raise ValueError(f'Unclosed {opener} argument at character {pos}')


def args_after(text, pos):
    opts = []
    while True:
        while pos < len(text) and text[pos].isspace(): pos += 1
        if pos < len(text) and text[pos] == '[':
            value, pos = group(text, pos, '[', ']')
            opts.append(norm(value))
        else:
            break
    if pos < len(text) and text[pos] == '{':
        value, end = group(text, pos)
        return opts, value, end
    return opts, None, pos


def commands(text, names=None):
    for match in COMMAND.finditer(text):
        if escaped(text, match.start()): continue
        if names is not None and match[1] not in names: continue
        options, value, end = args_after(text, match.end())
        yield {'command': match[1], 'star': bool(match[2]), 'options': options,
               'argument': value, 'start': match.start(), 'end': end,
               'line': text.count('\n', 0, match.start()) + 1}


def math_items(text):
    """Collect outer displays and inline math without interpreting LaTeX macros."""
    token = re.compile(r'\\begin\{([^}]+)\}|\\\[|\\\(|\$\$|\$')
    items, errors, cursor = [], [], 0
    while match := token.search(text, cursor):
        lo = match.start()
        if escaped(text, lo):
            cursor = match.end(); continue
        raw, env = match[0], match[1]
        if env:
            if env not in DISPLAYS and env != 'math':
                cursor = match.end(); continue
            closing = '\\end{' + env + '}'
            kind = 'inline' if env == 'math' else 'display'
        elif raw == '\\[': closing, kind = '\\]', 'display'
        elif raw == '\\(': closing, kind = '\\)', 'inline'
        elif raw == '$$': closing, kind = '$$', 'display'
        else: closing, kind = '$', 'inline'
        endpos = text.find(closing, match.end())
        while endpos >= 0 and escaped(text, endpos):
            endpos = text.find(closing, endpos + len(closing))
        if endpos < 0:
            errors.append({'line': text.count('\n', 0, lo) + 1, 'unclosed': raw})
            cursor = match.end(); continue
        hi = endpos + len(closing)
        payload = norm(text[match.end():endpos])
        items.append({'kind': kind, 'delimiter': raw, 'payload': payload,
                      'start': lo, 'end': hi, 'line': text.count('\n', 0, lo) + 1})
        cursor = hi
    return items, errors


def texcount(path):
    result = subprocess.run(['texcount', '-utf8', '-brief', '-sum=' + WEIGHTS, str(path)],
                            text=True, capture_output=True, check=True)
    match = re.search(r'^(\d+): File:', result.stdout, re.M)
    if not match:
        raise ValueError(f'Cannot parse TeXcount for {path}: {result.stdout!r}')
    diagnostics = '\n'.join(line for line in result.stderr.splitlines()
                            if not line.startswith('SUMWEIGHTS:'))
    return int(match[1]), diagnostics


def inventory(path, reference):
    raw = path.read_bytes()
    clean = reference.strip_comments(raw.decode())
    clean = mask_spans(clean, [(m.start(), m.end()) for m in VERBATIM.finditer(clean)])
    include_cmds = reference.INCLUDE_COMMANDS | {'includegraphics', 'IfFileExists'}
    interested = HEADINGS | BADGES | include_cmds | LAYOUT_NOARGS | LAYOUT_ARGS | REF_COMMANDS | reference.CITATION_COMMANDS | {'label', 'begin'}
    cmds = list(commands(clean, interested))
    items, math_errors = math_items(clean)
    selected = lambda names: [c for c in cmds if c['command'] in names]
    simple = lambda c: {k: c[k] for k in ('command', 'star', 'options', 'argument')}
    headings = [simple(c) for c in selected(HEADINGS)]
    labels = [norm(c['argument'] or '') for c in selected({'label'})]
    badges = [simple(c) for c in selected(BADGES)]
    paths = [simple(c) for c in selected(include_cmds)]
    statements = []
    for c in selected({'begin'}):
        if c['argument'] in STATEMENTS:
            options, _, _ = args_after(clean, c['end'])
            statements.append({'environment': c['argument'], 'options': options})
    layout = []
    for c in selected(LAYOUT_NOARGS | LAYOUT_ARGS):
        entry = simple(c)
        if c['command'] in {'fontsize', 'setlength', 'addtolength'}:
            _, trailing, _ = args_after(clean, c['end'])
            entry['second_argument'] = trailing
        layout.append(entry)
    # Arguments following a no-arg size command are prose, not layout parameters.
    for entry in layout:
        if entry['command'] in LAYOUT_NOARGS:
            entry['options'], entry['argument'] = [], None
    citations = reference.citation_keys(clean)
    suppress = reference.CITATION_COMMANDS | include_cmds | REF_COMMANDS | BADGES | {'label'} | LAYOUT_ARGS
    prose = mask_spans(clean, [(m['start'], m['end']) for m in items] +
                       [(c['start'], c['end']) for c in cmds if c['command'] in suppress])
    numeric = []
    for match in NUMBER.finditer(prose):
        numeric.append({'value': match[0], 'line': prose.count('\n', 0, match.start()) + 1,
                        'context': norm(prose[max(0, match.start()-75):match.end()+75])})
    count, count_diagnostics = texcount(path)
    return {'sha256': digest(raw), 'prose_words': count, 'texcount_diagnostics': count_diagnostics,
            'headings': headings, 'labels': labels, 'lean_badges': badges,
            'citation_keys': sorted(citations),
            'citation_occurrences': {k: len(v) for k, v in sorted(citations.items())},
            'input_and_graphics_commands': paths, 'statement_sequence': statements,
            'layout_commands': layout, 'display_math': [m for m in items if m['kind']=='display'],
            'inline_math': [m for m in items if m['kind']=='inline'],
            'math_parse_errors': math_errors, 'potential_numeric_facts': numeric}


def sequence_changes(old, new):
    changes = []
    for tag, i, j, k, l in SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
        if tag != 'equal': changes.append({'operation': tag, 'old_indices': [i,j],
                                           'new_indices': [k,l], 'old': old[i:j], 'new': new[k:l]})
    return changes


def compare(before, after):
    hard_fields = ['headings', 'labels', 'lean_badges', 'citation_keys',
                   'input_and_graphics_commands', 'statement_sequence', 'layout_commands']
    invariant = {name: before[name] == after[name] for name in hard_fields}
    old_math = [m['payload'] for m in before['display_math']]
    new_math = [m['payload'] for m in after['display_math']]
    invariant['display_math_payloads_and_order'] = old_math == new_math
    invariant['math_delimiters_balanced'] = not after['math_parse_errors']
    changed = {}
    for name in hard_fields:
        if not invariant[name]:
            changed[name] = {'before': before[name], 'after': after[name]}
    math_changes = sequence_changes(old_math, new_math)
    inline_changes = sequence_changes([m['payload'] for m in before['inline_math']],
                                      [m['payload'] for m in after['inline_math']])
    old_numbers = Counter(n['value'] for n in before['potential_numeric_facts'])
    new_numbers = Counter(n['value'] for n in after['potential_numeric_facts'])
    removed, added = old_numbers-new_numbers, new_numbers-old_numbers
    numeric_changes = {'removed_occurrence_counts': dict(removed), 'added_occurrence_counts': dict(added),
                       'baseline_contexts': [n for n in before['potential_numeric_facts'] if n['value'] in removed],
                       'target_contexts': [n for n in after['potential_numeric_facts'] if n['value'] in added]}
    b, a = before['prose_words'], after['prose_words']
    return {'before_sha256': before['sha256'], 'after_sha256': after['sha256'],
            'baseline_prose_words': b, 'target_prose_words': a,
            'words_removed': b-a, 'reduction_percent': round(100*(b-a)/b, 3) if b else 0.0,
            'hard_invariants': invariant, 'hard_invariants_pass': all(invariant.values()),
            'changed_structural_payloads': changed, 'changed_display_math': math_changes,
            'inline_math_changes_for_review': inline_changes,
            'potential_numeric_changes_for_review': numeric_changes,
            'citation_occurrence_changes': {k: [before['citation_occurrences'].get(k,0), after['citation_occurrences'].get(k,0)]
              for k in sorted(set(before['citation_occurrences']) | set(after['citation_occurrences']))
              if before['citation_occurrences'].get(k,0) != after['citation_occurrences'].get(k,0)},
            'manual_review_needed': bool(inline_changes or removed or added or not all(invariant.values())),
            'math_parse_errors': after['math_parse_errors'],
            'texcount_diagnostics': after['texcount_diagnostics']}


def summarize_inventory(inv):
    result = {k: v for k,v in inv.items() if k not in {'display_math','inline_math','potential_numeric_facts'}}
    for field in ('display_math','inline_math'):
        result[field+'_count'] = len(inv[field])
        result[field+'_payload_sha256'] = [digest(m['payload']) for m in inv[field]]
    result['potential_numeric_value_counts'] = dict(Counter(n['value'] for n in inv['potential_numeric_facts']))
    return result


def totals(records):
    groups = {'main': [v for p,v in records.items() if '/supplement/' not in p],
              'supplement': [v for p,v in records.items() if '/supplement/' in p],
              'overall': list(records.values())}
    out = {}
    for name, rows in groups.items():
        b = sum(r['baseline_prose_words'] for r in rows)
        a = sum(r['target_prose_words'] for r in rows)
        reduction = 100*(b-a)/b if b else 0
        out[name] = {'baseline_prose_words': b, 'target_prose_words': a,
                     'words_removed': b-a, 'reduction_percent': round(reduction,3),
                     'within_requested_10_to_20_percent': 10 <= reduction <= 20}
    return out


def self_check():
    text = r'caption \\[3pt] and $x$ then \[ y \] and \(z\) and \begin{align}a&=b\end{align}'
    items, errors = math_items(text)
    assert not errors
    assert [(m['kind'],m['payload']) for m in items] == [('inline','x'),('display','y'),('inline','z'),('display','a&=b')]
    headings = list(commands(r'\section{A \texorpdfstring{$x$}{x} heading}'))
    assert headings[0]['argument'] == r'A \texorpdfstring{$x$}{x} heading'
    opts, arg, _ = args_after(r'[A $[0,1]$]{B}',0)
    assert opts == ['A $[0,1]$'] and arg == 'B'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=DEFAULT_REPO)
    parser.add_argument('--manifest', type=Path, default=CACHE/'baseline-manifest.json')
    parser.add_argument('--baseline-root', type=Path, default=CACHE/'baseline')
    parser.add_argument('--target-root', type=Path, default=DEFAULT_REPO)
    parser.add_argument('--output', type=Path, default=CACHE/'concision-audit.json')
    parser.add_argument('--baseline-only', action='store_true')
    parser.add_argument('--partial', action='store_true', help='Use baseline for target files not yet proposed; mark them explicitly.')
    parser.add_argument('--fail-on-invariant-change', action='store_true')
    args = parser.parse_args()
    self_check()
    spec = importlib.util.spec_from_file_location('thesis_ref_audit', args.repo/'scripts/check_paper_references.py')
    reference = importlib.util.module_from_spec(spec); spec.loader.exec_module(reference)
    manifest = json.loads(args.manifest.read_text())
    records, inventory_rows, fallback = {}, {}, []
    for rel, expected in manifest['files'].items():
        path = args.baseline_root/rel
        if digest(path.read_bytes()) != expected['sha256']:
            raise ValueError(f'Frozen baseline hash mismatch: {rel}')
        before = inventory(path, reference)
        inventory_rows[rel] = summarize_inventory(before)
        target = args.target_root/rel
        if args.baseline_only:
            after = before
        elif target.exists():
            after = inventory(target, reference)
        elif args.partial:
            after = before; fallback.append(rel)
        else:
            raise FileNotFoundError(f'Target missing: {target}; use --partial for unfinished proposals')
        records[rel] = compare(before, after)
    result = {'created_utc': datetime.now(timezone.utc).isoformat(),
              'baseline_commit': manifest['baseline_commit'],
              'baseline_manifest': str(args.manifest), 'baseline_manifest_sha256': digest(args.manifest.read_bytes()),
              'baseline_includes_author_uncommitted_introduction_edit': True,
              'target_root': str(args.baseline_root if args.baseline_only else args.target_root),
              'scope': 'Sixteen frozen editorial source files: all chapter files, four supplement chapter files, and bilingual abstract. Counts include prose, headings and captions within those files; external generated tables, other frontmatter and bibliography are outside this word-count denominator.',
              'word_count_command': 'texcount -utf8 -brief -sum='+WEIGHTS+' FILE',
              'word_count_limitations': 'TeXcount heuristic, consistently weighted; formulas receive zero weight. Neither character counts nor PDF page counts substitute for this prose measure.',
              'semantic_equivalence_certified': False,
              'review_requirement': 'Independent editorial and mathematical review must establish retention of claims, hypotheses, qualifications and proof dependencies; exact structural matching alone is insufficient.',
              'numeric_review_limitations': 'Potential numeric facts exclude math and citation/reference/path/layout arguments. Changes in repetitions or architecture names can be benign; changed inline formulas are reported separately.',
              'fallback_to_baseline_files': fallback, 'totals': totals(records),
              'all_hard_invariants_pass': all(r['hard_invariants_pass'] for r in records.values()),
              'files_needing_manual_review': [p for p,r in records.items() if r['manual_review_needed']],
              'files': records}
    if args.baseline_only: result['baseline_inventory'] = inventory_rows
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+'\n')
    print(json.dumps({k:result[k] for k in ('totals','all_hard_invariants_pass','files_needing_manual_review','fallback_to_baseline_files')},indent=2))
    print('Wrote', args.output)
    if args.fail_on_invariant_change and not result['all_hard_invariants_pass']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
