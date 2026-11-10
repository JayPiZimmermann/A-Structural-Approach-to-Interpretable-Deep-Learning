#!/usr/bin/env python3
"""Synchronize active theorem badges without rewriting the pinned proof map.

Only recursive inputs of tex/main.tex are active. Editorial AliasLabel commands
can account for deduplicated statements, while their distinct Lean declarations
must retain physical links. Scope and formalization status remain those of the
reviewed, immutable formalization/tex_links.json snapshot.
"""
import argparse
import json
import re
from pathlib import Path
from tex_lean_inventory import active_tex_sources, retired_labels, published_link_details
from check_paper_references import strip_comments

ROOT = Path(__file__).resolve().parents[1]
PATTERN = r'\\begin\{(theorem(?:env)?|lemma(?:env)?|proposition(?:env)?|corollary(?:env)?|definition(?:env)?|claim|remark|observation)\}(.*?)\\end\{\1\}'


def add_title_badge(body, key):
    if body.startswith('['):
        depth, brace_depth, end = 1, 0, 1
        while end < len(body) and depth:
            char = body[end]
            if char == '{' and body[end-1] != '\\': brace_depth += 1
            elif char == '}' and body[end-1] != '\\': brace_depth -= 1
            elif not brace_depth and char == '[': depth += 1
            elif not brace_depth and char == ']': depth -= 1
            end += 1
        if depth: raise ValueError('Unclosed theorem title: ' + key)
        title = body[1:end-1].rstrip()
        return '[' + title + (', ' if title else '') + '\\LeanResult{' + key + '}]' + body[end:]
    return '[\\LeanResult{' + key + '}]' + body


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    config_path = ROOT/'formalization/tex_links.json'
    frozen_config = config_path.read_bytes()
    config = json.loads(frozen_config)
    retired = retired_labels(config)
    changed = []
    for path in active_tex_sources():
        original = path.read_text()
        def annotate(match):
            env, body = match.group(1), match.group(2)
            active = strip_comments(body)
            existing = re.findall(r'\\(?:LeanResult|leandecl)\{([^}]+)\}', active)
            unknown = set(existing) - set(config)
            if unknown: raise ValueError('Unmapped Lean badges: ' + str(sorted(unknown)))
            # Keep explicitly retained additional proof links on merged results.
            # Their count/scope is reviewed independently; the synchronizer must
            # not delete them by assuming a theorem has only one original label.
            if existing:
                return match[0]
            labels = re.findall(r'\\label\{([^}]+)\}', active)
            eligible = [key for key in labels if key in config and key not in retired
                        and not config[key].get('equation')]
            if eligible:
                body = add_title_badge(body, eligible[0])
            return '\\begin{' + env + '}' + body + '\\end{' + env + '}'
        result = re.sub(PATTERN, annotate, original, flags=re.S)
        if result != original:
            changed.append(str(path.relative_to(ROOT)))
            if not args.check:
                path.write_text(result)
    if config_path.read_bytes() != frozen_config:
        raise RuntimeError('Pinned Lean map changed during badge synchronization')
    if args.check and changed:
        raise SystemExit('Missing Lean badges in active thesis: ' + ', '.join(changed))
    details = published_link_details(config)
    print(f'Lean badges current: {sum(details["uses"].values())} physical links, '
          f'{len(details["alias_coverage"])} deduplicated mappings; pinned map unchanged'
          if args.check else f'{len(changed)} files updated; pinned map unchanged')


if __name__ == '__main__':
    main()
