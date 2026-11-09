#!/usr/bin/env python3
"""Synchronize thesis badges with the manually reviewed coverage map.

This does not establish coverage: it uses the explicit scope/status assigned by
mathematical review. The Lean audit verifies that the referenced declarations exist.
Equation mappings in tex_links.json are preserved.
"""
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PATTERN = r'\\begin\{(theorem(?:env)?|lemma(?:env)?|proposition(?:env)?|corollary(?:env)?|definition(?:env)?|claim|remark|observation)\}(.*?)\\end\{\1\}'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    coverage=json.loads((ROOT/'formalization/coverage_map.json').read_text())
    config=ROOT/'formalization/tex_links.json'
    previous=json.loads(config.read_text()) if config.exists() else {}
    links={k:v for k,v in previous.items() if v.get('equation')}
    changed=[]
    for path in sorted((ROOT/'tex/chapters').glob('*.tex')):
        original=path.read_text()
        def annotate(match):
            env,body=match.group(1),match.group(2)
            body=re.sub(r'\n\\hfill\\LeanResult\{[^}]+\}\s*$', '', body)
            # Older links were trailing badges; the paper uses the optional
            # theorem heading, next to its title, for numbered Lean references.
            body=re.sub(r',?\s*\\LeanResult\{[^}]+\}', '', body)
            label=re.search(r'\\label\{([^}]+)\}',body)
            claim=coverage.get(label[1].removeprefix('ptnb:')) if label else None
            reviewed=previous.get(label[1],{}) if label else {}
            if reviewed.get('review_id') or (claim and claim.get('lean')):
                key=label[1]
                if reviewed.get('review_id'):
                    links[key]=reviewed
                else:
                    display='Lean variant' if claim['status']=='formalized_variant' else 'Lean components'
                    links[key]={'declaration':claim['lean'][0],'display':display,'scope':claim['scope']}
                if body.startswith('['):
                    depth=1; brace_depth=0; end=1
                    while end<len(body) and depth:
                        char=body[end]
                        if char=='{' and body[end-1]!='\\':brace_depth+=1
                        elif char=='}' and body[end-1]!='\\':brace_depth-=1
                        elif not brace_depth and char=='[':depth+=1
                        elif not brace_depth and char==']':depth-=1
                        end+=1
                    if depth:raise ValueError('Unclosed theorem title: '+key)
                    title=body[1:end-1].rstrip()
                    body='['+title+(', ' if title else '')+'\\LeanResult{'+key+'}]'+body[end:]
                else:
                    body='[\\LeanResult{'+key+'}]'+body
            return '\\begin{'+env+'}'+body+'\\end{'+env+'}'
        result=re.sub(PATTERN,annotate,original,flags=re.S)
        if result!=original:
            changed.append(str(path.relative_to(ROOT)))
            if not args.check:path.write_text(result)
    result=json.dumps(links,indent=2)+'\n'
    if not config.exists() or config.read_text()!=result:
        changed.append(str(config.relative_to(ROOT)))
        if not args.check:config.write_text(result)
    if args.check and changed:raise SystemExit('Stale Lean badges/config: '+', '.join(changed))
    print(f'{len(links)} mapped statement/equation links; {len(changed)} files updated' if not args.check else 'Lean badges and config are current')

if __name__=='__main__':main()
