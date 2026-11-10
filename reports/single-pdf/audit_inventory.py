#!/usr/bin/env python3
"""Compare the former two-document content union with one active thesis root.

Logical claims and assets need reviewed dispositions when removed or merged.
Formula rewrites are review flags, not automatic semantic failures. This audit
never treats mathematical equivalence as established by string similarity.
"""
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'scripts'))
from check_paper_references import strip_comments, tex_closure, citation_keys, balanced_group
from tex_lean_inventory import source_label_inventory
BASELINE = Path('/home/jzimmermann/.cache/thesis-single-pdf/2026-11-10/baseline')
ENV = r'(equation\*?|align\*?|gather\*?|multline\*?|displaymath|eqnarray\*?|flalign\*?|alignat\*?)'
DISPLAY = re.compile(r'\\begin\{' + ENV + r'\}(.*?)\\end\{\1\}|(?<!\\)\\\[(.*?)(?<!\\)\\\]', re.S)
CLAIM = re.compile(r'\\begin\{(theorem(?:env)?|lemma(?:env)?|proposition|corollary|definition|observation|remark)\}(.*?)\\end\{\1\}', re.S)
COMMAND = re.compile(r'\\(includegraphics|input|include|appinputgen|appinputgenlt|appinputgenci|appfitgen|caption|chapter|section|subsection|subsubsection|paragraph)\*?(?:\s*\[[^]]*\])*\s*\{')
LABEL = re.compile(r'\\label\s*\{([^}]+)\}')
BADGE = re.compile(r'\\(?:LeanResult|leandecl)\s*\{([^}]+)\}')
ALIAS = re.compile(r'\\AliasLabel\s*\{([^}]+)\}\s*\{([^}]+)\}')


def norm(s): return re.sub(r'\s+', ' ', s).strip()
def sha(s): return hashlib.sha256(s.encode() if isinstance(s,str) else s).hexdigest()
def relative(path, root): return str(path.relative_to(root))


def collect(root, roots):
    files, unresolved = [], []
    for texroot in roots:
        found, missing = tex_closure(root/texroot, root/'tex')
        files.extend(p for p in found if p not in files); unresolved.extend(missing)
    labels, claims, displays, citations, assets, table_inputs = defaultdict(list), [], [], set(), defaultdict(list), defaultdict(list)
    headings, aliases, badges, source_hashes = [], {}, Counter(), {}
    for path in files:
        name = relative(path,root); raw = path.read_text(); text = strip_comments(raw)
        source_hashes[name] = sha(raw)
        # Generated declarations and macro definitions are not document content.
        if name.startswith('tex/preamble/') or name.endswith('.sty'): continue
        citations.update(citation_keys(text))
        for match in LABEL.finditer(text):
            if '#' not in match[1]: labels[match[1]].append({'file':name,'line':text.count('\n',0,match.start())+1})
        badges.update(key for key in BADGE.findall(text) if '#' not in key)
        for alias,target in ALIAS.findall(text):
            if '#' not in alias: aliases[alias]=target
        for match in CLAIM.finditer(text):
            keys=LABEL.findall(match[2])
            claims.append({'environment':match[1],'labels':keys,'file':name,
                           'payload_sha256':sha(norm(match[2]))})
        for match in DISPLAY.finditer(text):
            payload=match[2] if match[1] else match[3]
            # Labels are identity anchors, not part of the mathematical payload.
            displays.append({'labels':LABEL.findall(payload),'file':name,
                             'payload_sha256':sha(norm(LABEL.sub('',payload)))})
        for match in COMMAND.finditer(text):
            argument,end=balanced_group(text,match.end()-1)
            if argument is None: raise ValueError('Unclosed argument '+name)
            command=match[1]
            if command=='includegraphics': assets[norm(argument)].append(name)
            elif command in {'input','include','appinputgen','appinputgenlt','appinputgenci','appfitgen'}:
                if command.startswith(('appinput','appfit')) or 'table' in argument: table_inputs[command+':'+norm(argument)].append(name)
            elif command!='caption': headings.append({'level':command,'title':norm(argument),'file':name})
    return {'roots':roots,'active_files':[relative(p,root) for p in files],
            'unresolved_includes':unresolved,'source_sha256':source_hashes,
            'labels':dict(labels),'label_aliases':aliases,'citation_keys':sorted(citations),
            'lean_badges':dict(badges),'mathematical_claims':claims,'display_math':displays,
            'figure_assets':dict(assets),'table_inputs':dict(table_inputs),'headings':headings}


def resolve(alias, labels, aliases):
    seen=set()
    while alias in aliases:
        if alias in seen: return None
        seen.add(alias); alias=aliases[alias]
    return alias if alias in labels else None


def claims_by_label(inventory,kind):
    return {label:record for record in inventory[kind] for label in record['labels']}


def compare(old,new,ledger):
    missing_labels=[];aliased=[]
    for label in old['labels']:
        if label in new['labels']: continue
        canonical=resolve(label,new['labels'],new['label_aliases'])
        if canonical: aliased.append({'label':label,'canonical':canonical})
        else:missing_labels.append(label)
    missing_cites=sorted(set(old['citation_keys'])-set(new['citation_keys']))
    missing_assets=sorted(set(old['figure_assets'])-set(new['figure_assets']))
    missing_tables=sorted(set(old['table_inputs'])-set(new['table_inputs']))
    dispositions=ledger.get('dispositions',[])
    by_key={(r.get('kind'),r.get('key')):r for r in dispositions}
    unresolved=[]; reviewed=[]
    for kind,keys in [('label',missing_labels),('citation',missing_cites),('figure_asset',missing_assets),('table_input',missing_tables)]:
        for key in keys:
            review=by_key.get((kind,key),{})
            valid=bool(review.get('reason') and review.get('reviewed_by') and review.get('preserved_at'))
            if valid:
                locations=review['preserved_at'];locations=[locations] if isinstance(locations,str) else locations
                valid=all(x in new['labels'] or x in new['label_aliases'] or x in new['figure_assets'] or x in new['table_inputs'] or x in new['active_files'] for x in locations)
            (reviewed if valid else unresolved).append({'kind':kind,'key':key,'review':review if valid else None})
    # Resolve original claim labels through aliases, then check that every old
    # statement reaches a canonical statement rather than merely an unrelated
    # equation or heading elsewhere in the document.
    statement_index = {}
    for index, claim in enumerate(new['mathematical_claims']):
        for label in claim['labels']: statement_index[label] = index
    crosswalk = []
    statement_reviews = {row.get('key'): row for row in ledger.get('statement_dispositions', [])}
    for old_claim in old['mathematical_claims']:
        canonical = {resolve(label,new['labels'],new['label_aliases']) for label in old_claim['labels']}
        matches = sorted({statement_index[label] for label in canonical if label in statement_index})
        row = {'baseline_environment':old_claim['environment'], 'baseline_labels':old_claim['labels'],
                          'baseline_file':old_claim['file'], 'canonical_indices':matches,
                          'primary_statement_index':statement_index.get(resolve(old_claim['labels'][0], new['labels'], new['label_aliases'])) if old_claim['labels'] else None,
                          'canonical_labels':[new['mathematical_claims'][i]['labels'] for i in matches]}
        # A theorem can retain its statement while a repeated construction is
        # moved to an earlier corollary. Require an explicit reviewed crosswalk
        # identifying every destination instead of silently accepting the split.
        if len(matches) != 1:
            review = statement_reviews.get(next(iter(old_claim['labels']), None), {})
            targets = review.get('canonical_statement_labels', [])
            expected = {statement_index.get(resolve(label, new['labels'], new['label_aliases'])) for label in targets}
            if (review.get('reason') and review.get('reviewed_by') and targets
                    and None not in expected and expected == set(matches)
                    and review.get('baseline_labels') == old_claim['labels']):
                row['reviewed_split'] = review
        crosswalk.append(row)
    unresolved_claims = [row for row in crosswalk if row['primary_statement_index'] is None
                         or (len(row['canonical_indices']) != 1 and not row.get('reviewed_split'))]
    changed={}
    for kind in ['mathematical_claims','display_math']:
        before,after=claims_by_label(old,kind),claims_by_label(new,kind)
        changed[kind]=[{'label':key,'old_file':record['file'],'new_file':after[key]['file'],
                        'before_sha256':record['payload_sha256'],'after_sha256':after[key]['payload_sha256']}
                       for key,record in before.items() if key in after and record['payload_sha256']!=after[key]['payload_sha256']]
    return {'missing_labels':sorted(missing_labels),'alias_resolutions':aliased,
            'missing_citation_keys':missing_cites,'missing_figure_assets':missing_assets,
            'missing_table_inputs':missing_tables,'reviewed_deduplications':reviewed,
            'statement_crosswalk':crosswalk,'unresolved_statement_crosswalk':unresolved_claims,
            'unresolved_unique_content_dispositions':unresolved,'changed_claims_for_review':changed,
            'duplicate_active_labels':{k:v for k,v in new['labels'].items() if len(v)>1},
            'invalid_aliases':{k:v for k,v in new['label_aliases'].items() if resolve(k,new['labels'],new['label_aliases']) is None},
            'baseline_counts':{key:len(old[key]) for key in ['labels','citation_keys','mathematical_claims','display_math','figure_assets','table_inputs']},
            'candidate_counts':{key:len(new[key]) for key in ['labels','citation_keys','mathematical_claims','display_math','figure_assets','table_inputs']}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-root',type=Path,default=BASELINE)
    parser.add_argument('--candidate-root',type=Path,default=ROOT)
    parser.add_argument('--output-dir',type=Path,default=ROOT/'reports/single-pdf')
    parser.add_argument('--ledger',type=Path,default=ROOT/'reports/single-pdf/content-retention-ledger.json')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args();out=args.output_dir;out.mkdir(parents=True,exist_ok=True)
    old=collect(args.baseline_root,['tex/main.tex','tex/supplement.tex'])
    new=collect(args.candidate_root,['tex/main.tex'])
    old['baseline_commit']='b43bc24f3aa0cf715979ce30024d0ee4434d6fe5'
    new['publication_mode']='single_pdf'
    (out/'inventory-baseline.json').write_text(json.dumps(old,indent=2,ensure_ascii=False)+'\n')
    (out/'inventory-candidate.json').write_text(json.dumps(new,indent=2,ensure_ascii=False)+'\n')
    ledger=json.loads(args.ledger.read_text()) if args.ledger.exists() else {}
    report=compare(old,new,ledger)
    report.update({'created_utc':datetime.now(timezone.utc).isoformat(),'baseline_commit':old['baseline_commit'],
                   'semantic_equivalence_certified':False,
                   'scope':'Old main+supplement union against recursive main.tex closure; equation simplifications are reviewed, not rejected by byte equality.',
                   'parser_coverage_note':'Includes appfitgen table wrappers; the earlier incomplete baseline inventory is retained in inventory-baseline-before-appfitgen.json.',
                   'baseline_inventory':'inventory-baseline.json','candidate_inventory':'inventory-candidate.json',
                   'retention_ledger':str(args.ledger),'unresolved_includes':new['unresolved_includes']})
    passed=not any(report[k] for k in ['unresolved_unique_content_dispositions','unresolved_statement_crosswalk','duplicate_active_labels','invalid_aliases','unresolved_includes'])
    report['mechanical_retention_pass']=passed
    (out/'inventory-comparison.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({k:report[k] for k in ['baseline_counts','candidate_counts','missing_citation_keys','missing_figure_assets','missing_table_inputs','mechanical_retention_pass']},indent=2))
    print('Unresolved dispositions:',len(report['unresolved_unique_content_dispositions']))
    if args.check and not passed:raise SystemExit(1)

if __name__=='__main__':main()
