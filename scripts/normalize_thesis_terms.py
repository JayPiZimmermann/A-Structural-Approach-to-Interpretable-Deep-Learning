#!/usr/bin/env python3
"""Normalize terminology without paraphrasing sentences or editing identifiers.

Official bibliography entries and archived papers are excluded. TeX reference,
URL, code and file arguments, comments, and attributed quotes are protected.
"""
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORDS = {
    'artefact': 'artifact', 'artefacts': 'artifacts', 'organises': 'organizes',
    'characterisation': 'characterization', 'labelled': 'labeled', 'flavoured': 'flavored',
    'towards': 'toward', 'sub-networks': 'subnetworks', 'nonnegative': 'non-negative',
    'nondecreasing': 'non-decreasing', 'preactivation': 'pre-activation',
    'preactivations': 'pre-activations', 'feed-forward': 'feedforward',
    'layerwise': 'layer-wise', 'Layerwise': 'Layer-wise',
    'VGG16': 'VGG-16', 'ResNet18': 'ResNet-18', 'ResNet50': 'ResNet-50',
    'PASCAL VOC': 'Pascal VOC', 'GeLU': 'GELU',
    'DeepLift': 'DeepLIFT', 'GradientShap': 'GradientSHAP', 'Gradient SHAP': 'GradientSHAP',
    'layercam': 'LayerCAM', 'GradCAM': 'Grad-CAM', 'KShap': 'KernelSHAP',
    'winner-take-all': 'winner-takes-it-all', 'winner-takes-all': 'winner-takes-it-all',
    'post-hoc': 'post hoc',
}
PATTERN = re.compile(r'(?<![\w/])(' + '|'.join(re.escape(k) for k in sorted(WORDS,key=len,reverse=True)) + r')(?![\w/])')
PROTECTED = re.compile(r'\\(?:label|ref|eqref|cref|Cref|autoref|pageref|cite\w*|parencite|textcite|nocite|url|path|texttt|lstinline|input|include|includegraphics|LeanResult|DeclareLeanResult|DeclareLeanEquation)(?:\[[^\]]*\])?\s*\{|\\href\s*\{')


def protected_ranges(text):
    spans = []
    for m in re.finditer(r'(?<!\\)%[^\n]*|\\begin\{quote\}[\s\S]*?\\end\{quote\}', text):
        spans.append(m.span())
    for m in PROTECTED.finditer(text):
        i=m.end(); depth=1
        while i<len(text) and depth:
            if text[i] in '{}' and (i==0 or text[i-1]!='\\'):
                depth += 1 if text[i]=='{' else -1
            i+=1
        spans.append((m.start(),i))
    return spans


def normalize(text):
    spans=protected_ranges(text); edits=[]
    def sub(m):
        if any(a<=m.start()<b for a,b in spans):return m[0]
        edits.append({'line':text.count('\n',0,m.start())+1,'old':m[0],'new':WORDS[m[0]]})
        return WORDS[m[0]]
    return PATTERN.sub(sub,text),edits


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    paths=[p for folder in ['chapters','appendices','frontmatter','figures','tables'] for p in (ROOT/'tex'/folder).rglob('*.tex')]
    paths += [ROOT/'tex/preamble/paper_v2.tex',ROOT/'tex/preamble/abbreviations_def.tex']
    report={}
    for p in sorted(set(paths)):
        text=p.read_text();updated,edits=normalize(text)
        if edits:
            report[str(p.relative_to(ROOT))]=edits
            if not args.check:p.write_text(updated)
    if not args.check:
        (ROOT/'reports/terminology-normalization.json').write_text(json.dumps({'policy':WORDS,'edits':report},indent=2)+'\n')
    print(f'{sum(map(len,report.values()))} terminology replacements in {len(report)} files')
    if args.check and report:raise SystemExit(1)

if __name__=='__main__':main()
