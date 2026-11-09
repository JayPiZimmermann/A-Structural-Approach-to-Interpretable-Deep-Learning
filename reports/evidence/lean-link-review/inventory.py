#!/usr/bin/env python3
"""Read-only active TeX/contract snapshot for the independent link audit."""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent

def clean(text):
 return re.sub(r'(?<!\\)%[^\n]*',lambda m:' '*len(m[0]),text)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=[]; missing=[]
def visit(p):
 if p in files:return
 if not p.is_file():missing.append(str(p.relative_to(ROOT)));return
 files.append(p)
 for m in re.finditer(r'\\(?:input|include)\{([^{}]+)\}',clean(p.read_text())):
  name=m[1]
  if '\\' in name:continue
  q=ROOT/'tex'/name
  if not q.suffix:q=q.with_suffix('.tex')
  if not q.exists():q=p.parent/name; q=q if q.suffix else q.with_suffix('.tex')
  visit(q)
visit(ROOT/'tex/chapters/00_text.tex')
statement_envs={'theorem','theoremenv','lemma','lemmaenv','proposition','corollary','claim','observation','remark','definition'}
equation_envs={'equation','align','gather','multline','flalign','alignat'}
records=[]
for p in files:
 text=clean(p.read_text());stack=[]
 for m in re.finditer(r'\\(begin|end)\{([^{}]+)\}',text):
  kind,env=m[1],m[2]
  if kind=='begin':stack.append((env,m.start(),m.end()))
  elif stack and stack[-1][0]==env:
   env,start,end=stack.pop()
   if env not in statement_envs|equation_envs:continue
   block=text[start:m.end()]
   labels=re.findall(r'\\label\{([^{}]+)\}',block)
   if env in statement_envs:
    # Equation labels nested inside theorem are not theorem aliases.
    head=block[:re.search(r'\\begin\{(?:equation|align|gather|multline|flalign|alignat)',block).start()] if re.search(r'\\begin\{(?:equation|align|gather|multline|flalign|alignat)',block) else block
    labels=re.findall(r'\\label\{([^{}]+)\}',head)
   records.append({'file':str(p.relative_to(ROOT)),'line':text[:start].count('\n')+1,'environment':env,'kind':'statement' if env in statement_envs else 'equation','labels':labels,'text':block})
records.sort(key=lambda r:(files.index(ROOT/r['file']),r['line']))
contracts={}; sources=['formalization/verification.json','reports/softplus-game-expected-types.json','reports/conditioned-survival-expected-types.json','reports/attention-reference-expected-types.json']
for name in sources:
 for t in json.loads((ROOT/name).read_text())['targets']:
  contracts[t['declaration']]={**t,'contract_manifest':name}
links=json.loads((ROOT/'formalization/tex_links.json').read_text())
data={'active_files':[str(p.relative_to(ROOT)) for p in files],'missing_inputs':missing,'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'contract_manifests':{s:sha(ROOT/s) for s in sources},'links_sha256':sha(ROOT/'formalization/tex_links.json'),'records':records,'contracts':contracts,'links':links}
(OUT/'inventory.json').write_text(json.dumps(data,indent=2)+'\n')
for category in ['statement','equation']:
 (OUT/(category+'s.txt')).write_text('\n\n'.join(f"{i} {r['file']}:{r['line']} {r['environment']} {r['labels']} {'LINKED' if any(l in links for l in r['labels']) else 'MISSING'}\n{r['text']}" for i,r in enumerate(records) if r['kind']==category)+'\n')
print('files',len(files),'statements',sum(r['kind']=='statement' for r in records),'equations',sum(r['kind']=='equation' for r in records),'contracts',len(contracts),'links',len(links),'missing_inputs',missing)
print('equations with labels',sum(bool(r['labels']) for r in records if r['kind']=='equation'))
