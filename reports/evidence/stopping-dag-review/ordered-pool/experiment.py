#!/usr/bin/env python3
"""Exhaustive finite ordered-pool adapter audit, Python standard library only."""
from itertools import product
from pathlib import Path
from random import Random
import hashlib,json
HERE=Path(__file__).resolve().parent;SEED=20261109;rng=Random(SEED)
cases=[];failures=[];counts={'pools':0,'ties_for_maximum':0,'unique_max_with_losing_ties':0,'permuted_or_repeated_inputs':0}
def compile_pool(inputs):
 if len(inputs)==1:return ('i',inputs[0])
 return ('max',compile_pool(inputs[1:]),('i',inputs[0]))
def run(e,pairs):
 if e[0]=='i':return pairs[e[1]],e[1],True
 a,i,ra=run(e[1],pairs);b,j,rb=run(e[2],pairs);va,vb=a[0]-a[1],b[0]-b[1]
 return (a,i,ra and va!=vb) if va>vb else (b,j,rb and va!=vb)
def trial(vals,inputs):
 pairs=[(v+2+j,2+j) for j,v in enumerate(vals)]
 selected=[vals[i] for i in inputs];winner=min(j for j,v in enumerate(selected) if v==max(selected))
 actual_pair,actual_node,regular=run(compile_pool(inputs),pairs)
 if actual_pair!=pairs[inputs[winner]] or actual_node!=inputs[winner]:failures.append({'values':vals,'inputs':inputs})
 unique=selected.count(max(selected))==1
 if unique and not regular:failures.append({'unique_regular_failure':selected})
 counts['pools']+=1;counts['ties_for_maximum']+=int(not unique)
 counts['unique_max_with_losing_ties']+=int(unique and len(set(selected))<len(selected))
 counts['permuted_or_repeated_inputs']+=int(inputs!=sorted(set(inputs)))
 cases.append({'values':vals,'inputs':inputs,'winner_operand_position':winner,'actual_graph_node':actual_node})
for width in range(1,7):
 for vals in product([-1,0,1],repeat=width):trial(list(vals),list(range(width)))
for _ in range(250):
 n=rng.randrange(1,6);trial([rng.randrange(-2,3) for _ in range(n)],[rng.randrange(n) for _ in range(rng.randrange(1,8))])
raw=(json.dumps(cases,indent=2,sort_keys=True)+'\n').encode();(HERE/'experiment-cases.json').write_bytes(raw)
r={'seed':SEED,'counts':counts,'failures':failures,'cases_sha256':hashlib.sha256(raw).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Source min-operand-index tie choice equals actual recursively compiled right-tie syntax; unique winners remain regular despite tied losing tails. Unsorted enumeration deliberately means operand position, not node index.'}
(HERE/'experiment-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));assert not failures
