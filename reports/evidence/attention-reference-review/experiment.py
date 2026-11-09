#!/usr/bin/env python3
"""Finite reference-KL support and uniqueness audit; standard library only.
Exact fractions determine support, policies and optimizer; Decimal(60) checks
independently evaluated logarithmic objective and strict gap numerically.
"""
from fractions import Fraction as Q
from decimal import Decimal as D,getcontext
from random import Random
from pathlib import Path
import json,hashlib
getcontext().prec=60
HERE=Path(__file__).resolve().parent;SEED=20261109;rng=Random(SEED);TOL=D('1e-48')
counts={k:0 for k in ['problems','positive_total','zero_total','policies','unsupported','supported_nonoptimal','boundary_optimizers','objective_bridges','strict_gaps']};failures=[];cases=[]
def dec(q):return D(q.numerator)/D(q.denominator)
def ln(q):return dec(q).ln()
def partitions(total,n):
 if n==1:yield [total]
 else:
  for i in range(total+1):
   for p in partitions(total-i,n-1):yield [i]+p

def objective(r,c,p):
 if any(w>0 and (a==0 or b==0) for a,b,w in zip(r,c,p)):return None
 return sum((dec(w)*ln(b) for b,w in zip(c,p) if w),D(0))-sum((dec(w)*(ln(w)-ln(a)) for a,w in zip(r,p) if w),D(0))
def mass_objective(r,c,p):
 mass=[a*b for a,b in zip(r,c)]
 if any(w and not m for w,m in zip(p,mass)):return None
 return sum((dec(w)*ln(m)-dec(w)*ln(w) for w,m in zip(p,mass) if w),D(0))
for case in range(144):
 n=1+case%4;r=[Q(rng.randrange(4)) for _ in range(n)];sr=sum(r)
 if sr and case%7:r=[w/sr for w in r]
 c=[Q(rng.randrange(5),2) for _ in range(n)]
 if case%13==0:c=[Q(0)]*n
 total=sum(a*b for a,b in zip(r,c));counts['problems']+=1;counts['positive_total']+=int(total>0);counts['zero_total']+=int(total==0)
 policies=[[Q(w,6) for w in p] for p in partitions(6,n)]
 if total:
  optimum=[a*b/total for a,b in zip(r,c)];policies.append(optimum);counts['boundary_optimizers']+=int(any(w==0 for w in optimum));value=ln(total)
  if abs(objective(r,c,optimum)-value)>TOL:failures.append(f'optimizer value {case}')
 for p in policies:
  counts['policies']+=1;v=objective(r,c,p);w=mass_objective(r,c,p);counts['objective_bridges']+=1
  if (v is None)!=(w is None) or (v is not None and abs(v-w)>TOL):failures.append(f'bridge {case} {p}')
  if v is None:counts['unsupported']+=1
  if not total:
   if v is not None:failures.append(f'zero total not bottom {case}')
  elif v is not None:
   if v>value+TOL:failures.append(f'bound {case}')
   if p!=optimum:
    counts['supported_nonoptimal']+=1;counts['strict_gaps']+=1
    if not v<value-TOL:failures.append(f'strict gap {case} {p}')
 cases.append({'reference':[str(q) for q in r],'contribution':[str(q) for q in c]})
# Zero reference and zero contribution independently invalidate pure actions.
assert objective([Q(0),Q(1)],[Q(7),Q(1)],[Q(1),Q(0)]) is None
assert objective([Q(1,2),Q(1,2)],[Q(0),Q(2)],[Q(1),Q(0)]) is None
# A wrong real-log-zero replacement would turn either impossible value finite.
raw=(json.dumps(cases,indent=2,sort_keys=True)+'\n').encode();(HERE/'experiment-cases.json').write_bytes(raw)
r={'seed':SEED,'decimal_precision':getcontext().prec,'absolute_log_tolerance':str(TOL),'counts':counts,'failures':failures,'negative_controls':['dropping separate zero-reference support guard','treating log zero as finite real zero','claiming a unique policy when every stream mass vanishes'],'cases_sha256':hashlib.sha256(raw).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Exact support and optimizer ratios with numerical high-precision logarithmic comparisons supplement universal Lean proofs. Only local active-player value optimization is tested.'}
(HERE/'experiment-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));assert not failures
