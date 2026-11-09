#!/usr/bin/env python3
"""Exact finite Doob conditioning audit including dead states and zero starts.
Standard library only; completed cemetery paths are independently enumerated.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from random import Random
import json,hashlib,math
HERE=Path(__file__).resolve().parent;SEED=20261109;rng=Random(SEED)
counts={k:0 for k in ['chains','zero_horizon','starts','positive_starts','zero_starts','zero_potential_states','ordinary_paths','completed_paths','pruned_paths','weighted_generic_checks','normalized_conditioned_laws','marginal_checks']};failures=[];cases=[]
def check(c,s):
 if not c:failures.append(s)
def potential(K,terminal):
 h=[None]*(len(K)+1);h[-1]=list(terminal)
 for i in reversed(range(len(K))):h[i]=[sum((w*h[i+1][t] for t,w in enumerate(row)),Q(0)) for row in K[i]]
 return h
def law(K,s,path):
 p=Q(1)
 for i,t in enumerate(path):p*=K[i][s][t];s=t
 return p
def transform(K,h):return [[[w*h[i+1][t]/h[i][s] if h[i][s]>0 else Q(0) for t,w in enumerate(row)] for s,row in enumerate(mat)] for i,mat in enumerate(K)]
# There is positive original probability of moving into an ordinary state that
# later cannot survive. The transformed law must remove it, not demand h>0 there.
cases.append({'n':2,'K':[[[Q(1,2),Q(1,2)],[Q(0),Q(1)]],[[Q(1),Q(0)],[Q(0),Q(0)]]]})
for c in range(160):
 n=1+c%4;N=c%5;K=[]
 for i in range(N):
  mat=[]
  for s in range(n):
   ws=[rng.randrange(4) if rng.randrange(3) else 0 for _ in range(n)]
   if (c+i+s)%5==0:ws=[0]*n
   den=sum(ws)+rng.randrange(1,5)
   mat.append([Q(w,den) for w in ws])
  K.append(mat)
 cases.append({'n':n,'K':K})
for ci,c in enumerate(cases):
 n,K=c['n'],c['K'];N=len(K);h=potential(K,[Q(1)]*n);T=transform(K,h);counts['chains']+=1;counts['zero_horizon']+=int(N==0)
 counts['zero_potential_states']+=sum(z==0 for layer in h for z in layer)
 for i in range(N):
  for s in range(n):
   check(0<=h[i][s]<=1,f'h bounds {ci} {i} {s}')
   check(sum(T[i][s])==(1 if h[i][s]>0 else 0),f'row {ci} {i} {s}')
   for t in range(n):
    if h[i+1][t]==0:check(T[i][s][t]==0,'zero target')
 completed=[ [list(row)+[1-sum(row)] for row in mat]+[[Q(0)]*n+[Q(1)]] for mat in K]
 generic_h=potential(K,[Q(rng.randrange(4),3) for _ in range(n)]);G=transform(K,generic_h)
 for s in range(n):
  counts['starts']+=1;counts['positive_starts']+=int(h[0][s]>0);counts['zero_starts']+=int(h[0][s]==0)
  base_mass=Q(0);cond_mass=Q(0);base_marg=[[Q(0)]*n for _ in range(N+1)];cond_marg=[[Q(0)]*n for _ in range(N+1)]
  ordinary=list(product(range(n),repeat=N))
  for path in ordinary:
   p=law(K,s,path);q=law(T,s,path);base_mass+=p;cond_mass+=q;counts['ordinary_paths']+=1
   states=[s]+list(path)
   if h[0][s]>0:
    check(q==p/h[0][s],f'quotient {ci} {s} {path}')
    for i,t in enumerate(states):
     cond_marg[i][t]+=q
     if h[i][t]==0:counts['pruned_paths']+=1;check(q==0,f'prune {ci} {s} {path}')
   else:check(p==0,f'zero original {ci} {s} {path}')
   counts['weighted_generic_checks']+=1
   check(law(G,s,path)*generic_h[0][s]==p*generic_h[N][states[-1]],f'weighted generic {ci} {s} {path}')
  check(base_mass==h[0][s],f'survival DP mass {ci} {s}')
  if h[0][s]>0:counts['normalized_conditioned_laws']+=1;check(cond_mass==1,f'conditioned norm {ci} {s}')
  total=Q(0);survives=Q(0)
  for path in product(range(n+1),repeat=N):
   p=law(completed,s,path);total+=p;counts['completed_paths']+=1
   if not path or path[-1]!=n:survives+=p
   for i,t in enumerate([s]+list(path)):
    if t<n:base_marg[i][t]+=p
  check(total==1 and survives==base_mass,f'actual cemetery survival {ci} {s}')
  if h[0][s]>0:
   for i in range(N+1):
    for t in range(n):
     counts['marginal_checks']+=1;check(cond_marg[i][t]==base_marg[i][t]*h[i][t]/h[0][s],f'marginal {ci} {s} {i} {t}')
serial=[{'n':c['n'],'K':[[[str(w) for w in row] for row in mat] for mat in c['K']]} for c in cases]
raw=(json.dumps(serial,indent=2,sort_keys=True)+'\n').encode();(HERE/'experiment-cases.json').write_bytes(raw)
r={'seed':SEED,'counts':counts,'failures':failures,'negative_controls':['reachable dead ordinary state violates global h>0 although initial survival>0','zero-potential transformed row sums to zero, not one','zero initial survival gives no surviving original path and cannot support normalized conditioning'],'cases_sha256':hashlib.sha256(raw).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Exact rational independent completed-cemetery enumeration plus dynamic-program survival. Marginal experiments are supplemental and do not claim a Lean marginal theorem in the reviewed leaf.'}
(HERE/'experiment-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));assert not failures
