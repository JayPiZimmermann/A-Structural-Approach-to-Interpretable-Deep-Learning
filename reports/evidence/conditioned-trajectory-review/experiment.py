"""Independent finite path enumeration. Python standard library only; exact rational kernels."""
from fractions import Fraction as Q
from itertools import product
from math import sqrt
from pathlib import Path
import random,json,hashlib
OUT=Path(__file__).resolve().parent
SEED=1132026;rng=random.Random(SEED)
counts=dict(pairs=0,positive_pairs=0,zero_starts=0,paths=0,marginals=0,geometric_edges=0,completed_prefix_checks=0)

def laws(K,s,N):
 d=len(K[0]); ans={}
 for path in product(range(d),repeat=N):
  p=Q(1);u=s
  for i,v in enumerate(path):p*=K[i][u][v];u=v
  ans[path]=p
 return ans

def potential(K,N):
 d=len(K[0]);h=[[Q(1)]*d for _ in range(N+1)]
 for i in reversed(range(N)):
  h[i]=[sum((K[i][u][v]*h[i+1][v] for v in range(d)),Q(0)) for u in range(d)]
 return h

def conditioned(K,N,h):
 return [[[K[i][u][v]*h[i+1][v]/h[i][u] if h[i][u] else Q(0) for v in range(len(K[0]))] for u in range(len(K[0]))] for i in range(N)] or K

def complete(K):
 d=len(K[0]);return [[row+[1-sum(row)] for row in layer]+[[Q(0)]*d+[Q(1)]] for layer in K]

def bc(p,q):return sum(sqrt(float(v*q[k])) for k,v in p.items())
def h2(p,q):return sum((sqrt(float(v))-sqrt(float(q[k])))**2 for k,v in p.items())/2

def approx(a,b):assert abs(float(a)-float(b))<2e-12,(a,b)

def randomK(d,N):
 def row():
  weights=[rng.randrange(5) for _ in range(d+1)]
  if not sum(weights):return [Q(0)]*d
  return [Q(w,sum(weights)) for w in weights[:-1]]
 return [[row() for _ in range(d)] for _ in range(max(1,N))]

cases=[]
# Nontrivial conditioned overlap: probabilities (1/5,4/5) vs (4/5,1/5),
# differing positive initial survival and reachable zero-survival state.
A=[[[Q(1,2),Q(1,2)]]*2,[[Q(1,10),Q(2,5)],[Q(0),Q(0)]]]
B=[[[Q(3,4),Q(1,4)]]*2,[[Q(4,5),Q(1,5)],[Q(0),Q(0)]]]
cases.append((2,A,B,0))
for _ in range(160):
 d=rng.randrange(1,4);N=rng.randrange(5)
 cases.append((N,randomK(d,N),randomK(d,N),rng.randrange(d)))
serialized=[]
for N,A,B,s in cases:
 counts['pairs']+=1;d=len(A[0]);hA=potential(A,N);hB=potential(B,N)
 CA=conditioned(A,N,hA);CB=conditioned(B,N,hB)
 p= laws(A,s,N);q=laws(B,s,N);cp=laws(CA,s,N);cq=laws(CB,s,N)
 counts['paths']+=len(p);assert sum(p.values())==hA[0][s] and sum(q.values())==hB[0][s]
 for K,h,C,plain,cond in [(A,hA,CA,p,cp),(B,hB,CB,q,cq)]:
  # Full sum marginal independently compared to prefix sum and dynamic survival.
  for i in range(N+1):
   prefix=laws(K,s,i)
   for t in range(d):
    before=sum(v for path,v in prefix.items() if (s if i==0 else path[-1])==t)
    full=sum(v for path,v in plain.items() if (s if i==0 else path[i-1])==t)
    actual=sum(v for path,v in cond.items() if (s if i==0 else path[i-1])==t)
    assert full==before*h[i][t];counts['marginals']+=1
    if h[0][s]:assert actual==before*h[i][t]/h[0][s]
  if not h[0][s]:
   counts['zero_starts']+=1;assert all(v==0 for v in plain.values())
  else:
   assert sum(cond.values())==1
   for path,v in cond.items():assert v==plain[path]/h[0][s]
 for i in range(N):
  for u in range(d):
   for v in range(d):
    left=sqrt(float(CA[i][u][v]*CB[i][u][v]));den=sqrt(float(hA[i][u]*hB[i][u]))
    right=sqrt(float(A[i][u][v]*B[i][u][v]))*sqrt(float(hA[i+1][v]*hB[i+1][v]))/den if den else 0
    approx(left,right);counts['geometric_edges']+=1
 if hA[0][s] and hB[0][s]:
  counts['positive_pairs']+=1;norm=bc(p,q)/sqrt(float(hA[0][s]*hB[0][s]))
  approx(bc(cp,cq),norm);approx(h2(cp,cq),1-norm)
  # A separate DP on sqrt edges, compared with literal full path overlap.
  z=[1.]*d
  for i in reversed(range(N)):
   z=[sum(sqrt(float(CA[i][u][v]*CB[i][u][v]))*z[v] for v in range(d)) for u in range(d)]
  approx(z[s],bc(cp,cq))
 # Actual complete cemetery paths are normalized and BC decreases with depth.
 fullA=complete(A);fullB=complete(B);previous=1.;previousH=0.
 for n in range(N+1):
  fp=laws(fullA,s,n);fq=laws(fullB,s,n);assert sum(fp.values())==sum(fq.values())==1
  curr=bc(fp,fq);currH=h2(fp,fq);approx(currH,1-curr)
  assert -2e-12<=curr<=previous+2e-12 and currH>=previousH-2e-12
  previous=curr;previousH=currH;counts['completed_prefix_checks']+=1
 serialized.append({'N':N,'start':s,'A':[[[str(x) for x in row]for row in layer]for layer in A],'B':[[[str(x) for x in row]for row in layer]for layer in B]})
(OUT/'experiment-cases.json').write_text(json.dumps(serialized,indent=2)+'\n')
# Negative control: horizon-dependent survival conditioning need not preserve
# the common-prefix-law consistency required by trajectory_bc_monotone.
# At horizon 1 disjoint-ish prefixes; killing the disagreement at horizon 2 raises BC.
A=[[[Q(1,4),Q(3,4)]]*2,[[Q(1),Q(0)],[Q(0),Q(0)]]]
B=[[[Q(3,4),Q(1,4)]]*2,[[Q(1),Q(0)],[Q(0),Q(0)]]]
short=bc(laws(conditioned(A,1,potential(A,1)),0,1),laws(conditioned(B,1,potential(B,1)),0,1))
long=bc(laws(conditioned(A,2,potential(A,2)),0,2),laws(conditioned(B,2,potential(B,2)),0,2))
assert short<long
out={'status':'pass','seed':SEED,'counts':counts,'negative_control':{'different_horizon_conditioning_BC':[short,long],'interpretation':'No monotonicity is claimed across different horizon-dependent conditioning transforms.'},'cases_sha256':hashlib.sha256((OUT/'experiment-cases.json').read_bytes()).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(OUT/'experiment-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
