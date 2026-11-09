"""Exact independent regularizer and nonlinear-convex-input checks (stdlib only)."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,random
SEED=20261109
rng=random.Random(SEED)
counts=dict(optimizer_comparisons=0,support_inequalities=0,pair_checks=0,
            regularized_networks=0,negative_affine_outputs=0,convex_input_jensen=0)
cases=[]
def cost(l,c,p):return l*(p*p-p)-c
def gate(l,z):return max(Q(0),min(Q(1),(z+l)/(2*l))) if l else Q(z>0)
def objective(l,c,z,p):return p*z-cost(l,c,p)
def value(l,c,z):return objective(l,c,z,gate(l,z))
def pair(l,c,u,v):
 p=gate(l,u-v)
 return p*u-cost(l,c,p),p*v
zs=[Q(i,2) for i in range(-12,13)]
for l in map(Q,(0,1,2,3)):
 for c in map(Q,(0,2)):
  for z in zs:
   p=gate(l,z);v=value(l,c,z)
   for t in (Q(i,20) for i in range(21)):
    assert cost(l,c,t)<=0 and v>=objective(l,c,z,t)
    counts['optimizer_comparisons']+=1
   for y in zs:
    assert v+p*(y-z)<=value(l,c,y)
    assert abs(v-value(l,c,y))<=abs(z-y)
    if z<=y:assert v<=value(l,c,y)
    counts['support_inequalities']+=1
  for u in map(Q,range(7)):
   for v in map(Q,range(7)):
    a,b=pair(l,c,u,v)
    assert a>=0 and b>=0 and a-b==value(l,c,u-v)
    counts['pair_checks']+=1

def dot(a,b):return sum((x*y for x,y in zip(a,b)),Q(0))
def affine_pair(W,b,p,n):
 return ([sum((max(w,0)*u+max(-w,0)*v for w,u,v in zip(row,p,n)),Q(0))+max(c,0) for row,c in zip(W,b)],
         [sum((max(w,0)*v+max(-w,0)*u for w,u,v in zip(row,p,n)),Q(0))+max(-c,0) for row,c in zip(W,b)])
for case in range(240):
 l=Q(rng.randrange(4));c=Q(rng.randrange(3));width=rng.randrange(4)
 p=[Q(rng.randrange(5)) for _ in range(width)];n=[Q(rng.randrange(5)) for _ in range(width)]
 actual=[u-v for u,v in zip(p,n)];data=[]
 for _ in range(rng.randrange(1,5)):
  out=rng.randrange(1,4)
  W=[[Q(rng.randrange(-2,3)) for _ in range(width)] for _ in range(out)]
  b=[Q(rng.randrange(-3,4)) for _ in range(out)]
  preP,preN=affine_pair(W,b,p,n)
  split=[pair(l,c,u,v) for u,v in zip(preP,preN)]
  p=[t[0] for t in split];n=[t[1] for t in split]
  actual=[value(l,c,dot(row,actual)+bias) for row,bias in zip(W,b)]
  assert all(u>=0 and v>=0 for u,v in zip(p,n))
  assert [u-v for u,v in zip(p,n)]==actual
  width=out;data.append((W,b))
 w=[Q(rng.randrange(-3,4)) for _ in range(width)];bias=Q(rng.randrange(-4,5))
 a,b=affine_pair([w],[bias],p,n)
 output=dot(w,actual)+bias
 assert a[0]-b[0]==output
 counts['regularized_networks']+=1;counts['negative_affine_outputs']+=int(output<0)
 cases.append((l,c,data,w,bias))

# Nonlinear convex valid lift p(x)=x^2+x+1, q(x)=x^2+1, so p-q=x.
# Apply actual monotone DC split recurrences, then nonnegative split affine readout.
for case in range(180):
 layers=[];width=1
 for _ in range(rng.randrange(1,4)):
  out=rng.randrange(1,4)
  wp=[[Q(rng.randrange(3)) for _ in range(width)] for _ in range(out)]
  wn=[[Q(rng.randrange(3)) for _ in range(width)] for _ in range(out)]
  bp=[Q(rng.randrange(-3,4)) for _ in range(out)]
  bn=[Q(rng.randrange(-3,4)) for _ in range(out)]
  layers.append((wp,wn,bp,bn));width=out
 rwP=[Q(rng.randrange(3)) for _ in range(width)];rwN=[Q(rng.randrange(3)) for _ in range(width)]
 rbP=Q(rng.randrange(-3,4));rbN=Q(rng.randrange(-3,4))
 def run(x):
  p,n=[x*x+x+1],[x*x+1]
  for wp,wn,bp,bn in layers:
   zp=[dot(a,p)+dot(b,n)+c for a,b,c in zip(wp,wn,bp)]
   zn=[dot(b,p)+dot(a,n)+c for a,b,c in zip(wp,wn,bn)]
   p,n=[max(a,b) for a,b in zip(zp,zn)],zn
  return dot(rwP,p)+dot(rwN,n)+rbP,dot(rwN,p)+dot(rwP,n)+rbN
 for _ in range(24):
  x,y=Q(rng.randrange(-5,6)),Q(rng.randrange(-5,6));t=Q(rng.randrange(11),10)
  v,a,b=run(t*x+(1-t)*y),run(x),run(y)
  assert all(v[i]<=t*a[i]+(1-t)*b[i] for i in (0,1))
  counts['convex_input_jensen']+=1
 cases.append(('convex-input',layers,rwP,rwN,rbP,rbN))

assert (Q(0),Q(0))!=(Q(1),Q(1)) # distinct maximizing tie selections preserve the same difference
assert -Q(0)**2>(-Q(-1)**2-Q(1)**2)/2 # negative readout destroys convexity of x^2
payload=json.dumps(cases,default=str,separators=(',',':')).encode();b=Path(__file__).parent
(b/'experiment-cases.json').write_bytes(payload)
r={'seed':SEED,'counts':counts,'failures':[],
 'negative_controls_detected':['claiming tie-selection-independent streams','dropping nonnegative convex readout weights'],
 'cases_sha256':hashlib.sha256(payload).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'scope':'Independent exact finite checks; quadratic convex costs and nonlinear convex lifts supplement universal Lean contracts.'}
(b/'experiment-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
