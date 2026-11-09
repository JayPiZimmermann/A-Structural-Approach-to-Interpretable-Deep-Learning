#!/usr/bin/env python3
"""Independent finite path enumeration and arbitrary-profile game checks, stdlib only."""
from pathlib import Path
from fractions import Fraction as F
import json,random,math,hashlib
OUT=Path(__file__).resolve().parent;SEED=9171337;rng=random.Random(SEED)
def sp(z,t):return t*(max(z/t,0)+math.log1p(math.exp(-abs(z/t))))
def sig(z,t):return 1/(1+math.exp(-z/t))
def ent(p):return -sum(q*math.log(q) for q in [p,1-p] if q)
def close(a,b,tol=3e-9):assert abs(a-b)<=tol*(1+abs(a)+abs(b)),(a,b)
def val(graph,x,t):
 v=list(map(float,x)); rows=[];pol=[]
 for op in graph:
  n=len(v);typ=op['type'];w=[0.0]*n;b=float(op.get('bias',0));r=1.0
  if typ in ['affine','activation']:
   w=list(map(float,op['weights']));z=sum(a*q for a,q in zip(w,v))+b
   value=sp(z,t) if typ=='activation' else z
   if typ=='activation':r=sig(z,t)
   choice=r
  elif typ=='addition':
   for i in op['inputs']:w[i]+=1
   value=sum(v[i] for i in op['inputs']);choice=None
  else:
   pos=max(range(len(op['inputs'])),key=lambda k:v[op['inputs'][k]])
   w[op['inputs'][pos]]=1;value=v[op['inputs'][pos]]
   choice=[float(i==pos) for i in range(len(op['inputs']))]
  rows.append((w,b,r));pol.append(choice);v.append(value)
 return v,rows,pol
def players(graph,xpair,t,plus,minus):
 # Independently evaluate four actual player/owner payoff coordinates.
 V=[[[float(xpair[p!=turn][i]) for i in range(len(xpair[0]))] for turn in [0,1]] for p in [0,1]]
 for z,op in enumerate(graph):
  out=[[0.0]*2 for _ in [0,1]];typ=op['type']
  for p in [0,1]:
   for turn in [0,1]:
    policy=minus[z] if turn else plus[z]
    if typ in ['affine','activation']:
     b=float(op['bias']);r=policy if typ=='activation' else 1
     a=max(b if p==turn else -b,0)
     for i,w in enumerate(op['weights']):a+=max(float(w),0)*V[p][turn][i]+max(-float(w),0)*V[p][1-turn][i]
     out[p][turn]=r*a+(t*ent(r) if typ=='activation' and p==turn else 0)
    elif typ=='addition':out[p][turn]=sum(V[p][turn][i] for i in op['inputs'])
    else:out[p][turn]=sum(q*V[p][turn][i] for q,i in zip(policy,op['inputs']))
  for p in [0,1]:
   for turn in [0,1]:V[p][turn].append(out[p][turn])
 return V
def paths(rows,d,start,turn,prob=1.,disc=1.,visits=None,rewards=None,t=1.,graph=None):
 visits=[] if visits is None else visits;rewards=[0.,0.] if rewards is None else rewards
 visits=visits+[(start,turn,disc)]
 if start<d:return [(prob,visits,rewards,(start,turn))]
 j=start-d;w,b,r=rows[j];typ=graph[j]['type'];D=sum(abs(a) for a in w)
 pay=[rewards[p]+disc*(r*max(b if p==turn else -b,0)+(t*ent(r) if typ=='activation' and p==turn else 0)) for p in [0,1]]
 ans=[];cem=1 if D==0 else 1-r
 if cem:ans.append((prob*cem,visits,pay,None))
 if D:
  for i,a in enumerate(w):
   if a:ans+=paths(rows,d,i,turn^(a<0),prob*r*abs(a)/D,disc*D,visits,pay,t,graph)
 return ans
cases=[]
# Explicit zero-input negative-bias activation, zero-score gate, ungated negative output,
# reversed tied pool operands, losing-tail tie, repeated addition and skip references.
cases += [dict(x=[],theta=1,graph=[dict(type='activation',weights=[],bias=-2),dict(type='affine',weights=[-3],bias=-5)])]
cases += [dict(x=[0],theta=1,graph=[dict(type='activation',weights=[1],bias=0),dict(type='affine',weights=[0,-2],bias=-5)])]
cases += [dict(x=[4,4,2],theta=1,graph=[dict(type='pool',inputs=[1,0,2]),dict(type='addition',inputs=[3,3]),dict(type='affine',weights=[1,0,0,-2,3],bias=-2)])]
cases += [dict(x=[5,2,2],theta=1,graph=[dict(type='pool',inputs=[0,1,2]),dict(type='activation',weights=[-1,0,0,1],bias=0)])]
for _ in range(96):
 d=rng.randint(1,3);x=[F(rng.randint(-6,6),2) for _ in range(d)];g=[]
 for j in range(6):
  n=d+j;typ=rng.choice(['affine','activation','activation','addition','pool'])
  if typ in ['affine','activation']:
   weights=[F(rng.randint(-3,3),2) if rng.random()<.7 else F(0) for _ in range(n)]
   if rng.random()<.15:weights=[F(0)]*n
   g.append(dict(type=typ,weights=weights,bias=F(rng.randint(-4,4),2)))
  else:g.append(dict(type=typ,inputs=[rng.randrange(n) for _ in range(2 if typ=='addition' else rng.randint(1,3))]))
 cases.append(dict(x=x,theta=rng.choice([.5,1.,2.]),graph=g))
maxfd=0.;npaths=0;nfd=0;saddlechecks=0
for case in cases:
 x=case['x'];g=case['graph'];t=case['theta'];d=len(x);v,rows,canon=val(g,x,t)
 pair=([max(float(q),0) for q in x],[max(-float(q),0) for q in x]);V=players(g,pair,t,canon,canon)
 plus=[];minus=[]
 for op,cp in zip(g,canon):
  if op['type']=='activation':plus.append(rng.randrange(11)/10);minus.append(rng.randrange(11)/10)
  elif op['type']=='pool':
   def dist():
    a=[rng.randrange(5) for _ in op['inputs']];s=sum(a)
    return [q/s for q in a] if s else [1/len(a)]*len(a)
   plus.append(dist());minus.append(dist())
  else:plus.append(None);minus.append(None)
 VA=players(g,pair,t,plus,canon);VB=players(g,pair,t,canon,minus)
 for j in range(d+len(g)):
  for turn in [0,1]:
   expected=(-1 if turn else 1)*v[j]
   close(V[0][turn][j]-V[1][turn][j],expected)
   assert VA[0][turn][j]-VA[1][turn][j]<=expected+1e-8
   assert VB[0][turn][j]-VB[1][turn][j]>=expected-1e-8
   saddlechecks+=2
   pp=paths(rows,d,j,turn,t=t,graph=g);npaths+=len(pp);close(sum(p[0] for p in pp),1)
   for p in [0,1]:
    payoff=0.
    for prob,vis,reward,terminal in pp:
     if terminal:
      i,q=terminal;reward=reward.copy();reward[p]+=vis[-1][2]*pair[p!=q][i]
     payoff+=prob*reward[p]
    close(payoff,V[p][turn][j])
   # Full intermediate visits compared with an independently propagated suffix derivative.
   for target in range(j+1):
    tangent=[0.]*(d+len(g));tangent[target]=1
    for k in range(max(d,target+1),j+1):
     w,b,r=rows[k-d];tangent[k]=r*sum(a*tangent[i] for i,a in enumerate(w))
    signedocc=sum(prob*sum(disc*(1 if q==0 else -1) for node,q,disc in vis if node==target) for prob,vis,reward,end in pp)
    close(tangent[j],(-1 if turn else 1)*signedocc)
  # Numerical gradient checks skip points with tied top pool operands anywhere.
  unique=all(op['type']!='pool' or sum(v[i]==max(v[k] for k in op['inputs']) for i in op['inputs'])==1 for op in g)
  if unique:
   for i in range(d):
    eps=1e-5;xp=list(map(float,x));xm=xp.copy();xp[i]+=eps;xm[i]-=eps
    fd=(val(g,xp,t)[0][j]-val(g,xm,t)[0][j])/(2*eps)
    pp=paths(rows,d,j,0,t=t,graph=g)
    exact=sum(prob*sum(disc*(1 if q==0 else -1) for node,q,disc in vis if node==i) for prob,vis,reward,end in pp)
    maxfd=max(maxfd,abs(fd-exact));close(fd,exact,3e-6);nfd+=1
serial=json.loads(json.dumps(cases,default=lambda q:float(q)))
(OUT/'experiment-cases.json').write_text(json.dumps({'seed':SEED,'cases':serial},indent=2)+'\n')
result={'seed':SEED,'case_count':len(cases),'enumerated_paths':npaths,'arbitrary_profile_saddle_checks':saddlechecks,'finite_difference_checks':nfd,'max_absolute_finite_difference_error':maxfd,'cases_sha256':hashlib.sha256((OUT/'experiment-cases.json').read_bytes()).hexdigest(),'status':'passed','limits':'Numerical independent stress test; exact Lean consumers and kernel contracts provide the proofs.'}
(OUT/'experiment-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
