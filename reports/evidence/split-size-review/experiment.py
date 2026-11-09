#!/usr/bin/env python3
"""Independent explicit graph materialization for local-tree split size.
Every expression occurrence receives a distinct vertex; references become
one-edge copies of earlier shared output vertices. Standard library only.
"""
from fractions import Fraction as Q
from pathlib import Path
from random import Random
import json,hashlib,math
HERE=Path(__file__).resolve().parent;SEED=20261109;rng=Random(SEED)
counts={'source_graphs':0,'zero_input_graphs':0,'gates':0,'materialized_vertices':0,'materialized_arcs':0,'recovery_checks':0,'monotonicity_checks':0,'empty_products':0,'zero_exponents':0,'negative_biases':0,'repeated_parents':0}
failures=[]
def ck(c,s):
 if not c:failures.append(s)
def add(a,b):return ('a',a,b)
def source_expr(g):
 if g['kind']=='prod':
  e=('c',1)
  parents=[p for p,w in zip(g['parents'],g['powers']) for _ in range(w)]
  for p in reversed(parents):e=('m',('i',p),e)
  return e
 branches=[]
 for w,b in zip(g['weights'],g['biases']):
  terms=('c',0)
  for p,v in reversed(list(zip(g['parents'],w))):terms=add(('s',v,('i',p)),terms)
  branches.append(add(('c',b),terms))
 e=branches[0]
 for a in reversed(branches[1:]):e=('x',a,e)
 return e

def split(e):
 t=e[0]
 if t=='i':return ('i',e[1],0),('i',e[1],1)
 if t=='c':return ('c',max(e[1],0)),('c',max(-e[1],0))
 if t=='s':
  p,n=split(e[2]);a,b=max(e[1],0),max(-e[1],0)
  return add(('s',a,p),('s',b,n)),add(('s',a,n),('s',b,p))
 p,n=split(e[1]);q,r=split(e[2])
 if t=='a':return add(p,q),add(n,r)
 if t=='m':return add(('m',p,q),('m',n,r)),add(('m',p,r),('m',n,q))
 return ('x',add(p,r),add(q,n)),add(n,r)

def treecount(e):
 if e[0]=='i':return 1,1
 if e[0]=='c':return 1,0
 if e[0]=='s':
  v,a=treecount(e[2]);return v+1,a+1
 va,aa=treecount(e[1]);vb,ab=treecount(e[2]);return va+vb+1,aa+ab+2

def materialize(ops,d):
 vertices=[('external',i,b) for i in range(d) for b in [0,1]]
 outputs=[(2*i,2*i+1) for i in range(d)];predicted=[2*d,0]
 def emit(e):
  t=e[0]
  if t=='i':node=('copy',outputs[e[1]][e[2]])
  elif t=='c':node=e
  elif t=='s':node=('s',e[1],emit(e[2]))
  else:node=(t,emit(e[1]),emit(e[2]))
  index=len(vertices);vertices.append(node);return index
 for g in ops:
  p,n=split(source_expr(g));vp,ap=treecount(p);vn,an=treecount(n)
  predicted[0]+=vp+vn;predicted[1]+=ap+an
  pp=emit(p);nn=emit(n);outputs.append((pp,nn))
 arcs=sum(0 if t[0] in ['external','c'] else 1 if t[0] in ['copy','s'] else 2 for t in vertices)
 ck((len(vertices),arcs)==tuple(predicted),'materialized count differs recurrence')
 for i,t in enumerate(vertices):
  deps=[] if t[0] in ['external','c'] else [t[1]] if t[0]=='copy' else [t[2]] if t[0]=='s' else list(t[1:])
  ck(all(j<i for j in deps),'cycle or forward reference')
 return vertices,outputs,arcs

def graph_eval(vertices,outputs,x):
 v=[]
 for t in vertices:
  if t[0]=='external':z=x[t[1]][t[2]]
  elif t[0]=='c':z=Q(t[1])
  elif t[0]=='copy':z=v[t[1]]
  elif t[0]=='s':z=t[1]*v[t[2]]
  elif t[0]=='a':z=v[t[1]]+v[t[2]]
  elif t[0]=='m':z=v[t[1]]*v[t[2]]
  else:z=max(v[t[1]],v[t[2]])
  v.append(z)
 return [(v[p],v[n]) for p,n in outputs]

def direct_eval(ops,x):
 v=list(x)
 for g in ops:
  if g['kind']=='max':z=max(b+sum((w*v[p] for p,w in zip(g['parents'],ws)),Q(0)) for b,ws in zip(g['biases'],g['weights']))
  else:z=math.prod(v[p]**w for p,w in zip(g['parents'],g['powers']))
  v.append(z)
 return v

cases=[]
for case in range(144):
 d=case%3;K=1+case%3;D=case%5;ops=[]
 for node in range(2+case%5):
  n=d+node;f=0 if n==0 else rng.randrange(4);parents=[rng.randrange(n) for _ in range(f)]
  if rng.randrange(2):
   rank=rng.randrange(1,K+1);ops.append({'kind':'max','parents':parents,'weights':[[rng.randrange(-3,4) for _ in parents] for _ in range(rank)],'biases':[rng.randrange(-3,4) for _ in range(rank)]})
  else:
   powers=[0]*f
   for _ in range(rng.randrange(D+1)):
    if f:powers[rng.randrange(f)]+=1
   ops.append({'kind':'prod','parents':parents,'powers':powers})
 cases.append({'d':d,'K':K,'D':D,'gates':ops})
for ci,c in enumerate(cases):
 d,ops,K,D=c['d'],c['gates'],c['K'],c['D'];verts,outs,arcs=materialize(ops,d)
 size=d+sum(1+len(g['parents']) for g in ops);C=24*2**max(K,D)*(4*K+2*D+1)
 ck(len(verts)+arcs<=C*size,f'size {ci}')
 counts['source_graphs']+=1;counts['zero_input_graphs']+=int(d==0);counts['gates']+=len(ops);counts['materialized_vertices']+=len(verts);counts['materialized_arcs']+=arcs
 for g in ops:
  counts['repeated_parents']+=int(len(set(g['parents']))<len(g['parents']))
  if g['kind']=='prod':
   counts['empty_products']+=int(not g['parents']);counts['zero_exponents']+=g['powers'].count(0)
   ck(sum(g['powers'])+1<=math.prod(w+1 for w in g['powers']),'expansion bound')
  else:counts['negative_biases']+=sum(b<0 for b in g['biases'])
 for k in range(9):
  x=[(Q(rng.randrange(-3,4)),Q(rng.randrange(-3,4))) for _ in range(d)]
  result=graph_eval(verts,outs,x);direct=direct_eval(ops,[p-n for p,n in x])
  counts['recovery_checks']+=len(result);ck([p-n for p,n in result]==direct,f'recovery {ci} {k}')
  x=[(Q(rng.randrange(4)),Q(rng.randrange(4))) for _ in range(d)];y=[(p+rng.randrange(3),n+rng.randrange(3)) for p,n in x]
  a,b=graph_eval(verts,outs,x),graph_eval(verts,outs,y)
  for (p,n),(q,r) in zip(a,b):
   counts['monotonicity_checks']+=2;ck(0<=p<=q and 0<=n<=r,f'monotone {ci} {k}')
# Deep repeated squaring has exponentially growing polynomial degree but local
# degree two and linearly growing actual graph size because earlier nodes shared.
chain=[]
for depth in [1,2,4,8,16,32]:
 ops=[{'kind':'prod','parents':[i],'powers':[2]} for i in range(depth)]
 vs,outs,arcs=materialize(ops,1);chain.append({'depth':depth,'source_size':1+2*depth,'split_size':len(vs)+arcs})
ck(len({(a['split_size']-2)//a['depth'] for a in chain})==1,'sharing chain not linear')
# One fixed parent with growing exponent refutes a constant bound based only on
# distinct fan-in, which is deliberately NOT the theorem hypothesis.
exponents=[]
for exponent in [1,2,4,8]:
 vs,_,arcs=materialize([{'kind':'prod','parents':[0],'powers':[exponent]}],1)
 exponents.append({'exponent':exponent,'source_size':3,'split_size':len(vs)+arcs})
raw=(json.dumps(cases,indent=2,sort_keys=True)+'\n').encode();(HERE/'experiment-cases.json').write_bytes(raw)
r={'seed':SEED,'counts':counts,'failures':failures,'sharing_chain':chain,'unbounded_exponent_control':exponents,'cases_sha256':hashlib.sha256(raw).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Independent materialization counts literal vertices and edges and evaluates actual emitted graph. Finite rational checks supplement universal Lean source/size contracts; no polynomial-size claim in K,D.'}
(HERE/'experiment-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));assert not failures
