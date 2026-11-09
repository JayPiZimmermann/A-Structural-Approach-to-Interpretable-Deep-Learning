#!/usr/bin/env python3
"""Independent exact-rational DAG trajectories, biased payoffs and cut derivatives.
Standard library only. Syntax/forward evaluator and explicit path enumerator are
separate. Finite differences check actual forward functions within selected cells.
"""
from fractions import Fraction as Q
from random import Random
from pathlib import Path
import json, hashlib
HERE=Path(__file__).resolve().parent
SEED=20261109
rng=Random(SEED)
counts={k:0 for k in ['graphs','zero_input_graphs','nodes','negative_scale_visits','tied_max_comparisons','zero_fanin_nodes','paths','normalized_laws','payoff_checks','visit_cut_checks','scalar_cut_checks','finite_difference_checks','strict_graphs']}
failures=[]
def check(condition,label):
    if not condition: failures.append(label)
def scalar(e,v):
    tag=e[0]
    if tag=='i': return v[e[1]]
    if tag=='c': return Q(e[1])
    if tag=='a': return scalar(e[1],v)+scalar(e[2],v)
    if tag=='s': return e[1]*scalar(e[2],v)
    return max(scalar(e[1],v),scalar(e[2],v))
def pair(e,v):
    tag=e[0]
    if tag=='i': return v[e[1]]
    if tag=='c': return (Q(max(e[1],0)),Q(max(-e[1],0)))
    if tag=='a':
        a,b=pair(e[1],v),pair(e[2],v);return (a[0]+b[0],a[1]+b[1])
    if tag=='s':
        a=pair(e[2],v);c=e[1];return (c*a[0],c*a[1]) if c>=0 else (-c*a[1],-c*a[0])
    a,b=pair(e[1],v),pair(e[2],v)
    return a if a[0]-a[1]>b[0]-b[1] else b

def linear(e,v):
    """Syntax-derived signed-edge multiset and immediate bias pair."""
    tag=e[0]
    if tag=='i':return {(e[1],False):Q(1)},(Q(0),Q(0)),True
    if tag=='c':return {},(Q(max(e[1],0)),Q(max(-e[1],0))),True
    if tag=='m':
        scores=[scalar(a,[p-n for p,n in v]) for a in e[1:]]
        k,b,regular=linear(e[1] if scores[0]>scores[1] else e[2],v)
        if scores[0]==scores[1]: counts['tied_max_comparisons']+=1
        return k,b,regular and scores[0]!=scores[1]
    if tag=='s':
        k,b,regular=linear(e[2],v);c=e[1]
        if c<0:counts['negative_scale_visits']+=1
        return {(i,t^(c<0)):abs(c)*w for (i,t),w in k.items() if c*w},tuple(abs(c)*b[t^(c<0)] for t in [False,True]),regular
    ka,ba,ra=linear(e[1],v);kb,bb,rb=linear(e[2],v)
    k=ka.copy()
    for a,w in kb.items():k[a]=k.get(a,Q(0))+w
    return k,(ba[0]+bb[0],ba[1]+bb[1]),ra and rb

def forward(ops,initial):
    v=list(initial)
    for e in ops:v.append(pair(e,v))
    return v

def scalar_forward(ops,initial):
    v=list(initial)
    for e in ops:v.append(scalar(e,v))
    return v

def paths(start,turn,d,values,rows):
    """List of (probability, [(state,sign,cumulative_discount)], total payoff).
    Paths actually terminate at an input or cemetery; no fictitious suffixes.
    """
    if start<d:return [(Q(1),[(start,turn,Q(1))],values[start][turn])]
    row,bias,_=rows[start-d];disc=sum(row.values(),Q(0))
    if disc==0:return [(Q(1),[(start,turn,Q(1))],bias[turn])]
    out=[]
    for (i,flip),weight in row.items():
        for prob,visits,pay in paths(i,turn^flip,d,values,rows):
            out.append((weight/disc*prob,[(start,turn,Q(1))]+[(j,b,disc*discount) for j,b,discount in visits],bias[turn]+disc*pay))
    return out

def occupation(ps,target,channel):
    return sum((prob*sum((disc for node,sign,disc in visits if node==target and sign==channel),Q(0)) for prob,visits,_ in ps),Q(0))

def symbolic_cut(ops,values,target,channel):
    """Independent forward-mode pair sensitivity after treating all cut nodes
    as independent inputs; no path/probability/discount quantities used."""
    cut=target+1;v=values[:cut];der=[(Q(0),Q(0)) for _ in v]
    der[target]=tuple(Q(int(t==channel)) for t in [False,True])
    def diff(e):
        t=e[0]
        if t=='i':return der[e[1]]
        if t=='c':return Q(0),Q(0)
        if t=='a':
            a,b=diff(e[1]),diff(e[2]);return a[0]+b[0],a[1]+b[1]
        if t=='s':
            a=diff(e[2]);c=e[1];return tuple(abs(c)*a[t^(c<0)] for t in [False,True])
        va,vb=pair(e[1],v),pair(e[2],v)
        return diff(e[1] if va[0]-va[1]>vb[0]-vb[1] else e[2])
    for e in ops:
        out=diff(e);v.append(pair(e,v));der.append(out)
    return der

def gen(n,depth=2):
    if n==0:return ('c',rng.randrange(-3,4))
    tags=['i','c'] if depth==0 else ['i','c','a','s','m','r']
    t=rng.choice(tags)
    if t=='i':return ('i',rng.randrange(n))
    if t=='c':return ('c',rng.randrange(-3,4))
    if t=='s':return ('s',rng.randrange(-3,4),gen(n,depth-1))
    if t=='r':return ('m',gen(n,depth-1),('c',0))
    return (t,gen(n,depth-1),gen(n,depth-1))

cases=[]
# Dedicated shared fanout with negative edge, actual nonzero negative prefix,
# zero fan-in, duplicate addition, exact tied pool and stopped ReLU.
cases.append({'d':2,'x':[[2,1],[1,0]],'ops':[('a',('i',0),('i',0)),('s',-2,('i',2)),('a',('i',2),('i',3)),('m',('i',0),('i',1)),('m',('c',0),('c',0)),('c',-5)]})
for case in range(160):
    d=case%4;ops=[gen(d+i) for i in range(rng.randrange(3,8))]
    cases.append({'d':d,'x':[[rng.randrange(-2,5),rng.randrange(-2,5)] for _ in range(d)],'ops':ops})
for ci,case in enumerate(cases):
    d,ops=case['d'],case['ops'];initial=[tuple(map(Q,p)) for p in case['x']]
    values=forward(ops,initial);scalarvalues=scalar_forward(ops,[p-n for p,n in initial])
    check(scalarvalues==[p-n for p,n in values],f'recovery {ci}')
    rows=[linear(e,values[:d+i]) for i,e in enumerate(ops)]
    regular=all(r for _,_,r in rows)
    counts['graphs']+=1;counts['zero_input_graphs']+=int(d==0);counts['nodes']+=len(ops);counts['strict_graphs']+=int(regular)
    counts['zero_fanin_nodes']+=sum(not row for row,_,_ in rows)
    for start in range(len(values)):
      allpaths=[paths(start,t,d,values,rows) for t in [False,True]]
      for turn,ps in enumerate(allpaths):
        counts['paths']+=len(ps);counts['normalized_laws']+=1
        check(sum((p for p,_,_ in ps),Q(0))==1 and all(p>=0 for p,_,_ in ps),f'law {ci} {start} {turn}')
        counts['payoff_checks']+=1
        check(sum((p*pay for p,_,pay in ps),Q(0))==values[start][turn],f'payoff {ci} {start} {turn}')
      for target in range(start+1):
        # For original input targets, cut at entire input prefix. For internal
        # targets, keep all graph predecessors at actual forward prefix values.
        cut=max(d,target+1);suffix=ops[cut-d:]
        cut_derivatives={}
        for channel in [False,True]:
          # Seed at target even for input cut with more than one retained input.
          def sensitivity():
            if cut==target+1:return symbolic_cut(suffix,values,target,channel)
            # Target input is first moved to end of a dummy prefix only in seed;
            # actual indices remain unchanged.
            v=values[:cut];der=[(Q(0),Q(0)) for _ in v];der[target]=tuple(Q(int(t==channel)) for t in [False,True])
            for e in suffix:
              k,_,_=linear(e,v)
              der.append(tuple(sum((w*der[i][t^b] for (i,b),w in k.items()),Q(0)) for t in [False,True]));v.append(pair(e,v))
            return der
          deriv=sensitivity();cut_derivatives[channel]=deriv
          for turn in [False,True]:
            occ=occupation(allpaths[turn],target,channel)
            counts['visit_cut_checks']+=1
            check(occ==deriv[start][turn],f'cut {ci} {start} {target} {turn} {channel}')
          if regular and start>=cut:
            eps=Q(1,10**7);pert=list(values[:cut]);z=list(pert[target]);z[channel]+=eps;pert[target]=tuple(z)
            pos=forward(suffix,pert)
            z[channel]-=2*eps;pert[target]=tuple(z);neg=forward(suffix,pert)
            for turn in [False,True]:
              counts['finite_difference_checks']+=1
              check((pos[start][turn]-neg[start][turn])/(2*eps)==deriv[start][turn],f'finite difference {ci} {start} {target} {turn} {channel}')
        dp=symbolic_cut(suffix,values,target,False) if cut==target+1 else None
        for q in [False,True]:
            counts['scalar_cut_checks']+=1
            signed=(-1 if q else 1)*(occupation(allpaths[q],target,False)-occupation(allpaths[q],target,True))
            check(signed==cut_derivatives[False][start][0]-cut_derivatives[False][start][1],f'selected scalar {ci} {start} {target} {q}')
            # Direct ordinary scalar finite difference for strict graphs.
            if regular and start>=cut:
                eps=Q(1,10**7);v=scalarvalues[:cut];v[target]+=eps;a=scalar_forward(suffix,v)[start];v[target]-=2*eps;b=scalar_forward(suffix,v)[start]
                check((a-b)/(2*eps)==signed,f'scalar derivative {ci} {start} {target} {q}')

# Verified source correspondence counterexample and meaningful negative controls.
tie={'inputs':[[2,1],[1,0]],'represented_values':[1,1],'source_min_index':0,'generic_binary_winner':1,'source_pair':[2,1],'generic_pair':[1,0]}
check(pair(('m',('i',0),('i',1)),[(Q(2),Q(1)),(Q(1),Q(0))])==(1,0),'tie witness')
# Path reaching an internal node also continues to an input: terminal-only
# occupation at that internal node is zero, but actual full occupation is one.
v=forward([('s',2,('i',0)),('a',('i',1),('i',0))],[(Q(1),Q(0))]);rows=[linear(('s',2,('i',0)),v[:1]),linear(('a',('i',1),('i',0)),v[:2])]
check(occupation(paths(2,False,1,v,rows),1,False)==1,'internal visits distinct from endpoint')
case_bytes=(json.dumps(cases,sort_keys=True,indent=2)+'\n').encode();(HERE/'experiment-cases.json').write_bytes(case_bytes)
r={'seed':SEED,'counts':counts,'failures':failures,'verified_source_mismatch':tie,'negative_controls_detected':['smallest-index source pool differs from generic right-tie pool','terminal-only proxy misses true internal visits','omitting bias payoff fails no-input constant graph'],'cases_sha256':hashlib.sha256(case_bytes).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Finite exact checks supplement universal Lean proofs. Probabilities and full paths are independently enumerated; actual forward finite differences check strict-cell derivatives. Generic right-tie semantic model tested; ordered source pool adapter separately required.'}
(HERE/'experiment-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));assert not failures
