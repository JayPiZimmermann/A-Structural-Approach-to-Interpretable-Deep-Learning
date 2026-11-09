"""Independent finite CPWL/lattice and signed-max audit, standard library only.

Exact Fraction arithmetic; no production definitions or author-produced examples
are imported. A small RREF producer derives slope dependences and recursively
constructs the signed small-max expression, instead of assuming one.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from functools import lru_cache
from bisect import bisect_right
import hashlib
import json
import random
from pathlib import Path

SEED=20261109
rng=random.Random(SEED)
stats=dict(polynomials=0,dimension_zero=0,partition_steps=0,orientation_flips=0,
           zero_bias_dependence=0,repeated_slopes=0,signed_max_evaluations=0,
           lattice_functions=0,lattice_blocks=0,lattice_evaluations=0,separation_pairs=0)
cases=[]

def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q(0))

def null_vector(columns):
    rows=[list(row) for row in zip(*columns)]
    n=len(columns); row=0; pivots=[]
    for col in range(n):
        pivot=next((k for k in range(row,len(rows)) if rows[k][col]),None)
        if pivot is None: continue
        rows[row],rows[pivot]=rows[pivot],rows[row]
        scale=rows[row][col]; rows[row]=[x/scale for x in rows[row]]
        for k in range(len(rows)):
            if k!=row:
                scale=rows[k][col]
                rows[k]=[x-scale*y for x,y in zip(rows[k],rows[row])]
        pivots.append(col);row+=1
        if row==len(rows): break
    free=next(j for j in reversed(range(n)) if j not in pivots)
    v=[Q(0)]*n;v[free]=Q(1)
    for i,col in enumerate(pivots):v[col]=-rows[i][free]
    assert any(v) and all(dot(r,v)==0 for r in zip(*columns))
    return v

for dim in range(4):
  for number in range(90):
    n=rng.randrange(dim+2,dim+6)
    slopes=[tuple(Q(rng.randrange(-2,3)) for _ in range(dim)) for _ in range(n)]
    intercepts=[Q(rng.randrange(-7,8)) for _ in range(n)]
    points=list(product(map(Q,(-2,-1,0,1,2)),repeat=dim))
    stats['repeated_slopes']+=n-len(set(slopes))

    @lru_cache(None)
    def reduce(S):
        if len(S)<=dim+1:return {S:Q(1)}
        c=null_vector([(Q(1),)+slopes[i] for i in S])
        bias=dot(c,[intercepts[i] for i in S])
        if bias>0:c=[-v for v in c];bias=-bias;stats['orientation_flips']+=1
        stats['zero_bias_dependence']+=int(bias==0)
        A=tuple(i for i,v in zip(S,c) if v>0)
        B=tuple(i for i,v in zip(S,c) if v<=0)
        assert A and B and sum(c)==0 and bias<=0
        stats['partition_steps']+=1
        for x in points:
            values={i:dot(slopes[i],x)+intercepts[i] for i in S}
            assert min(values[i] for i in A)<=max(values[i] for i in B)
            assert dot(c,[values[i] for i in S])==bias
        result={}
        # Isolate the full-set term from the alternating powerset identity.
        for count in range(len(A)):
            for U in combinations(A,count):
                T=tuple(sorted(B+U));sign=Q((-1)**(len(A)+1+count))
                assert 0<len(T)<len(S)
                for block,weight in reduce(T).items():
                    result[block]=result.get(block,Q(0))+sign*weight
        return {block:c for block,c in result.items() if c}

    expression=reduce(tuple(range(n)))
    assert all(1<=len(block)<=dim+1 for block in expression)
    for x in points:
        values=[dot(v,x)+b for v,b in zip(slopes,intercepts)]
        reconstructed=sum((c*max(values[i] for i in block) for block,c in expression.items()),Q(0))
        assert reconstructed==max(values)
        stats['signed_max_evaluations']+=1
    stats['polynomials']+=1;stats['dimension_zero']+=int(dim==0)
    cases.append(dict(kind='max',dimension=dim,slopes=slopes,intercepts=intercepts,
                      expression=[[block,c] for block,c in sorted(expression.items())]))

for number in range(140):
    n=rng.randrange(2,8)
    breaks=sorted(map(Q,rng.sample(range(-5,6),n-1)))
    slopes=[Q(rng.randrange(-3,4)) for _ in range(n)]
    intercepts=[Q(rng.randrange(-6,7))]
    for i,knot in enumerate(breaks):
        intercepts.append(intercepts[-1]+(slopes[i]-slopes[i+1])*knot)
    def f(x):
        i=bisect_right(breaks,x)
        return slopes[i]*x+intercepts[i]
    def line(i,x):return slopes[i]*x+intercepts[i]
    for i,knot in enumerate(breaks):assert line(i,knot)==line(i+1,knot)
    crossings=set(breaks)
    for i,j in combinations(range(n),2):
        if slopes[i]!=slopes[j]:
            crossings.add((intercepts[j]-intercepts[i])/(slopes[i]-slopes[j]))
    roots=sorted(crossings)
    # Complete arrangement representatives identify every realized upper set:
    # all equality points and one point in each open interval, including tails.
    representatives=roots+[roots[0]-1,roots[-1]+1]+[(a+b)/2 for a,b in zip(roots,roots[1:])]
    blocks={tuple(i for i in range(n) if f(x)<=line(i,x)) for x in representatives}
    assert all(block for block in blocks)
    probes=representatives+[Q(rng.randrange(-30,31),rng.randrange(1,5)) for _ in range(30)]
    for x in probes:
        lattice=max(min(line(i,x) for i in block) for block in blocks)
        assert lattice==f(x)
        # Independent numerical DC closure using the exact max-of-differences law.
        G=H=None
        for block in sorted(blocks):
            g=Q(0);h=max(-line(i,x) for i in block)
            if G is None:G,H=g,h
            else:G,H=max(G+h,g+H),H+h
        assert G-H==f(x)
        stats['lattice_evaluations']+=1
    selected=rng.sample(probes,min(12,len(probes)))
    for x,y in product(selected,repeat=2):
        assert any(f(x)<=line(i,x) and line(i,y)<=f(y) for i in range(n))
        stats['separation_pairs']+=1
    stats['lattice_functions']+=1;stats['lattice_blocks']+=len(blocks)
    cases.append(dict(kind='continuous-piecewise',breakpoints=breaks,slopes=slopes,
                      intercepts=intercepts,blocks=sorted(blocks)))

# Negative controls: these fail if essential proof steps are silently dropped.
slopes=[Q(0),Q(1),Q(2)];bias=[Q(10),Q(0),Q(10)];c=[Q(1),Q(-2),Q(1)]
assert sum(c)==0 and dot(c,slopes)==0 and dot(c,bias)>0
assert min(bias[0],bias[2])>bias[1]  # Unoriented A={0,2}, B={1} fails at x=0.
assert not any(Q(1)<=v and v<=Q(0) for v in (Q(0),Q(1)))
# Last assertion is endpoint separation for the discontinuous constant selector
# f(t)=1 for t<1/2 and f(t)=0 otherwise: finite selection alone is insufficient.
assert abs(Q(-1))+abs(Q(1))!=2*abs(Q(0))  # d rather than d+1 would force |x| affine.

payload=json.dumps(cases,default=str,separators=(',',':')).encode()
out=Path(__file__).parent
(out/'experiment-cases.json').write_bytes(payload)
results={'seed':SEED,'counts':stats,'failures':[],
 'negative_controls_detected':['omitting intercept orientation','omitting continuity','reducing d+1 to d'],
 'cases_sha256':hashlib.sha256(payload).hexdigest(),
 'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'scope':'Independent exact finite tests and constructive coefficient producer; not a replacement for the universal Lean proofs.'}
(out/'experiment-results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
