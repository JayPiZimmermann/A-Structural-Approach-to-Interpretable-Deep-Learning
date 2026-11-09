from fractions import Fraction as F
from random import Random
from math import prod
import json
from pathlib import Path

R=Random(391547)
def dot(a,b): return sum((x*y for x,y in zip(a,b)),F(0))
def add(a,b): return [x+y for x,y in zip(a,b)]
def scale(c,a): return [c*x for x in a]
def zero(n): return [F(0)]*n
class Dual:
    def __init__(self,v,d): self.v,self.d=F(v),d
    def __add__(self,b): return Dual(self.v+b.v,add(self.d,b.d))
    def __mul__(self,c): return Dual(self.v*c,scale(c,self.d))
    def __sub__(self,b): return self+b*(-1)
def lin(W,b,x): return [sum((v*c for c,v in zip(w,x)),Dual(bi,zero(len(x[0].d)))) for w,bi in zip(W,b)]
def applyrelu(z): return [v if v.v>0 else Dual(0,zero(len(v.d))) for v in z]
def applymin(z): return [v if v.v<0 else Dual(0,zero(len(v.d))) for v in z]
def shift(p,q,a):
    s=add(p,q)
    return add(p,scale(-a,s)),add(q,scale(-a,s))
def back(layers,gates,a,rp,rn,beta,head):
    p,q=shift(rp,rn,beta) if head else shift(rn,rp,beta)
    p,q=shift(p,q,a[-1])
    for layer in range(len(layers)-1,-1,-1):
        W,b=layers[layer]; width=len(W[0]); pp,pn=zero(width),zero(width)
        for j,w in enumerate(W):
            for i,c in enumerate(w):
                wp,wn=max(c,0),max(-c,0)
                pp[i]+=p[j]*(wp if gates[layer][j] else wn)+q[j]*wn
                pn[i]+=p[j]*(wn if gates[layer][j] else wp)+q[j]*wp
        p,q=shift(pp,pn,a[layer])
    return p,q
checked=0; skipped=0; cases=[]
for trial in range(600):
    widths=R.choice([[2,3,1,2],[3,2,4,1],[1,1],[2],[1,2,3]])
    n=widths[0]; x=[F(R.randrange(-5,6),3) for _ in range(n)]
    layers=[([[F(R.randrange(-3,4)) for _ in range(a)] for _ in range(b)],
             [F(R.randrange(-5,6),7) for _ in range(b)]) for a,b in zip(widths,widths[1:])]
    v=[Dual(z,[F(i==j) for j in range(n)]) for i,z in enumerate(x)]
    prefixes=[]; gates=[]
    for W,b in layers:
        z=lin(W,b,v); prefixes.append(z); gates.append([u.v>0 for u in z]); v=applyrelu(z)
    case={'trial':trial,'widths':widths,'x':list(map(str,x)),'layers':[{'W':[[str(c) for c in w] for w in W],'b':list(map(str,b))} for W,b in layers]}
    if any(z.v==0 for zs in prefixes for z in zs):
        skipped+=1;case['status']='non_strict_skipped';cases.append(case);continue
    m=len(v); row=[F(R.randrange(-3,4)) for _ in range(m)]
    rp=[max(z,0) for z in row]; rn=[max(-z,0) for z in row]
    a=[F(R.randrange(-2,7),8) for _ in range(len(layers)+1)]
    beta=F(R.randrange(-2,7),8)
    case.update({'readout':list(map(str,row)),'alpha':list(map(str,a)),'beta':str(beta),'status':'passed'})
    cases.append(case)
    original=sum((u*c for u,c in zip(v,row)),Dual(0,zero(n))).d
    correction=zero(n)
    for j,z in enumerate(prefixes):
        q=applymin(z)
        for W,b in layers[j+1:]: q=lin([[abs(c) for c in w] for w in W],zero(len(W)),q)
        qd=sum((u*abs(c) for u,c in zip(q,row)),Dual(0,zero(n))).d
        coefficient=prod((1-2*t for t in a[j+1:]),start=F(1))*(1-2*beta)
        correction=add(correction,scale(coefficient,qd))
    for head in [True,False]:
        p,q=back(layers,gates,a,rp,rn,beta,head)
        actual=scale(F(1,2),add(p,scale(-1,q)))
        expected=scale(F(1,2),add(original,scale(-1,correction))) if head else scale(F(-1,2),add(original,correction))
        assert actual==expected,(trial,'shift formula',actual,expected)
    # Independent forward-mode dual split evaluates the genuine head functions.
    p=[Dual(z/2,[F(i==j)/2 for j in range(n)]) for i,z in enumerate(x)]
    q=[Dual(-z/2,[-F(i==j)/2 for j in range(n)]) for i,z in enumerate(x)]
    for W,b in layers:
        wp=[[max(c,0) for c in w] for w in W];wn=[[max(-c,0) for c in w] for w in W]
        pp=[u+v for u,v in zip(lin(wp,[max(c,0) for c in b],p),lin(wn,zero(len(W)),q))]
        nn=[u+v for u,v in zip(lin(wn,[max(-c,0) for c in b],p),lin(wp,zero(len(W)),q))]
        p,q=[u if u.v>v.v else v for u,v in zip(pp,nn)],nn
    for head in [True,False]:
        rp1,rn1=(rp,rn) if head else (rn,rp)
        actual=sum((u*c for u,c in zip(p,rp1)),Dual(0,zero(n)))+sum((u*c for u,c in zip(q,rn1)),Dual(0,zero(n)))
        pp,qq=back(layers,gates,[F(0)]*(len(layers)+1),rp,rn,F(0),head)
        assert actual.d==scale(F(1,2),add(pp,scale(-1,qq))),(trial,'actual head derivative')
    checked+=1
result={'seed':391547,'arithmetic':'exact fractions','generated':600,'strict_networks_checked':checked,'non_strict_skipped':skipped,'checks':['full varying-width shifted affine-readout g/h Q-source closed forms','independent forward-mode actual plain affine-head derivatives'],'failures':0,'limitations':'Finite experiment, not universal proof; tests actual algebra independently of Lean implementations; includes negative and >1/2 shifts, canonical bias splits, variable depth/width and signed readout.'}
Path(__file__).with_name('rational_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
