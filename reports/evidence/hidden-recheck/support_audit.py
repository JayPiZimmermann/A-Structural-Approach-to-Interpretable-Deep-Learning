from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

class Dual:
    def __init__(self,v,d):self.v=F(v);self.d=tuple(map(F,d))
    def __add__(self,b):return Dual(self.v+b.v,[a+c for a,c in zip(self.d,b.d)])
    def scale(self,k):return Dual(k*self.v,[k*a for a in self.d])
def split(layers,point):
    p,q=Dual(point[0],(1,0)),Dual(point[1],(0,1));ties=0
    for w,b in layers:
        wp,wn=max(w,0),max(-w,0)
        bp,bn=max(b,0),max(-b,0)
        pp=p.scale(wp)+q.scale(wn)+Dual(bp,(0,0))
        nn=p.scale(wn)+q.scale(wp)+Dual(bn,(0,0))
        ties+=int(pp.v==nn.v)
        p,q=(pp if pp.v>nn.v else nn),nn
    return (p,q),ties
points=list(product(map(F,[-1,0,1]),repeat=2))
networks=[[(w1,b1),(w2,b2)] for w1,b1,w2,b2 in product(map(F,[-1,0,1]),repeat=4)]
tests=0;tied_tests=0
for layers,x,y in product(networks,points,points):
    fx,ties=split(layers,x);fy,_=split(layers,y)
    for a,b in zip(fx,fy):
        support=a.v+sum(d*(v-u) for d,u,v in zip(a.d,x,y))
        assert support<=b.v,(layers,x,y,support,b.v)
        tests+=1;tied_tests+=int(ties>0)
# Negative control: dropping monotone readout hypothesis must fail at a tie.
a,_=split([(F(1),F(0))],(F(0),F(0)))
b,_=split([(F(1),F(0))],(F(1),F(0)))
negative_support=-a[0].v-a[0].d[0]
negative_target=-b[0].v
assert negative_support>negative_target
# The second Q in ReLU(ReLU(x)) is identically zero, despite zero second gates on x<0.
for x in map(F,[-3,-2,-1,0,1,2,3]):
    q2=min(max(x,0),0)
    g1=int(x>0);g2=int(max(x,0)>0)
    selected=(1-g2)*g1
    assert q2==0 and selected==0
# Discarded Q counterexample validates the deliberate pointwise scope distinction.
q=lambda x:min(F(x),F(0))
left=(q(0)-q(-1))/F(1);right=(q(1)-q(0))/F(1)
assert (left,right)==(F(1),F(0))
result={'arithmetic':'exact fractions','enumeration':'Every two-layer scalar canonical network with weights/biases in {-1,0,1}; every pair x,y in {-1,0,1}^2','networks':len(networks),'support_inequalities_checked':tests,'checks_with_tied_gate':tied_tests,'failures':0,'negative_control':'rp=-1 at tied unit ReLU fails support: selected support 0 > actual -1, so monotone-readout premise is essential','prefix_control':'Second Q of ReLU(ReLU(x)) is min(ReLU(x),0)=0, selected derivative zero even on entire negative halfline','pointwise_scope_control':'Zero readout discards unit-ReLU Q=min(x,0); both heads constant at x=0 but Q has one-sided slopes 1 and 0. This is not a counterexample to the new correctly restricted pointwise theorem.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
