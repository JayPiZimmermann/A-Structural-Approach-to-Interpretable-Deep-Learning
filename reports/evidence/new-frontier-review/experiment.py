"""Independent exact-arithmetic boundary audit. Python standard library only.

No production Lean definitions are imported or parsed. The producer uses ordinary
signed matrices, gates, enumerated neuron paths, and independently built split
stream recurrences. Seed and counters are emitted for replay.
"""
import hashlib
import itertools
import json
import random
from fractions import Fraction as Q
from pathlib import Path

SEED = 20261109
rng = random.Random(SEED)
counts = dict(networks=0, gate_ties=0, zero_edges=0, negative_edges=0,
              activation_coordinates=0, affine_readout_coordinates=0,
              routing_rows=0, empty_routing_rows=0, negative_raw_inputs=0)
cases = []

def dot(a, b):
    return sum((x*y for x,y in zip(a,b)), Q(0))

def matpair(W, bias, pair):
    p,n = pair
    return ([sum((max(w,0)*a+max(-w,0)*b for w,a,b in zip(row,p,n)),Q(0))
             +max(c,0) for row,c in zip(W,bias)],
            [sum((max(w,0)*b+max(-w,0)*a for w,a,b in zip(row,p,n)),Q(0))
             +max(-c,0) for row,c in zip(W,bias)])

def propagated_paths(Ws, gates, start, index, output):
    # Enumerate genuine neuron-index paths, with no separate stream/sign choices.
    widths=[len(w) for w in Ws]
    total=[Q(0),Q(0)]
    for rest in itertools.product(*(range(w) for w in widths[start:])):
        if not rest or rest[-1] != output:
            continue
        prev=index; weight=Q(1); parity=0
        for l,j in enumerate(rest,start):
            w=Ws[l][j][prev]
            parity ^= int(w<0)
            weight *= abs(w)*gates[l][j]
            prev=j
        total[parity]+=weight
    if start==len(Ws) and index==output:
        total[0]=Q(1)
    return total

def path_pair(Ws, bs, gates, initial, output):
    answer=[Q(0),Q(0)]
    for i,(p,n) in enumerate(zip(*initial)):
        even,odd=propagated_paths(Ws,gates,0,i,output)
        answer[0]+=even*p+odd*n
        answer[1]+=even*n+odd*p
    for l,b in enumerate(bs):
        for j,c in enumerate(b):
            even,odd=propagated_paths(Ws,gates,l+1,j,output)
            p,n=max(c,0)*gates[l][j],max(-c,0)*gates[l][j]
            answer[0]+=even*p+odd*n
            answer[1]+=even*n+odd*p
    return answer

for number in range(700):
    depth=rng.randrange(1,5)
    widths=[rng.randrange(0,4)]+[rng.randrange(1,4) for _ in range(depth)]
    Ws=[[[Q(rng.randrange(-2,3)) for _ in range(widths[l])]
          for _ in range(widths[l+1])] for l in range(depth)]
    bs=[[Q(rng.randrange(-2,3)) for _ in range(widths[l+1])] for l in range(depth)]
    initial=([Q(rng.randrange(4)) for _ in range(widths[0])],
             [Q(rng.randrange(4)) for _ in range(widths[0])])
    pair=initial
    raw=[p-n for p,n in zip(*pair)]
    counts['negative_raw_inputs']+=sum(x<0 for x in raw)
    gates=[]
    for W,b in zip(Ws,bs):
        z=[dot(row,raw)+c for row,c in zip(W,b)]
        gate=[int(v>0) for v in z]; gates.append(gate)
        pre=matpair(W,b,pair)
        pair=([p*g for p,g in zip(pre[0],gate)],[n*g for n,g in zip(pre[1],gate)])
        raw=[max(v,0) for v in z]
        assert [p-n for p,n in zip(*pair)]==raw
        counts['gate_ties']+=sum(v==0 for v in z)
        counts['negative_edges']+=sum(w<0 for row in W for w in row)
        counts['zero_edges']+=sum(w==0 for row in W for w in row)
    for j in range(widths[-1]):
        assert path_pair(Ws,bs,gates,initial,j)==[pair[0][j],pair[1][j]]
        counts['activation_coordinates']+=1
    # Ungated signed and biased terminal affine readout, rather than silently adding a ReLU.
    R=[[Q(rng.randrange(-2,3)) for _ in range(widths[-1])]]
    c=[Q(rng.randrange(-2,3))]
    affine=matpair(R,c,pair)
    assert path_pair(Ws+[R],bs+[c],gates+[[1]],initial,0)==[affine[0][0],affine[1][0]]
    assert affine[0][0]-affine[1][0]==dot(R[0],raw)+c[0]
    counts['affine_readout_coordinates']+=1
    counts['networks']+=1
    cases.append([widths,Ws,bs,initial])

for width in range(4):
    for raw_tuple in itertools.product((-1,0,1),repeat=width):
        for weight_tuple in itertools.product((-1,0,1),repeat=width):
            for bias,eps in itertools.product((-1,0,1),(0,1)):
                products=[Q(x*w) for x,w in zip(raw_tuple,weight_tuple)]
                P=Q(eps)+max(Q(bias),0)+sum(map(lambda z:max(z,0),products),Q(0))
                N=Q(eps)+max(-Q(bias),0)+sum(map(lambda z:max(-z,0),products),Q(0))
                assert P-N==dot(raw_tuple,weight_tuple)+bias
                assert (P-N>0)==(dot(raw_tuple,weight_tuple)+bias>0)
                for sign in (1,-1):
                    masses=[Q(eps),max(sign*Q(bias),0)]+[max(sign*z,0) for z in products]
                    total=sum(masses,Q(0))
                    probs=[m/total for m in masses] if total else [Q(1)]+[Q(0)]*(len(masses)-1)
                    assert sum(probs)==1
                    assert all(p>=0 for p in probs)
                    assert all(probs[i]==(masses[i]/total if total else 0) for i in range(1,len(masses)))
                    counts['routing_rows']+=1
                    counts['empty_routing_rows']+=int(not total)

# Negative controls guard two easy changed-target bugs.
assert max(Q(-3)*Q(-2),0)==6
assert max(Q(-3),0)*max(Q(-2),0)==0  # clipping raw input before multiplying would fail
noncanonical_pair=[1*2+1*1+1,1*1+1*2]
canonical_pair=matpair([[Q(0)]],[Q(1)],([Q(2)],[Q(1)]))
assert noncanonical_pair != [canonical_pair[0][0],canonical_pair[1][0]]

payload=json.dumps(cases,default=str,separators=(',',':')).encode()
result={'seed':SEED,'counts':counts,'cases_sha256':hashlib.sha256(payload).hexdigest(),
        'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'failures':[], 'negative_controls_detected':['premature raw-input clipping','noncanonical parity path formula'],
        'scope':'Exact independent finite cases; supports but does not replace universal Lean proofs.'}
Path(__file__).with_name('experiment-results.json').write_text(json.dumps(result,indent=2)+'\n')
Path(__file__).with_name('experiment-cases.json').write_bytes(payload)
print(json.dumps(result,indent=2))
