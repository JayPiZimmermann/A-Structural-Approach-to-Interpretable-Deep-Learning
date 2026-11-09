"""Independent exact matrix compiler for finite signed affine-max forests.

Uses Fraction and standard-library containers only. Constructs explicit weight
matrices/bias vectors, evaluates their ReLU layers, and compares with the direct
max-affine expression. No Lean definitions or author's examples are imported.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json
import random

SEED=20261109
rng=random.Random(SEED)
counts=dict(forests=0,zero_dimension=0,empty_outer_sum=0,padded_forests=0,
            evaluations=0,negative_outputs=0,exact_hidden_gate_ties=0,
            total_hidden_layers=0,negative_outer_coefficients=0)
cases=[]

def dot(a,b):return sum((x*y for x,y in zip(a,b)),Q(0))

def compile_forest(n,k,slopes,biases):
    """Returns layers, affine readout weights/biases, and final hidden width."""
    outputs=len(slopes)
    if k==0:
        return [],[rows[0] for rows in slopes],[row[0] for row in biases],n
    half=2**(k-1)
    childrenW=[child for rows in slopes for child in (rows[:half],rows[half:])]
    childrenB=[child for row in biases for child in (row[:half],row[half:])]
    layers,W,b,width=compile_forest(n,k-1,childrenW,childrenB)
    newW=[];newb=[]
    for i in range(outputs):
        u,v=W[2*i],W[2*i+1];bu,bv=b[2*i],b[2*i+1]
        newW.extend([[a-c for a,c in zip(u,v)],list(v),[-a for a in v]])
        newb.extend([bu-bv,bv,-bv])
    readW=[]
    for i in range(outputs):
        row=[Q(0)]*(3*outputs)
        row[3*i:3*i+3]=[Q(1),Q(1),Q(-1)]
        readW.append(row)
    return layers+[(newW,newb)],readW,[Q(0)]*outputs,3*outputs

def evaluate(layers,w,b,x):
    values=x
    for W,B in layers:
        pre=[dot(row,values)+c for row,c in zip(W,B)]
        counts['exact_hidden_gate_ties']+=sum(v==0 for v in pre)
        values=[max(v,0) for v in pre]
    return dot(w,values)+b

for dim in range(7):
  for number in range(24):
    k=dim.bit_length()  # ceil(log2(dim+1)), with k=0 when dim=0.
    outputs=number%5
    terms=[];paddedW=[];paddedB=[];coeff=[];padded=False
    for i in range(outputs):
        size=rng.randrange(1,dim+2)
        W=[[Q(rng.randrange(-3,4)) for _ in range(dim)] for _ in range(size)]
        B=[Q(rng.randrange(-5,6)) for _ in range(size)]
        terms.append((W,B));coeff.append(Q(rng.randrange(-3,4)))
        paddedW.append(W+[W[0]]*(2**k-size));paddedB.append(B+[B[0]]*(2**k-size))
        padded |= size<2**k
    layers,W,B,width=compile_forest(dim,k,paddedW,paddedB)
    finalW=[sum((c*row[j] for c,row in zip(coeff,W)),Q(0)) for j in range(width)]
    finalB=dot(coeff,B)
    assert len(layers)==k and 2**k>=dim+1
    if k:assert 2**(k-1)<dim+1
    previous_width=dim
    for matrix,bias in layers:
        assert len(matrix)==len(bias) and all(len(row)==previous_width for row in matrix)
        previous_width=len(matrix)
    assert previous_width==width and len(finalW)==width
    probes=[tuple(Q(0) for _ in range(dim))]
    probes += [tuple(Q(rng.randrange(-6,7),rng.randrange(1,4)) for _ in range(dim)) for _ in range(16)]
    for x in probes:
        expected=sum((c*max(dot(row,x)+b for row,b in zip(w,bs))
                      for c,(w,bs) in zip(coeff,terms)),Q(0))
        actual=evaluate(layers,finalW,finalB,x)
        assert actual==expected
        counts['evaluations']+=1;counts['negative_outputs']+=int(actual<0)
    counts['forests']+=1;counts['zero_dimension']+=int(dim==0)
    counts['empty_outer_sum']+=int(outputs==0);counts['padded_forests']+=int(padded)
    counts['negative_outer_coefficients']+=sum(c<0 for c in coeff)
    counts['total_hidden_layers']+=len(layers)
    cases.append(dict(dimension=dim,hidden_depth=k,terms=terms,coefficients=coeff,
                      layers=layers,readout_weights=finalW,readout_bias=finalB))

# Concrete negative controls for signed rails and affine terminal semantics.
u,v=Q(-3),Q(-5)
correct=max(u-v,0)+max(v,0)-max(-v,0)
assert correct==max(u,v)==-3
assert max(u-v,0)+max(v,0)!=correct  # Dropping the negative-v rail fails.
assert max(correct,0)!=correct     # Appending an output ReLU fails.

payload=json.dumps(cases,default=str,separators=(',',':')).encode()
base=Path(__file__).parent;(base/'experiment-cases.json').write_bytes(payload)
result={'seed':SEED,'counts':counts,'failures':[],
 'negative_controls_detected':['dropping negative signed rail','adding final output ReLU'],
 'cases_sha256':hashlib.sha256(payload).hexdigest(),
 'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'scope':'Independent exact matrix constructions and evaluations; universal correctness and literal real-log depth are checked in Lean.'}
(base/'experiment-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
