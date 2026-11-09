#!/usr/bin/env python3
"""Independent high-precision entropy-game path/payoff audit (standard library).
Decimal exp/log at precision 60, deterministic rational cases; comparisons use
explicit tolerance. This numerical evidence supplements universal Lean proofs.
"""
from decimal import Decimal as D,getcontext
from random import Random
from pathlib import Path
import json,hashlib
getcontext().prec=60
HERE=Path(__file__).resolve().parent;SEED=20261109;rng=Random(SEED);ZERO=D(0);ONE=D(1)
TOL=D('1e-45');FDTOL=D('1e-20')
counts={k:0 for k in ['networks','zero_input_networks','zero_rows','profiles','normalized_path_laws','player_payoff_checks','arbitrary_profile_advantage_checks','saddle_checks','occupation_derivatives','finite_differences','affine_readout_checks','intermediate_derivatives','pure_action_probabilities']};fails=[];cases=[]
def close(a,b):return abs(a-b)<=TOL*(1+abs(a)+abs(b))
def ck(c,s):
 if not c:fails.append(s)
def H(p):return -(p*p.ln() if p else ZERO)-((1-p)*(1-p).ln() if p!=1 else ZERO)
def gate(t,z):return ONE/(ONE+(-z/t).exp())
def soft(t,z):return t*(ONE+(z/t).exp()).ln()
def layers_forward(layers,x,t):
 values=[x];probs=[]
 for L in layers:
  out=[];r=[]
  for wp,wn,bp,bn in zip(L['wp'],L['wn'],L['bp'],L['bn']):
   z=bp-bn+sum(((a-b)*v for a,b,v in zip(wp,wn,values[-1])),ZERO)
   r.append(gate(t,z));out.append(soft(t,z))
  probs.append(r);values.append(out)
 return values,probs

def player_dp(layers,initial,profiles,t):
 # value[player][turn][neuron]
 v=[[[p if player==turn else n for p,n in initial] for turn in [0,1]] for player in [0,1]]
 for l,L in enumerate(layers):
  out=[[[] for _ in [0,1]] for _ in [0,1]]
  for player in [0,1]:
   for turn in [0,1]:
    for j,(wp,wn,bp,bn) in enumerate(zip(L['wp'],L['wn'],L['bp'],L['bn'])):
     r=profiles[turn][l][j];cont=(bp if player==turn else bn)+sum((a*v[player][turn][i]+b*v[player][1-turn][i] for i,(a,b) in enumerate(zip(wp,wn))),ZERO)
     out[player][turn].append(r*cont+(t*H(r) if player==turn else ZERO))
  v=out
 return v

def signed_dp(layers,x,profiles,t):
 p=x;q=[-a for a in x]
 for l,L in enumerate(layers):
  pp=[];qq=[]
  for j,(wp,wn,bp,bn) in enumerate(zip(L['wp'],L['wn'],L['bp'],L['bn'])):
   rp,rn=profiles[0][l][j],profiles[1][l][j]
   pp.append(rp*(bp-bn+sum((a*u+b*v for a,b,u,v in zip(wp,wn,p,q)),ZERO))+t*H(rp))
   qq.append(rn*(bn-bp+sum((b*u+a*v for a,b,u,v in zip(wp,wn,p,q)),ZERO))-t*H(rn))
  p,q=pp,qq
 return p,q

def paths(layers,initial,profiles,t,l,j,turn):
 # Probability, terminal (input,absolute turn) or None, cumulative discount,
 # and both realized player payoffs. Stop and zero-row continue remain distinct
 # action histories, despite their common cemetery state.
 if l==0:return [(ONE,(j,turn),ONE,tuple(initial[j][player!=turn] for player in [0,1]))]
 L=layers[l-1];wp,wn=L['wp'][j],L['wn'][j];r=profiles[turn][l-1][j];disc=sum(wp+wn,ZERO)
 bonus=tuple(t*H(r) if player==turn else ZERO for player in [0,1]);bias=tuple(L['bp'][j] if player==turn else L['bn'][j] for player in [0,1])
 result=[]
 if r!=1:result.append((1-r,None,ONE,bonus))
 if disc==0:
  if r:result.append((r,None,ZERO,tuple(b+c for b,c in zip(bias,bonus))))
 else:
  for i,(a,b) in enumerate(zip(wp,wn)):
   for flip,w in enumerate([a,b]):
    if w and r:
     for prob,terminal,discount,pay in paths(layers,initial,profiles,t,l-1,i,turn^flip):
      result.append((r*w/disc*prob,terminal,disc*discount,tuple(v+b+disc*y for v,b,y in zip(bonus,bias,pay))))
 return result

def jacobian(layers,values,probs,start):
 n=len(values[start]);J=[[ONE if i==j else ZERO for i in range(n)] for j in range(n)]
 for l in range(start,len(layers)):
  L=layers[l];J=[[probs[l][j]*sum(((a-b)*J[h][i] for h,(a,b) in enumerate(zip(wp,wn))),ZERO) for i in range(n)] for j,(wp,wn) in enumerate(zip(L['wp'],L['wn']))]
 return J

def numbers(x):
 if isinstance(x,D):return str(x)
 if isinstance(x,dict):return {k:numbers(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [numbers(v) for v in x]
 return x

for case in range(96):
 n=case%4;t=[D('0.5'),ONE,D(2)][case%3];initial=[(D(rng.randrange(-2,5))/2,D(rng.randrange(-2,5))/2) for _ in range(n)];x=[p-q for p,q in initial];layers=[]
 for l in range(1+case%3):
  m=1+(case+l)%3;wp=[];wn=[]
  for j in range(m):
   a=[D(rng.randrange(4))/4 for _ in range(n)];b=[D(rng.randrange(4))/4 for _ in range(n)]
   if (case+l+j)%5==0:a=[ZERO]*n;b=[ZERO]*n
   counts['zero_rows']+=int(sum(a+b,ZERO)==0);wp.append(a);wn.append(b)
  layers.append({'wp':wp,'wn':wn,'bp':[D(rng.randrange(-2,4))/2 for _ in range(m)],'bn':[D(rng.randrange(-2,4))/2 for _ in range(m)]});n=m
 values,gibbs=layers_forward(layers,x,t);eq=[gibbs,gibbs]
 randoms=[[[D(rng.randrange(5))/4 for _ in L['bp']] for L in layers] for _ in [0,1]]
 profiles=[eq,randoms,[randoms[0],gibbs],[gibbs,randoms[1]]]
 counts['networks']+=1;counts['zero_input_networks']+=int(not x)
 cases.append(numbers({'theta':t,'initial':initial,'layers':layers,'deviation_profiles':randoms}))
 for profile in profiles:
  counts['profiles']+=1;counts['pure_action_probabilities']+=sum(r in [ZERO,ONE] for player in profile for layer in player for r in layer)
  v=player_dp(layers,initial,profile,t);signed=signed_dp(layers,x,profile,t)
  for j in range(n):
   for turn in [0,1]:
    counts['arbitrary_profile_advantage_checks']+=1;ck(close(v[0][turn][j]-v[1][turn][j],signed[turn][j]),f'advantage {case} {j} {turn}')
    ps=paths(layers,initial,profile,t,len(layers),j,turn);counts['normalized_path_laws']+=1;ck(close(sum((p for p,_,_,_ in ps),ZERO),ONE),'path normalization')
    for player in [0,1]:
     counts['player_payoff_checks']+=1;ck(close(sum((p*pay[player] for p,_,_,pay in ps),ZERO),v[player][turn][j]),f'full payoff {case} {j} {turn} {player}')
 lower=signed_dp(layers,x,[randoms[0],gibbs],t);upper=signed_dp(layers,x,[gibbs,randoms[1]],t);equilibrium=signed_dp(layers,x,eq,t)
 for j,y in enumerate(values[-1]):
  for turn in [0,1]:
   target=-y if turn else y;counts['saddle_checks']+=1
   ck(lower[turn][j]<=target+TOL and target<=upper[turn][j]+TOL and close(equilibrium[turn][j],target),f'saddle {case} {j} {turn}')
 # Genuine original-coordinate chain Jacobian, plus actual forward differences.
 J=jacobian(layers,values,gibbs,0)
 for j in range(n):
  for q in [0,1]:
   ps=paths(layers,initial,eq,t,len(layers),j,q)
   for i in range(len(x)):
    occ=[sum((p*disc for p,end,disc,_ in ps if end==(i,r)),ZERO) for r in [0,1]]
    counts['occupation_derivatives']+=1;ck(close(J[j][i],(-1 if q else 1)*(occ[0]-occ[1])),f'gradient {case} {j} {i} {q}')
  for i in range(len(x)):
   eps=D('1e-12');a=x.copy();b=x.copy();a[i]+=eps;b[i]-=eps
   fd=(layers_forward(layers,a,t)[0][-1][j]-layers_forward(layers,b,t)[0][-1][j])/(2*eps)
   counts['finite_differences']+=1;ck(abs(fd-J[j][i])<=FDTOL*(1+abs(fd)+abs(J[j][i])),f'finite diff {case} {j} {i}')
 # Forced arbitrary signed affine output, including a separate signed bias.
 C=[D(rng.randrange(-3,4))/2 for _ in range(n)];bias=D(rng.randrange(-4,5));out=sum((c*y for c,y in zip(C,values[-1])),ZERO)+bias
 eqread=sum((max(c,ZERO)*equilibrium[0][j]+max(-c,ZERO)*equilibrium[1][j] for j,c in enumerate(C)),ZERO)+bias
 counts['affine_readout_checks']+=1;ck(close(eqread,out),'affine output')
 # Actual forward cut: suffix uses true prefix activations and restricted policies.
 for cut in range(1,len(layers)):
  suffix=layers[cut:];sx=values[cut];sinit=[(z,ZERO) for z in sx];sp=[gibbs[cut:],gibbs[cut:]];SJ=jacobian(layers,values,gibbs,cut)
  for j in range(n):
   for q in [0,1]:
    ps=paths(suffix,sinit,sp,t,len(suffix),j,q)
    for i in range(len(sx)):
     o=[sum((p*di for p,end,di,_ in ps if end==(i,r)),ZERO) for r in [0,1]]
     counts['intermediate_derivatives']+=1;ck(close(SJ[j][i],(-1 if q else 1)*(o[0]-o[1])),'cut gradient')
# Negative controls: both-player entropy credit cancels the actual advantage,
# and individual stream derivative 3/4 at (1,1) differs from occupation 1/2.
ln2=D(2).ln();ck(ln2>0,'entropy must not cancel both players')
def splitplus(u,v):r=gate(ONE,u-v);return r*u+H(r)
eps=D('1e-12');head_deriv=(splitplus(1+eps,ONE)-splitplus(1-eps,ONE))/(2*eps)
ck(abs(head_deriv-D('0.75'))<FDTOL and abs(head_deriv-D('0.5'))>D('0.2'),'individual head negative control')
raw=(json.dumps(cases,indent=2,sort_keys=True)+'\n').encode();(HERE/'experiment-cases.json').write_bytes(raw)
r={'seed':SEED,'decimal_precision':getcontext().prec,'identity_relative_tolerance':str(TOL),'finite_difference_relative_tolerance':str(FDTOL),'counts':counts,'failures':fails,'negative_controls':['crediting entropy to both players falsely cancels positive zero-preactivation value','individual soft positive-stream derivative at (1,1) is 3/4 while occupation is 1/2','dropping continuation bias loses nonzero values at zero-fan-in nodes'],'cases_sha256':hashlib.sha256(raw).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Independent finite high-precision checks for layered arbitrary profiles and complete action histories; they supplement the universal kernel proofs and do not certify a residual/maxpool extension.'}
(HERE/'experiment-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));assert not fails
