import json
from pathlib import Path
items=[]
def add(mod,name,ty,scope,univ=None,kind=None):
 d={'module':'HiddenMonotonicity.'+mod,'declaration':'HiddenMonotonicity.'+name,'expected_type':ty,'open_namespaces':['HiddenMonotonicity'],'open_scopes':['BigOperators'],'universes':univ or [],'review_id':'hidden-recheck/older/'+name,'review_evidence':'reports/adversarial-hidden-recheck.json','scope':scope}
 if kind:d['kind']=kind
 items.append(d)
add('Sensitivities','canonical_weight_split',
'''∀ (w : ℝ), max w 0 - max (-w) 0 = w ∧ max w 0 + max (-w) 0 = |w|''',
'Canonical scalar positive and negative parts recover the signed weight and its absolute value.')
add('OriginalTrace','Network.sensitivity_complementarity_absolute',
'''∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : PairVec n) (r : Row m) (head : Bool),
 ((net.trace x).stabilized (fun _ => 0) r head).1 + ((net.trace x).stabilized (fun _ => 0) r head).2 = r.comp net.absoluteMap''',
'Exact selected-mask mass of projection heads for canonical backbone; affine final readout uses affine_canonical_mass instead.')
add('QSources','Network.symmetric_head_derivative',
'''∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x) (r : Row m) (head : Bool),
 HasFDerivAt (fun y : Vec n => if head then r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).1 else r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).2)
 (unified ((net.originalTrace x).stabilized (fun _ => 0) r head)) x''',
'Actual full balanced-input derivative of either projection head under strict internal gates; the new affine differentiable-head API handles ties.')
add('StabilizedBackward','MaskedTrace.stabilized_bulk',
'''∀ {n m : ℕ} (tr : MaskedTrace n m) (α : ℕ → ℝ) (r : Row m) (head : Bool),
 (tr.stabilized α r head).1 + (tr.stabilized α r head).2 = tr.bulkCoefficient α • (r.comp tr.absMap)''',
'Entire shifted selected-mask bulk, including the current and terminal shift factors, arbitrary varying widths.')
for name,block,sign in [('actual_positive_pullback','blockPP','(v,0)'),('actual_negative_pullback','blockPN','(0,v)')]:
 add('NetworkDerivative',name,
 f'''∀ {{n k : ℕ}} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n) (v : Vec n) (D : PairVec k →L[ℝ] ℝ),
 (D.comp (layerJac wp wn bp bn x)) {sign} = D ({block} wp wn bp bn x v,0) + D (0,matrixCLM {'wn' if sign=='(v,0)' else 'wp'} v)''',
 'Exact two-contribution pullback identity for the selected layer Jacobian; layer_derivative supplies its actual-derivative bridge under strict branch separation.')
add('StabilizedBackward','MaskedTrace.stabilized',
'''∀ {n m : ℕ}, MaskedTrace n m → (ℕ → ℝ) → Row m → Bool → Sensitivity n''',
'Recursive selected-mask algorithm: pull back the shifted tail and subtract the same local alpha multiple of the partial sum; terminal seed is also shifted. This is a definition, not a proposition.',kind='definition')
add('Network','Network.shift',
'''∀ {n m : ℕ} (net : Network n m) (p q c : Fin n → ℝ),
 net.split (p+c) (q+c) = ((net.split p q).1 + net.common c, (net.split p q).2 + net.common c)''',
'Actual whole-network common-shift equivariance with biases. common uses Wp+Wn; canonical sign parts identify the absolute-weight product.')
add('Chunks','maxpool_correct',
'''∀ {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι] (p n : ι → ℝ),
 Finset.univ.sup' Finset.univ_nonempty (fun j => p j + ∑ i ∈ Finset.univ.erase j, n i) - ∑ i, n i = Finset.univ.sup' Finset.univ_nonempty (fun j => p j-n j)''',
'Exact finite nonempty convex-pool difference identity; full output/shape properties are in maxpool_properties.',univ=['u'])
add('Sensitivities','monotone_directional_nonnegative',
'''∀ {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) (D : (Fin n → ℝ) →L[ℝ] ℝ)
 (hg : Monotone g) (hd : HasFDerivAt g D x) (hv : 0≤v), 0≤D v''',
'Actual derivative of an arbitrary differentiable coordinatewise-monotone function is nonnegative in every nonnegative direction; no subdifferential assertion.')
add('Decomposition','Network.valid_decomposition_recovery',
'''∀ {n m : ℕ} (net : Network n m) (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ)
 (hv : ValidPairActivation σ φ) (x : PairVec n),
 (net.decomposeWith φ x).1-(net.decomposeWith φ x).2 = net.forwardWith σ (x.1-x.2)''',
'Neuron-local scalar difference preservation gives full-network recovery using the same weights and biases. Positivity is separately established, not assumed by this algebraic theorem.')
add('Decomposition','Network.mixing_recovery',
'''∀ {n m : ℕ} (net : Network n m) (η : ℝ) (x : PairVec n),
 (net.decomposeWith (mixPair η) x).1-(net.decomposeWith (mixPair η) x).2 = net.eval (x.1-x.2)''',
'Exact actual mixing-network recovery for every real eta; stream positivity additionally needs eta in [0,1] and nonnegative parameters/inputs.')
add('Convexity','Network.convex',
'''∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
 (p q p' q' : Fin n → ℝ) (t : ℝ) (ht : 0≤t) (ht' : t≤1),
 (net.split (mix t p p') (mix t q q')).1 ≤ mix t (net.split p q).1 (net.split p' q').1 ∧
 (net.split (mix t p p') (mix t q q')).2 ≤ mix t (net.split p q).2 (net.split p' q').2''',
'Both actual split heads are globally Jensen convex in their split input pair with nonnegative split weights and arbitrary biases. General convex input-splitting composition is a separate scope item.')
add('Decomposition','Network.mixing_one_is_split',
'''∀ {n m : ℕ} (net : Network n m) (x : PairVec n), net.decomposeWith (mixPair 1) x = net.split x.1 x.2''',
'Literal full-network equality between the eta=1 mixing evaluator and the established DC split evaluator.')
add('Convexity','Network.monotone',
'''∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
 (p q p' q' : Fin n → ℝ) (hp : p≤p') (hq : q≤q'),
 (net.split p q).1 ≤ (net.split p' q').1 ∧ (net.split p q).2 ≤ (net.split p' q').2''',
'Actual pair-input monotonicity of both complete split heads, with nonnegative split weights and arbitrary biases.')
add('Network','layer_difference',
'''∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Fin k → ℝ) (p q : Fin n → ℝ),
 (fun i => max ((wp.mulVec p + wn.mulVec q + bp) i) ((wn.mulVec p + wp.mulVec q + bn) i)) -
 (wn.mulVec p + wp.mulVec q + bn) = (fun i => relu (((wp-wn).mulVec (p-q) + (bp-bn)) i))''',
'Biased rectangular ReLU-layer recovery; this is not an ungated affine/convolution theorem. linear_chunk_properties is the source-facing affine result.')
add('BlockedPaths','Network.gradient_blindness',
'''∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x) (j : Fin m) (i : Fin n)
 (hblocked : ∀ path : Thesis.BackwardGames.Paths (net.originalTrace x),
 PathConnected (net.originalTrace x) j i path → PathHasInactive (net.originalTrace x) path),
 ∃ U : Set (Vec n), IsOpen U ∧ x∈U ∧ ∀ y∈U, fderiv ℝ net.eval y (Pi.single i 1) j=0''',
'Zero actual derivative on an open neighborhood when every connected signed path is gated off. Fully activated backbone output coordinate and strict gates; affine final readout needs its explicit model bridge.')
add('NetworkDerivative','layer_derivative',
'''∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n)
 (hx : ∀ i, (preP wp wn x+bp) i ≠ (preN wp wn x+bn) i),
 HasFDerivAt (layerFun wp wn bp bn) (layerJac wp wn bp bn x) x''',
'Actual Frechet derivative of the split max/affine layer when all branch comparisons are strict; arbitrary weights and biases.')
add('FinitePolynomialWitness','MaxPolynomial.ordinary_finite_polynomial_witness',
'''∀ {ι : Type u} (e : MaxPolynomial ι), ∃ ps : List (MvPolynomial ι ℝ), ps≠[] ∧
 (∀ p∈ps, ∀ d : ι →₀ ℕ, 0≤p.coeff d) ∧
 ∀ x : ι → ℝ, 0≤x → e.eval x=foldMax (ps.map (MvPolynomial.eval x))''',
'An actual nonempty finite list of ordinary multivariate polynomials with nonnegative coefficients represents the max polynomial on the nonnegative orthant.',univ=['u'])
add('CircuitStatements','Circuit.maxout_multiplication_split_correct',
'''∀ {d n : ℕ} (c : Circuit d n) (x : Vec d) (i : Fin n),
 c.eval x i = (c.positiveExpressions.1 i).polynomialMaximum.eval (canonicalSplitInput x) -
 (c.positiveExpressions.2 i).polynomialMaximum.eval (canonicalSplitInput x)''',
'Actual shared-node signed arithmetic DAG recovered by two finite max-polynomial streams on canonical nonnegative split inputs. No tensor-index or complexity bound asserted.')
Path('reports/hidden-recheck-expected-types.json').write_text(json.dumps({'version':1,'targets':items},indent=2,ensure_ascii=False)+'\n')
s='\n'.join('import '+m for m in sorted({x['module'] for x in items}))+'\n'
for d in items:
 s+='\nnoncomputable section\n'
 if d['universes']:s+='universe '+' '.join(d['universes'])+'\n'
 s+='open HiddenMonotonicity\nopen scoped BigOperators\n'
 s+='example : '+d['expected_type']+' := @'+d['declaration']+'\n'
 s+='#check @'+d['declaration']+'\n#print axioms '+d['declaration']+'\nend\n'
Path('formalization/.lake/diagnostics/new-hidden-audit/OlderTypes.lean').write_text(s)
print(len(items))
