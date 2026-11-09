import HiddenMonotonicity.BlockedPaths
import HiddenMonotonicity.Chunks
import HiddenMonotonicity.CircuitStatements
import HiddenMonotonicity.Convexity
import HiddenMonotonicity.Decomposition
import HiddenMonotonicity.FinitePolynomialWitness
import HiddenMonotonicity.Network
import HiddenMonotonicity.NetworkDerivative
import HiddenMonotonicity.OriginalTrace
import HiddenMonotonicity.QSources
import HiddenMonotonicity.Sensitivities
import HiddenMonotonicity.StabilizedBackward

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ (w : ℝ), max w 0 - max (-w) 0 = w ∧ max w 0 + max (-w) 0 = |w| := @HiddenMonotonicity.canonical_weight_split
#check @HiddenMonotonicity.canonical_weight_split
#print axioms HiddenMonotonicity.canonical_weight_split
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : PairVec n) (r : Row m) (head : Bool),
 ((net.trace x).stabilized (fun _ => 0) r head).1 + ((net.trace x).stabilized (fun _ => 0) r head).2 = r.comp net.absoluteMap := @HiddenMonotonicity.Network.sensitivity_complementarity_absolute
#check @HiddenMonotonicity.Network.sensitivity_complementarity_absolute
#print axioms HiddenMonotonicity.Network.sensitivity_complementarity_absolute
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x) (r : Row m) (head : Bool),
 HasFDerivAt (fun y : Vec n => if head then r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).1 else r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).2)
 (unified ((net.originalTrace x).stabilized (fun _ => 0) r head)) x := @HiddenMonotonicity.Network.symmetric_head_derivative
#check @HiddenMonotonicity.Network.symmetric_head_derivative
#print axioms HiddenMonotonicity.Network.symmetric_head_derivative
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (tr : MaskedTrace n m) (α : ℕ → ℝ) (r : Row m) (head : Bool),
 (tr.stabilized α r head).1 + (tr.stabilized α r head).2 = tr.bulkCoefficient α • (r.comp tr.absMap) := @HiddenMonotonicity.MaskedTrace.stabilized_bulk
#check @HiddenMonotonicity.MaskedTrace.stabilized_bulk
#print axioms HiddenMonotonicity.MaskedTrace.stabilized_bulk
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n) (v : Vec n) (D : PairVec k →L[ℝ] ℝ),
 (D.comp (layerJac wp wn bp bn x)) (v,0) = D (blockPP wp wn bp bn x v,0) + D (0,matrixCLM wn v) := @HiddenMonotonicity.actual_positive_pullback
#check @HiddenMonotonicity.actual_positive_pullback
#print axioms HiddenMonotonicity.actual_positive_pullback
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n) (v : Vec n) (D : PairVec k →L[ℝ] ℝ),
 (D.comp (layerJac wp wn bp bn x)) (0,v) = D (blockPN wp wn bp bn x v,0) + D (0,matrixCLM wp v) := @HiddenMonotonicity.actual_negative_pullback
#check @HiddenMonotonicity.actual_negative_pullback
#print axioms HiddenMonotonicity.actual_negative_pullback
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ}, MaskedTrace n m → (ℕ → ℝ) → Row m → Bool → Sensitivity n := @HiddenMonotonicity.MaskedTrace.stabilized
#check @HiddenMonotonicity.MaskedTrace.stabilized
#print axioms HiddenMonotonicity.MaskedTrace.stabilized
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (p q c : Fin n → ℝ),
 net.split (p+c) (q+c) = ((net.split p q).1 + net.common c, (net.split p q).2 + net.common c) := @HiddenMonotonicity.Network.shift
#check @HiddenMonotonicity.Network.shift
#print axioms HiddenMonotonicity.Network.shift
end

noncomputable section
universe u
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι] (p n : ι → ℝ),
 Finset.univ.sup' Finset.univ_nonempty (fun j => p j + ∑ i ∈ Finset.univ.erase j, n i) - ∑ i, n i = Finset.univ.sup' Finset.univ_nonempty (fun j => p j-n j) := @HiddenMonotonicity.maxpool_correct
#check @HiddenMonotonicity.maxpool_correct
#print axioms HiddenMonotonicity.maxpool_correct
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) (D : (Fin n → ℝ) →L[ℝ] ℝ)
 (hg : Monotone g) (hd : HasFDerivAt g D x) (hv : 0≤v), 0≤D v := @HiddenMonotonicity.monotone_directional_nonnegative
#check @HiddenMonotonicity.monotone_directional_nonnegative
#print axioms HiddenMonotonicity.monotone_directional_nonnegative
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ)
 (hv : ValidPairActivation σ φ) (x : PairVec n),
 (net.decomposeWith φ x).1-(net.decomposeWith φ x).2 = net.forwardWith σ (x.1-x.2) := @HiddenMonotonicity.Network.valid_decomposition_recovery
#check @HiddenMonotonicity.Network.valid_decomposition_recovery
#print axioms HiddenMonotonicity.Network.valid_decomposition_recovery
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (η : ℝ) (x : PairVec n),
 (net.decomposeWith (mixPair η) x).1-(net.decomposeWith (mixPair η) x).2 = net.eval (x.1-x.2) := @HiddenMonotonicity.Network.mixing_recovery
#check @HiddenMonotonicity.Network.mixing_recovery
#print axioms HiddenMonotonicity.Network.mixing_recovery
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
 (p q p' q' : Fin n → ℝ) (t : ℝ) (ht : 0≤t) (ht' : t≤1),
 (net.split (mix t p p') (mix t q q')).1 ≤ mix t (net.split p q).1 (net.split p' q').1 ∧
 (net.split (mix t p p') (mix t q q')).2 ≤ mix t (net.split p q).2 (net.split p' q').2 := @HiddenMonotonicity.Network.convex
#check @HiddenMonotonicity.Network.convex
#print axioms HiddenMonotonicity.Network.convex
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (x : PairVec n), net.decomposeWith (mixPair 1) x = net.split x.1 x.2 := @HiddenMonotonicity.Network.mixing_one_is_split
#check @HiddenMonotonicity.Network.mixing_one_is_split
#print axioms HiddenMonotonicity.Network.mixing_one_is_split
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative)
 (p q p' q' : Fin n → ℝ) (hp : p≤p') (hq : q≤q'),
 (net.split p q).1 ≤ (net.split p' q').1 ∧ (net.split p q).2 ≤ (net.split p' q').2 := @HiddenMonotonicity.Network.monotone
#check @HiddenMonotonicity.Network.monotone
#print axioms HiddenMonotonicity.Network.monotone
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Fin k → ℝ) (p q : Fin n → ℝ),
 (fun i => max ((wp.mulVec p + wn.mulVec q + bp) i) ((wn.mulVec p + wp.mulVec q + bn) i)) -
 (wn.mulVec p + wp.mulVec q + bn) = (fun i => relu (((wp-wn).mulVec (p-q) + (bp-bn)) i)) := @HiddenMonotonicity.layer_difference
#check @HiddenMonotonicity.layer_difference
#print axioms HiddenMonotonicity.layer_difference
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x) (j : Fin m) (i : Fin n)
 (hblocked : ∀ path : Thesis.BackwardGames.Paths (net.originalTrace x),
 PathConnected (net.originalTrace x) j i path → PathHasInactive (net.originalTrace x) path),
 ∃ U : Set (Vec n), IsOpen U ∧ x∈U ∧ ∀ y∈U, fderiv ℝ net.eval y (Pi.single i 1) j=0 := @HiddenMonotonicity.Network.gradient_blindness
#check @HiddenMonotonicity.Network.gradient_blindness
#print axioms HiddenMonotonicity.Network.gradient_blindness
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n)
 (hx : ∀ i, (preP wp wn x+bp) i ≠ (preN wp wn x+bn) i),
 HasFDerivAt (layerFun wp wn bp bn) (layerJac wp wn bp bn x) x := @HiddenMonotonicity.layer_derivative
#check @HiddenMonotonicity.layer_derivative
#print axioms HiddenMonotonicity.layer_derivative
end

noncomputable section
universe u
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {ι : Type u} (e : MaxPolynomial ι), ∃ ps : List (MvPolynomial ι ℝ), ps≠[] ∧
 (∀ p∈ps, ∀ d : ι →₀ ℕ, 0≤p.coeff d) ∧
 ∀ x : ι → ℝ, 0≤x → e.eval x=foldMax (ps.map (MvPolynomial.eval x)) := @HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness
#check @HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness
#print axioms HiddenMonotonicity.MaxPolynomial.ordinary_finite_polynomial_witness
end

noncomputable section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {d n : ℕ} (c : Circuit d n) (x : Vec d) (i : Fin n),
 c.eval x i = (c.positiveExpressions.1 i).polynomialMaximum.eval (canonicalSplitInput x) -
 (c.positiveExpressions.2 i).polynomialMaximum.eval (canonicalSplitInput x) := @HiddenMonotonicity.Circuit.maxout_multiplication_split_correct
#check @HiddenMonotonicity.Circuit.maxout_multiplication_split_correct
#print axioms HiddenMonotonicity.Circuit.maxout_multiplication_split_correct
end
