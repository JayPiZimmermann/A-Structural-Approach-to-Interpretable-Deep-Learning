import Thesis.StoppingCircuit
import Thesis.StoppingPaths
import Thesis.StoppingRegions
set_option pp.universes true
set_option pp.explicit true

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hp : net.NonnegativeParameters) (r : Vec n),
 0≤frozenStopping net r 0 ∧ Monotone (stoppingJac (net.originalTrace r)) ∧
 (∀ x ∈ gateRegion net r, net.decomposeWith stopPair x = stoppingJac (net.originalTrace r) x + frozenStopping net r 0) ∧
 MonotoneOn (net.decomposeWith stopPair) (gateRegion net r) := @Thesis.StoppingStructure.stopping_region_nonnegative_affine
#check @Thesis.StoppingStructure.stopping_region_nonnegative_affine
#print axioms Thesis.StoppingStructure.stopping_region_nonnegative_affine
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (x : PairVec n),
 net.decomposeWith stopPair x = stoppingJac (net.originalTrace (x.1-x.2)) x + (biasSources net (x.1-x.2)).sum := @Thesis.StoppingStructure.stopping_input_and_bias_sources
#check @Thesis.StoppingStructure.stopping_input_and_bias_sources
#print axioms Thesis.StoppingStructure.stopping_input_and_bias_sources
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
example : ∀ {n m : ℕ} (tr : MaskedTrace n m) (i : Fin n) (path : GeometricPaths tr),
 geometricParity tr i path = decide (Odd (negativeEdgeCount tr i path)) := @Thesis.StoppingStructure.geometricParity_negative_count
#check @Thesis.StoppingStructure.geometricParity_negative_count
#print axioms Thesis.StoppingStructure.geometricParity_negative_count
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (hb : ZeroBias net) (x : PairVec n) (j : Fin m),
 let tr := net.originalTrace (x.1-x.2)
 (net.decomposeWith stopPair x).1 j = ∑ i, ∑ path : GeometricPaths tr,
 geometricWeight tr j i path * (if geometricParity tr i path then x.2 i else x.1 i) ∧
 (net.decomposeWith stopPair x).2 j = ∑ i, ∑ path : GeometricPaths tr,
 geometricWeight tr j i path * (if geometricParity tr i path then x.1 i else x.2 i) := @Thesis.StoppingStructure.stopping_activation_parity_paths
#check @Thesis.StoppingStructure.stopping_activation_parity_paths
#print axioms Thesis.StoppingStructure.stopping_activation_parity_paths
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
example : ∀ {n m k : ℕ} (net : Network n m) (hc : net.Canonical) (hb : ZeroBias net)
 (wp wn : Matrix (Fin k) (Fin m) ℝ)
 (hw : ∀ j i, wp j i=max (wp j i-wn j i) 0 ∧ wn j i=max (-(wp j i-wn j i)) 0)
 (x : PairVec n) (j : Fin k),
 let tr := preactivationTrace net (x.1-x.2) wp wn
 preP wp wn (net.decomposeWith stopPair x) j = ∑ i, ∑ path : GeometricPaths tr,
 geometricWeight tr j i path * (if geometricParity tr i path then x.2 i else x.1 i) ∧
 preN wp wn (net.decomposeWith stopPair x) j = ∑ i, ∑ path : GeometricPaths tr,
 geometricWeight tr j i path * (if geometricParity tr i path then x.1 i else x.2 i) := @Thesis.StoppingStructure.stopping_preactivation_parity_paths
#check @Thesis.StoppingStructure.stopping_preactivation_parity_paths
#print axioms Thesis.StoppingStructure.stopping_preactivation_parity_paths
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingStructure
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : PairVec n) (j : Fin m),
 let tr := net.originalTrace (x.1-x.2)
 (net.decomposeWith stopPair x).1 j =
 (∑ i, ∑ path : GeometricPaths tr, geometricWeight tr j i path * (if geometricParity tr i path then x.2 i else x.1 i)) + ((biasSources net (x.1-x.2)).sum).1 j ∧
 (net.decomposeWith stopPair x).2 j =
 (∑ i, ∑ path : GeometricPaths tr, geometricWeight tr j i path * (if geometricParity tr i path then x.1 i else x.2 i)) + ((biasSources net (x.1-x.2)).sum).2 j := @Thesis.StoppingStructure.stopping_biased_parity_paths
#check @Thesis.StoppingStructure.stopping_biased_parity_paths
#print axioms Thesis.StoppingStructure.stopping_biased_parity_paths
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
example : ∀ {n : ℕ} (a : SignedExpr (Fin n)) (x : PairVec n),
 stoppingExpr (.maximum a (.constant 0)) x = stopPair (stoppingExpr a x) := @Thesis.StoppingCircuit.stoppingExpr_relu
#check @Thesis.StoppingCircuit.stoppingExpr_relu
#print axioms Thesis.StoppingCircuit.stoppingExpr_relu
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
example : ∀ {d n : ℕ} (c : Circuit d n) (x : PairVec d),
 (stoppingCircuit c x).1-(stoppingCircuit c x).2 = c.eval (x.1-x.2) := @Thesis.StoppingCircuit.stoppingCircuit_recovery
#check @Thesis.StoppingCircuit.stoppingCircuit_recovery
#print axioms Thesis.StoppingCircuit.stoppingCircuit_recovery
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
example : ∀ {d n : ℕ} (c : Circuit d n) (x : PairVec d) (hx : 0≤x),
 0≤stoppingCircuit c x := @Thesis.StoppingCircuit.stoppingCircuit_nonnegative
#check @Thesis.StoppingCircuit.stoppingCircuit_nonnegative
#print axioms Thesis.StoppingCircuit.stoppingCircuit_nonnegative
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
example : (∀ b, 0≤additionProbability b) ∧ (∑ b : Bool, additionProbability b)=1 := @Thesis.StoppingCircuit.addition_probability_law
#check @Thesis.StoppingCircuit.addition_probability_law
#print axioms Thesis.StoppingCircuit.addition_probability_law
end

noncomputable section
universe u
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
example : ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
 (f g : E → ℝ) (Df Dg : E →L[ℝ] ℝ) (x : E)
 (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x),
 HasFDerivAt (fun y => f y+g y) ((2 : ℝ) • (additionProbability false • Df+additionProbability true • Dg)) x := @Thesis.StoppingCircuit.addition_derivative_occupation
#check @Thesis.StoppingCircuit.addition_derivative_occupation
#print axioms Thesis.StoppingCircuit.addition_derivative_occupation
end

noncomputable section
universe u
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
example : ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
 (f g : E → ℝ × ℝ) (Df Dg : E →L[ℝ] ℝ × ℝ) (x : E)
 (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
 (hne : (f x).1-(f x).2 ≠ (g x).1-(g x).2),
 HasFDerivAt (fun y => winnerPair (g y) (f y))
 (if (g x).1-(g x).2 < (f x).1-(f x).2 then Df else Dg) x := @Thesis.StoppingCircuit.winner_derivative
#check @Thesis.StoppingCircuit.winner_derivative
#print axioms Thesis.StoppingCircuit.winner_derivative
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
example : ∀ (leftWins : Bool),
 (∀ b,0≤winnerProbability leftWins b) ∧ (∑ b : Bool,winnerProbability leftWins b)=1 := @Thesis.StoppingCircuit.winner_probability_law
#check @Thesis.StoppingCircuit.winner_probability_law
#print axioms Thesis.StoppingCircuit.winner_probability_law
end

noncomputable section
open HiddenMonotonicity Thesis.StoppingDecomposition Thesis.StoppingCircuit
open scoped BigOperators
example : ∀ (leftWins : Bool) (left right : ℝ),
 (1 : ℝ)*(winnerProbability leftWins true*left+winnerProbability leftWins false*right) = if leftWins then left else right := @Thesis.StoppingCircuit.winner_discounted_occupation
#check @Thesis.StoppingCircuit.winner_discounted_occupation
#print axioms Thesis.StoppingCircuit.winner_discounted_occupation
end

noncomputable section
universe u
open HiddenMonotonicity Thesis.StoppingCircuit
open scoped BigOperators
example : ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
 (f g : E → ℝ × ℝ) (Df Dg : E →L[ℝ] ℝ × ℝ) (x : E)
 (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
 (hne : (f x).1-(f x).2 ≠ (g x).1-(g x).2),
 HasFDerivAt (fun y => winnerPair (g y) (f y))
 ((1 : ℝ) • (winnerProbability (decide ((g x).1-(g x).2 < (f x).1-(f x).2)) true • Df +
 winnerProbability (decide ((g x).1-(g x).2 < (f x).1-(f x).2)) false • Dg)) x := @Thesis.StoppingCircuit.winner_derivative_occupation
#check @Thesis.StoppingCircuit.winner_derivative_occupation
#print axioms Thesis.StoppingCircuit.winner_derivative_occupation
end
