import Thesis.GeneralRegularization
set_option pp.explicit true
set_option pp.universes true

noncomputable section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
example : ∀ (R : Regularizer) (z : ℝ), ∃ p ∈ Icc (0 : ℝ) 1, IsMaxOn (objective R z) (Icc 0 1) p := @Thesis.GeneralRegularization.exists_optimizer
#check @Thesis.GeneralRegularization.exists_optimizer
#print axioms Thesis.GeneralRegularization.exists_optimizer
end

noncomputable section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
example : ∀ (R : Regularizer) (z : ℝ), IsGreatest ((objective R z) '' Icc (0 : ℝ) 1) (activation R z) := @Thesis.GeneralRegularization.activation_isGreatest
#check @Thesis.GeneralRegularization.activation_isGreatest
#print axioms Thesis.GeneralRegularization.activation_isGreatest
end

noncomputable section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
example : ∀ (R : Regularizer) (π : ℝ → ℝ) (hπ : ∀ z, π z ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (objective R z) (Icc 0 1) (π z)) {n m k : ℕ} (net : Network n m) (x : PairVec n) (wp wn : Matrix (Fin k) (Fin m) ℝ) (bp bn : Vec k), ValidPairActivation (activation R) (pairWith R π) ∧ NonnegativePairActivation (pairWith R π) ∧ ConvexOn ℝ univ (activation R) ∧ Monotone (activation R) ∧ LipschitzWith 1 (activation R) ∧ (∀ z, DifferentiableAt ℝ (activation R) z → π z = deriv (activation R) z) ∧ (preP wp wn (net.decomposeWith (pairWith R π) x)+bp - (preN wp wn (net.decomposeWith (pairWith R π) x)+bn) = affineLayer wp wn bp bn (net.forwardWith (activation R) (x.1-x.2))) := @Thesis.GeneralRegularization.regularized_decomposition_validity
#check @Thesis.GeneralRegularization.regularized_decomposition_validity
#print axioms Thesis.GeneralRegularization.regularized_decomposition_validity
end

noncomputable section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
example : ∀ z : ℝ, activation zeroRegularizer z = relu z := @Thesis.GeneralRegularization.zero_activation
#check @Thesis.GeneralRegularization.zero_activation
#print axioms Thesis.GeneralRegularization.zero_activation
end

noncomputable section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
example : pairWith zeroRegularizer hardGate = Thesis.StoppingDecomposition.stopPair := @Thesis.GeneralRegularization.zero_pair_is_stopping
#check @Thesis.GeneralRegularization.zero_pair_is_stopping
#print axioms Thesis.GeneralRegularization.zero_pair_is_stopping
end

noncomputable section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
example : ∀ (θ : ℝ) (hθ : 0 < θ) (z : ℝ), Thesis.Regularization.gate θ z ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (objective (entropyRegularizer θ hθ) z) (Icc 0 1) (Thesis.Regularization.gate θ z) := @Thesis.GeneralRegularization.sigmoid_optimal
#check @Thesis.GeneralRegularization.sigmoid_optimal
#print axioms Thesis.GeneralRegularization.sigmoid_optimal
end

noncomputable section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
example : ∀ (θ : ℝ) (hθ : 0 < θ) (z : ℝ), activation (entropyRegularizer θ hθ) z = Thesis.Regularization.softplus θ z := @Thesis.GeneralRegularization.entropy_activation
#check @Thesis.GeneralRegularization.entropy_activation
#print axioms Thesis.GeneralRegularization.entropy_activation
end

noncomputable section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
example : ∀ (θ : ℝ) (hθ : 0 < θ) (z : ℝ × ℝ), pairWith (entropyRegularizer θ hθ) (Thesis.Regularization.gate θ) z = Thesis.Regularization.softSplit θ z.1 z.2 := @Thesis.GeneralRegularization.entropy_pair_is_softSplit
#check @Thesis.GeneralRegularization.entropy_pair_is_softSplit
#print axioms Thesis.GeneralRegularization.entropy_pair_is_softSplit
end
