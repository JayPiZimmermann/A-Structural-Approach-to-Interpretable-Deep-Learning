import Thesis.TrajectoryHellinger

/- Independent type check for the equation linked from the thesis. -/
noncomputable section
open Finset Thesis.TrajectoryHellinger

example {S : ℕ → Type} [∀ n, Fintype (S n)]
    (A B : Kernel S) (s₀ : S 0) (n : ℕ)
    (hA : ∀ i < n, ∀ s t, 0 ≤ A i s t)
    (hB : ∀ i < n, ∀ s t, 0 ≤ B i s t)
    (hArow : ∀ i < n, ∀ s, ∑ t, A i s t = 1)
    (hBrow : ∀ i < n, ∀ s, ∑ t, B i s t = 1) :
    hellingerSquared (pathLaw A s₀ n) (pathLaw B s₀ n) =
      hellinger (pathLaw A s₀ n) (pathLaw B s₀ n) ^ 2 ∧
    hellinger (pathLaw A s₀ n) (pathLaw B s₀ n) ^ 2 = 1 - BC A B s₀ n ∧
    hellinger (pathLaw A s₀ n) (pathLaw B s₀ n) = Real.sqrt (1 - BC A B s₀ n) ∧
    hellinger (pathLaw A s₀ n) (pathLaw B s₀ n) =
      Real.sqrt (1 - ∑ s, g A B s₀ n s) :=
  trajectory_hellinger_recursion A B s₀ n hA hB hArow hBrow

#print axioms Thesis.TrajectoryHellinger.trajectory_hellinger_recursion
#print axioms Thesis.TrajectoryHellinger.prefix_marginal
#print axioms Thesis.TrajectoryHellinger.BC_eq_path_overlap
#print axioms Thesis.TrajectoryHellinger.common_start_distance
