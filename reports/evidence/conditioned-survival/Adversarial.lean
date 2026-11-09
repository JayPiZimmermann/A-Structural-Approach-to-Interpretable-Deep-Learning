import Thesis.ConditionedSurvival

noncomputable section
open Thesis.Games Thesis.ConditionedSurvival

namespace SurvivalReview

/-- A two-step example. Half of the first step enters a state whose entire
next row is dead, while the other half survives with probability one. -/
def K (i : ℕ) (s t : Bool) : ℝ :=
  if i = 0 then 1/2 else if i = 1 ∧ s = false ∧ t = false then 1 else 0

example : ∀ i s t, 0 ≤ K i s t := by
  intro i s t
  unfold K
  split_ifs <;> norm_num

example : ∀ i s, ∑ t, K i s t ≤ 1 := by
  intro i s
  cases s <;> simp only [Fintype.sum_bool, K]
  all_goals split_ifs <;> norm_num at *

example : survival 2 K 0 false = 1/2 ∧
    survival 2 K 1 false = 1 ∧ survival 2 K 1 true = 0 := by
  norm_num [survival, backwardDP, K, Fintype.sum_bool, Finset.filter_insert, Finset.filter_singleton]

example : pathLaw 1 K false (true, ()) = 1/2 ∧
    kernel K (survival 2 K) 0 false true = 0 ∧
    kernel K (survival 2 K) 0 false false = 1 := by
  norm_num [kernel, survival, backwardDP, pathLaw, K, Fintype.sum_bool,
    Finset.filter_insert, Finset.filter_singleton]

example : pathLaw 2 (kernel K (survival 2 K)) false (false,false,()) = 1 ∧
    pathLaw 2 (kernel K (survival 2 K)) false (true,false,()) = 0 ∧
    pathLaw 2 K false (false,false,()) = 1/2 := by
  norm_num [kernel, survival, backwardDP, pathLaw, K, Fintype.sum_bool,
    Finset.filter_insert, Finset.filter_singleton]

example : kernel K (survival 2 K) 1 true false = 0 ∧
    kernel K (survival 2 K) 1 true true = 0 := by
  norm_num [kernel, survival, backwardDP, K, Fintype.sum_bool]

end SurvivalReview
