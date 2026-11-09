import Thesis.Tropical
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Constructions

/-! Finite discounted Markov decision processes, genuine contraction proofs,
unique Bellman solutions, and pure stationary greedy optimality. -/
noncomputable section
namespace Thesis.Bellman
open Finset Thesis.Tropical
open scoped Topology NNReal
variable {S A : Type} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]

structure MDP (S A : Type) [Fintype S] where
  discount : ℝ≥0
  discount_lt_one : discount < 1
  reward : S → A → ℝ
  transition : S → A → S → ℝ
  nonnegative : ∀ s a t, 0 ≤ transition s a t
  normalized : ∀ s a, ∑ t, transition s a t = 1

structure Policy (S A : Type) [Fintype A] where
  probability : S → A → ℝ
  nonnegative : ∀ s a, 0 ≤ probability s a
  normalized : ∀ s, ∑ a, probability s a = 1

def pure (choice : S → A) : Policy S A := by
  classical
  exact ⟨fun s a => if a = choice s then 1 else 0,
    fun _ _ => by split_ifs <;> norm_num,fun _ => by simp⟩

def MDP.action (M : MDP S A) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  M.reward s a + M.discount * ∑ t, M.transition s a t * v t

def MDP.bellman (M : MDP S A) (v : S → ℝ) (s : S) : ℝ :=
  finiteMax (M.action v s)

def MDP.policyBellman (M : MDP S A) (π : Policy S A) (v : S → ℝ) (s : S) : ℝ :=
  ∑ a, π.probability s a * M.action v s a

theorem MDP.action_bound (M : MDP S A) (v w : S → ℝ) (s : S) (a : A) :
    |M.action v s a-M.action w s a| ≤ M.discount*‖v-w‖ := by
  have he : M.action v s a-M.action w s a =
      M.discount * ∑ t, M.transition s a t*(v t-w t) := by
    simp only [action,mul_sub,sum_sub_distrib]
    ring
  rw [he,abs_mul,abs_of_nonneg M.discount.coe_nonneg]
  apply mul_le_mul_of_nonneg_left _ M.discount.coe_nonneg
  calc
    |∑ t, M.transition s a t*(v t-w t)| ≤ ∑ t, |M.transition s a t*(v t-w t)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, M.transition s a t*‖v-w‖ := by
      apply sum_le_sum
      intro t _
      rw [abs_mul,abs_of_nonneg (M.nonnegative s a t)]
      apply mul_le_mul_of_nonneg_left _ (M.nonnegative s a t)
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (v-w) t
    _ = ‖v-w‖ := by rw [← sum_mul,M.normalized,one_mul]

theorem max_difference_bound (f g : A → ℝ) (c : ℝ) (h : ∀ a, |f a-g a| ≤ c) :
    |finiteMax f-finiteMax g| ≤ c := by
  apply abs_le.mpr
  constructor
  · obtain ⟨a,ha⟩ := finiteMax_attained g
    have hbound := (abs_le.mp (h a)).1
    have hmax := le_finiteMax f a
    rw [ha]
    linarith
  · obtain ⟨a,ha⟩ := finiteMax_attained f
    have hbound := (abs_le.mp (h a)).2
    have hmax := le_finiteMax g a
    rw [ha]
    linarith

/-- The Bellman maximum is a discount contraction in the sup norm. -/
theorem MDP.bellman_contracting (M : MDP S A) : ContractingWith M.discount M.bellman := by
  refine ⟨M.discount_lt_one,LipschitzWith.of_dist_le_mul ?_⟩
  intro v w
  simp only [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg M.discount.coe_nonneg (norm_nonneg _))).mpr
  intro s
  change |M.bellman v s-M.bellman w s| ≤ _
  exact max_difference_bound _ _ _ (M.action_bound v w s)

/-- Every randomized policy evaluation operator has the same contraction constant. -/
theorem MDP.policyBellman_contracting (M : MDP S A) (π : Policy S A) :
    ContractingWith M.discount (M.policyBellman π) := by
  refine ⟨M.discount_lt_one,LipschitzWith.of_dist_le_mul ?_⟩
  intro v w
  simp only [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg M.discount.coe_nonneg (norm_nonneg _))).mpr
  intro s
  change |M.policyBellman π v s-M.policyBellman π w s| ≤ _
  have he : M.policyBellman π v s-M.policyBellman π w s =
      ∑ a, π.probability s a*(M.action v s a-M.action w s a) := by
    simp only [policyBellman,mul_sub,sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ a, |π.probability s a*(M.action v s a-M.action w s a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, π.probability s a*(M.discount*‖v-w‖) := by
      apply sum_le_sum
      intro a _
      rw [abs_mul,abs_of_nonneg (π.nonnegative s a)]
      exact mul_le_mul_of_nonneg_left (M.action_bound v w s a) (π.nonnegative s a)
    _ = _ := by rw [← sum_mul,π.normalized,one_mul]

def MDP.optimalValue (M : MDP S A) : S → ℝ := M.bellman_contracting.fixedPoint M.bellman

def MDP.policyValue (M : MDP S A) (π : Policy S A) : S → ℝ :=
  (M.policyBellman_contracting π).fixedPoint (M.policyBellman π)

theorem MDP.optimal_fixed (M : MDP S A) : M.bellman M.optimalValue = M.optimalValue :=
  M.bellman_contracting.fixedPoint_isFixedPt

theorem MDP.policy_fixed (M : MDP S A) (π : Policy S A) :
    M.policyBellman π (M.policyValue π) = M.policyValue π :=
  (M.policyBellman_contracting π).fixedPoint_isFixedPt

/-- Uniqueness is proved by Banach's theorem on the finite-dimensional complete space. -/
theorem MDP.optimal_unique (M : MDP S A) (v : S → ℝ) (h : M.bellman v = v) : v = M.optimalValue :=
  M.bellman_contracting.fixedPoint_unique h

theorem MDP.policy_unique (M : MDP S A) (π : Policy S A) (v : S → ℝ)
    (h : M.policyBellman π v = v) : v = M.policyValue π :=
  (M.policyBellman_contracting π).fixedPoint_unique h

theorem MDP.action_mono (M : MDP S A) {v w : S → ℝ} (h : v ≤ w) (s : S) (a : A) :
    M.action v s a ≤ M.action w s a := by
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ M.discount.coe_nonneg
  exact sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h t) (M.nonnegative s a t)

theorem MDP.policyBellman_mono (M : MDP S A) (π : Policy S A) : Monotone (M.policyBellman π) := by
  intro v w h s
  exact sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (M.action_mono h s a) (π.nonnegative s a)

theorem MDP.policyBellman_le (M : MDP S A) (π : Policy S A) (v : S → ℝ) :
    M.policyBellman π v ≤ M.bellman v := by
  intro s
  calc
    _ ≤ ∑ a, π.probability s a*M.bellman v s :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (le_finiteMax (M.action v s) a) (π.nonnegative s a)
    _ = _ := by rw [← sum_mul,π.normalized,one_mul]

theorem MDP.action_shift (M : MDP S A) (v : S → ℝ) (c : ℝ) (s : S) (a : A) :
    M.action (fun t => v t+c) s a = M.action v s a+M.discount*c := by
  simp only [action,mul_add,sum_add_distrib,← sum_mul,M.normalized,one_mul]
  ring

theorem MDP.policyBellman_shift (M : MDP S A) (π : Policy S A) (v : S → ℝ) (c : ℝ) :
    M.policyBellman π (fun s => v s+c) = fun s => M.policyBellman π v s+M.discount*c := by
  funext s
  simp only [policyBellman,M.action_shift,mul_add,sum_add_distrib,← sum_mul,π.normalized,one_mul]

/-- No stationary randomized policy exceeds the optimal Bellman solution. -/
theorem MDP.policy_le_optimal (M : MDP S A) (π : Policy S A) : M.policyValue π ≤ M.optimalValue := by
  let δ := finiteMax (fun s => M.policyValue π s-M.optimalValue s)
  obtain ⟨s,hs⟩ := finiteMax_attained (fun s => M.policyValue π s-M.optimalValue s)
  have hbound : M.policyValue π ≤ fun t => M.optimalValue t+δ := by
    intro t
    have ht := le_finiteMax (fun s => M.policyValue π s-M.optimalValue s) t
    change _ ≤ δ at ht
    linarith
  have hstep := M.policyBellman_mono π hbound s
  rw [M.policy_fixed,M.policyBellman_shift] at hstep
  have hopt := M.policyBellman_le π M.optimalValue s
  rw [M.optimal_fixed] at hopt
  have hγ : (M.discount : ℝ) < 1 := M.discount_lt_one
  have hδ : δ ≤ 0 := by
    change δ = _ at hs
    nlinarith
  intro t
  have ht := le_finiteMax (fun s => M.policyValue π s-M.optimalValue s) t
  change _ ≤ δ at ht
  linarith

def MDP.greedy (M : MDP S A) : S → A := fun s =>
  Classical.choose (finiteMax_attained (M.action M.optimalValue s))

theorem MDP.greedy_value (M : MDP S A) (s : S) :
    M.action M.optimalValue s (M.greedy s) = M.optimalValue s := by
  have h := Classical.choose_spec (finiteMax_attained (M.action M.optimalValue s))
  exact h.symm.trans (congrFun M.optimal_fixed s)

theorem MDP.policyBellman_pure (M : MDP S A) (choice : S → A) (v : S → ℝ) (s : S) :
    M.policyBellman (pure choice) v s = M.action v s (choice s) := by
  classical
  simp [policyBellman,pure]

/-- Any pure policy greedy for the optimal solution is optimal, including arbitrary ties. -/
theorem MDP.greedy_policy_optimal (M : MDP S A) (choice : S → A)
    (h : ∀ s, M.action M.optimalValue s (choice s) = M.optimalValue s) :
    M.policyValue (pure choice) = M.optimalValue := by
  apply Eq.symm
  apply M.policy_unique
  funext s
  rw [M.policyBellman_pure,h]

/-- prop:bellman, existence of an optimal pure stationary policy and domination
of all randomized stationary policies. -/
theorem MDP.bellman_optimality (M : MDP S A) :
    M.policyValue (pure M.greedy) = M.optimalValue ∧
      ∀ π : Policy S A, M.policyValue π ≤ M.policyValue (pure M.greedy) := by
  have h := M.greedy_policy_optimal M.greedy M.greedy_value
  exact ⟨h,fun π => h ▸ M.policy_le_optimal π⟩

end Thesis.Bellman
