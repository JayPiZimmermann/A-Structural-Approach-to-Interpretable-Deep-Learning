import Thesis.Bellman
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! The Bellman policy fixed point equals the convergent discounted Markov reward
series. Thus fixed points are identified with actual expected returns, rather than
using the Bellman equation itself as the definition of a return. -/
noncomputable section
namespace Thesis.Bellman
open Finset Matrix Filter
open scoped Topology NNReal
variable {S A : Type} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]

def MDP.policyReward (M : MDP S A) (π : Policy S A) : S → ℝ :=
  fun s => ∑ a, π.probability s a*M.reward s a

def MDP.policyTransition (M : MDP S A) (π : Policy S A) : Matrix S S ℝ :=
  fun s t => ∑ a, π.probability s a*M.transition s a t

theorem MDP.policyTransition_nonnegative (M : MDP S A) (π : Policy S A) (s t : S) :
    0 ≤ M.policyTransition π s t :=
  sum_nonneg fun a _ => mul_nonneg (π.nonnegative s a) (M.nonnegative s a t)

theorem MDP.policyTransition_normalized (M : MDP S A) (π : Policy S A) (s : S) :
    ∑ t, M.policyTransition π s t = 1 := by
  unfold policyTransition
  rw [sum_comm]
  simp only [← mul_sum,M.normalized,mul_one,π.normalized]

/-- One-step expectation of a continuation reward under the induced Markov chain. -/
def MDP.markovOperator (M : MDP S A) (π : Policy S A) : (S → ℝ) →ₗ[ℝ] (S → ℝ) :=
  (M.policyTransition π).mulVecLin

def MDP.discountedOperator (M : MDP S A) (π : Policy S A) : (S → ℝ) →ₗ[ℝ] (S → ℝ) :=
  (M.discount : ℝ) • M.markovOperator π

theorem MDP.policyBellman_affine (M : MDP S A) (π : Policy S A) (v : S → ℝ) :
    M.policyBellman π v = M.policyReward π+M.discountedOperator π v := by
  funext s
  simp only [policyBellman,action,mul_add,sum_add_distrib,policyReward,
    discountedOperator,markovOperator,LinearMap.smul_apply,Matrix.mulVecLin_apply,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,policyTransition]
  congr 1
  simp_rw [sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro t _
  ring

/-- The discounted Markov operator has sup-norm at most γ. -/
theorem MDP.discountedOperator_bound (M : MDP S A) (π : Policy S A) (v : S → ℝ) :
    ‖M.discountedOperator π v‖ ≤ M.discount*‖v‖ := by
  have h := (M.policyBellman_contracting π).toLipschitzWith.dist_le_mul v 0
  rw [M.policyBellman_affine,M.policyBellman_affine,map_zero] at h
  simpa only [dist_eq_norm,add_zero,add_sub_cancel_left,sub_zero] using h

/-- Uniform geometric bound on the expected discounted reward at time n. -/
theorem MDP.iterated_reward_bound (M : MDP S A) (π : Policy S A) (n : ℕ) :
    ‖(M.discountedOperator π)^[n] (M.policyReward π)‖ ≤
      (M.discount : ℝ)^n*‖M.policyReward π‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (M.discountedOperator_bound π _).trans (by
        simpa [pow_succ',mul_assoc] using mul_le_mul_of_nonneg_left ih M.discount.coe_nonneg)

theorem MDP.reward_series_summable (M : MDP S A) (π : Policy S A) :
    Summable (fun n => (M.discountedOperator π)^[n] (M.policyReward π)) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one M.discount.coe_nonneg M.discount_lt_one).mul_right ‖M.policyReward π‖)
  exact M.iterated_reward_bound π

/-- Finite-horizon expected return equals the finite sum of discounted stage rewards. -/
theorem MDP.truncated_return (M : MDP S A) (π : Policy S A) (n : ℕ) :
    (M.policyBellman π)^[n] 0 = ∑ t ∈ range n,
      (M.discountedOperator π)^[t] (M.policyReward π) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply',M.policyBellman_affine,ih,map_sum,sum_range_succ']
      simp only [Function.iterate_succ_apply',Function.iterate_zero, id_eq]
      exact add_comm _ _

theorem MDP.discounted_iterate (M : MDP S A) (π : Policy S A) (n : ℕ) (v : S → ℝ) :
    (M.discountedOperator π)^[n] v = (M.discount : ℝ)^n • (M.markovOperator π)^[n] v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [discountedOperator,LinearMap.smul_apply,map_smul,smul_smul,
        pow_succ',Function.iterate_succ_apply']
      rw [mul_comm]

/-- prop:bellman evaluation value is the actual Neumann/expected-return series,
including randomized stationary policies and arbitrary bounded finite rewards. -/
theorem MDP.expected_return_hasSum (M : MDP S A) (π : Policy S A) :
    HasSum (fun n => (M.discount : ℝ)^n • (M.markovOperator π)^[n] (M.policyReward π))
      (M.policyValue π) := by
  have hs := M.reward_series_summable π
  have ht := (M.policyBellman_contracting π).tendsto_iterate_fixedPoint (0 : S → ℝ)
  have he : (fun n => (M.policyBellman π)^[n] 0) =
      fun n => ∑ t ∈ range n, (M.discountedOperator π)^[t] (M.policyReward π) :=
    funext (M.truncated_return π)
  rw [he] at ht
  have hh : HasSum (fun n => (M.discountedOperator π)^[n] (M.policyReward π))
      (M.policyValue π) := hs.hasSum_iff_tendsto_nat.mpr ht
  simpa only [M.discounted_iterate] using hh

/-- The original Bellman fixed-point definition and the discounted-return definition agree. -/
theorem MDP.expected_return_eq_value (M : MDP S A) (π : Policy S A) :
    (∑' n, (M.discount : ℝ)^n • (M.markovOperator π)^[n] (M.policyReward π)) = M.policyValue π :=
  (M.expected_return_hasSum π).tsum_eq

end Thesis.Bellman
