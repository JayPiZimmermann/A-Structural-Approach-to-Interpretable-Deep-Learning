import HiddenMonotonicity.Core
import Mathlib.Algebra.Order.Group.Finset

namespace HiddenMonotonicity
open scoped BigOperators

/-- Classical derivative of a maximum wherever the first branch strictly wins. -/
theorem max_derivative_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (x : E) (Df Dg : E →L[ℝ] ℝ)
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x) (h : g x < f x) :
    HasFDerivAt (fun y => max (f y) (g y)) Df x := by
  apply hf.congr_of_eventuallyEq
  filter_upwards [hg.continuousAt.eventually_lt hf.continuousAt h] with y hy
  exact max_eq_left (le_of_lt hy)

/-- Classical derivative of a maximum wherever the second branch strictly wins. -/
theorem max_derivative_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (x : E) (Df Dg : E →L[ℝ] ℝ)
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x) (h : f x < g x) :
    HasFDerivAt (fun y => max (f y) (g y)) Dg x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.eventually_lt hg.continuousAt h] with y hy
  exact max_eq_right (le_of_lt hy)

/-- Convexity-preserving finite max-pooling identity, for any nonempty pool. -/
theorem maxpool_correct {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (p n : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun j => p j + ∑ i ∈ Finset.univ.erase j, n i) - ∑ i, n i =
    Finset.univ.sup' Finset.univ_nonempty (fun j => p j - n j) := by
  rw [sub_eq_add_neg, Finset.sup'_add]
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro j _
  have he := Finset.sum_erase_add Finset.univ n (Finset.mem_univ j)
  linarith

/-- Additive residual nodes preserve the split difference. -/
theorem residual_correct (p q r s : ℝ) : (p+r)-(q+s) = (p-q)+(r-s) := by ring

/-- Finite averaging/pooling and any fixed weighted sum preserve reconstruction. -/
theorem weighted_sum_correct {ι : Type*} [Fintype ι] (w p n : ι → ℝ) :
    (∑ i, w i*p i) - (∑ i, w i*n i) = ∑ i, w i*(p i-n i) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Two-factor sign expansion is algebraically exact; no convexity is claimed. -/
theorem multiplicative_split_correct (p q r s : ℝ) :
    (p*r+q*s)-(p*s+q*r) = (p-q)*(r-s) := by ring

/-- A shared scalar offset preserves the activation difference. -/
theorem common_offset_correct (p n τ : ℝ) :
    (max p n + τ*min p n) - (n + τ*min p n) = relu (p-n) := by
  rw [show (max p n + τ*min p n) - (n + τ*min p n) = max p n-n by ring]
  exact max_sub p n

/-- The thesis mixing family: both endpoints and every interpolation recover ReLU. -/
theorem mixing_correct (p n η : ℝ) :
    (η*max p n+(1-η)*p) - (η*n+(1-η)*min p n) = relu (p-n) := by
  rcases le_total p n with h | h
  · simp only [max_eq_right h, min_eq_left h]
    rw [relu, max_eq_right (sub_nonpos.mpr h)]
    ring
  · simp only [max_eq_left h, min_eq_right h]
    rw [relu, max_eq_left (sub_nonneg.mpr h)]
    ring

/-- Shared winner-take-all pooling preserves reconstruction at a chosen winner,
but the rule alone supplies no convexity or monotonicity guarantee. -/
theorem winner_pool_correct {ι : Type*} (p n : ι → ℝ) (j : ι) :
    p j - n j = (p-n) j := rfl

/-- Equal common shifts do not alter the comparison selecting a max branch. -/
theorem shift_mask_invariant (p n c : ℝ) :
    (p+c ≥ n+c ↔ p≥n) ∧ (p+c<n+c ↔ p<n) := by constructor <;> constructor <;> intro h <;> linarith

end HiddenMonotonicity
