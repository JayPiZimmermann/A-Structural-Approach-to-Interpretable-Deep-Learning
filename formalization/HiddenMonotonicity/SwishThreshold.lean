import HiddenMonotonicity.ModernSwish
import Mathlib.Topology.Order.IntermediateValue

/-! Exact turning point for the curvature of Swish. The constant is specified
by its unique positive root, rather than a floating-point approximation. -/
namespace HiddenMonotonicity.SmoothDC
open Set

noncomputable def swishTurningFunction (x : ℝ) : ℝ :=
  x * (2 * Real.sigmoid x - 1)

theorem swishTurningFunction_continuous : Continuous swishTurningFunction := by
  unfold swishTurningFunction
  fun_prop

theorem swishTurningFunction_even (x : ℝ) :
    swishTurningFunction (-x) = swishTurningFunction x := by
  simp only [swishTurningFunction, Real.sigmoid_neg]
  ring

theorem swishTurningFunction_strictMonoOn :
    StrictMonoOn swishTurningFunction (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hsy := Real.sigmoid_strictMono (show (0 : ℝ) < y from lt_of_le_of_lt hx hxy)
  rw [Real.sigmoid_zero] at hsy
  have hpos : 0 < 2 * Real.sigmoid y - 1 := by norm_num at hsy ⊢; linarith
  have hsm := Real.sigmoid_monotone hxy.le
  calc
    swishTurningFunction x ≤ x * (2 * Real.sigmoid y - 1) := by
      unfold swishTurningFunction
      exact mul_le_mul_of_nonneg_left (by linarith) hx
    _ < swishTurningFunction y := by
      exact mul_lt_mul_of_pos_right hxy hpos

theorem swishTurningFunction_two_lt : swishTurningFunction 2 < 2 := by
  have h := Real.sigmoid_lt_one (2 : ℝ)
  unfold swishTurningFunction
  linarith

theorem two_lt_swishTurningFunction_four : 2 < swishTurningFunction 4 := by
  have he : (5 : ℝ) ≤ Real.exp 4 := by
    convert Real.add_one_le_exp (4 : ℝ) using 1; norm_num
  have hs := Real.sigmoid_mul_rexp_neg (-4 : ℝ)
  rw [neg_neg, Real.sigmoid_neg] at hs
  have hsig := Real.sigmoid_lt_one (4 : ℝ)
  have hp := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hsig.le)
  have hlow : (3 / 4 : ℝ) < Real.sigmoid 4 := by nlinarith
  unfold swishTurningFunction
  linarith

theorem exists_swishTurningPoint :
    ∃ r : ℝ, 2 < r ∧ r < 4 ∧ swishTurningFunction r = 2 := by
  have hex := intermediate_value_Icc (show (2 : ℝ) ≤ 4 by norm_num)
    swishTurningFunction_continuous.continuousOn
    (show (2 : ℝ) ∈ Icc (swishTurningFunction 2) (swishTurningFunction 4) from
      ⟨swishTurningFunction_two_lt.le, two_lt_swishTurningFunction_four.le⟩)
  obtain ⟨r, hr, he⟩ := hex
  refine ⟨r, ?_, ?_, he⟩
  · exact lt_of_le_of_ne hr.1 (by intro h; subst r; linarith [swishTurningFunction_two_lt])
  · exact lt_of_le_of_ne hr.2 (by intro h; subst r; linarith [two_lt_swishTurningFunction_four])

noncomputable def swishTurningPoint : ℝ := Classical.choose exists_swishTurningPoint

theorem swishTurningPoint_spec :
    2 < swishTurningPoint ∧ swishTurningPoint < 4 ∧
      swishTurningFunction swishTurningPoint = 2 :=
  Classical.choose_spec exists_swishTurningPoint

theorem swishTurningPoint_pos : 0 < swishTurningPoint := by
  linarith [swishTurningPoint_spec.1]

theorem swishTurningPoint_equation :
    swishTurningPoint * (2 * Real.sigmoid swishTurningPoint - 1) = 2 :=
  swishTurningPoint_spec.2.2

theorem swishTurningPoint_unique (r : ℝ) (hr : 0 ≤ r)
    (he : swishTurningFunction r = 2) : r = swishTurningPoint := by
  apply swishTurningFunction_strictMonoOn.injOn hr swishTurningPoint_pos.le
  exact he.trans swishTurningPoint_spec.2.2.symm

theorem swishTurningFunction_lt_two_iff (x : ℝ) (hx : 0 ≤ x) :
    swishTurningFunction x < 2 ↔ x < swishTurningPoint := by
  rw [← swishTurningPoint_spec.2.2]
  exact swishTurningFunction_strictMonoOn.lt_iff_lt hx swishTurningPoint_pos.le

theorem two_lt_swishTurningFunction_iff (x : ℝ) (hx : 0 ≤ x) :
    2 < swishTurningFunction x ↔ swishTurningPoint < x := by
  rw [← swishTurningPoint_spec.2.2]
  exact swishTurningFunction_strictMonoOn.lt_iff_lt swishTurningPoint_pos.le hx

theorem swishTurningFunction_abs (x : ℝ) :
    swishTurningFunction |x| = swishTurningFunction x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, swishTurningFunction_even]

theorem swish_curvature_turning_factor (β x : ℝ) :
    curvature (swish β) x =
      β * sigmoidFirst (β*x) * (2 - swishTurningFunction (β*x)) := by
  rw [swish_curvature]
  unfold swishSecond swishTurningFunction
  ring

/-- Exact two-inflection sign classification, including both tails. -/
theorem swish_curvature_turning_sign (β : ℝ) (hβ : 0 < β) (x : ℝ) :
    (0 < curvature (swish β) x ↔ |β*x| < swishTurningPoint) ∧
    (curvature (swish β) x < 0 ↔ swishTurningPoint < |β*x|) ∧
    (curvature (swish β) x = 0 ↔ |β*x| = swishTurningPoint) := by
  have hp : 0 < β * sigmoidFirst (β*x) :=
    mul_pos hβ (mul_pos (Real.sigmoid_pos _) (sub_pos.mpr (Real.sigmoid_lt_one _)))
  rw [swish_curvature_turning_factor, ← swishTurningFunction_abs (β*x)]
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_pos_iff_of_pos_left hp, sub_pos]
    exact swishTurningFunction_lt_two_iff _ (abs_nonneg _)
  · simp only [mul_neg_iff, hp, true_and, not_lt_of_ge hp.le, false_and, or_false,
      sub_neg]
    exact two_lt_swishTurningFunction_iff _ (abs_nonneg _)
  · rw [mul_eq_zero, or_iff_right (ne_of_gt hp), sub_eq_zero]
    constructor
    · intro he
      exact swishTurningPoint_unique _ (abs_nonneg _) he.symm
    · intro he
      rw [he, swishTurningPoint_spec.2.2]

theorem swishFirst_neg (β x : ℝ) :
    swishFirst β (-x) = 1 - swishFirst β x := by
  simp only [swishFirst, mul_neg, Real.sigmoid_neg, sigmoidFirst_even]
  ring

/-- The endpoint slopes simplify using the defining turning-point equation. -/
theorem swishFirst_at_turningPoint (β : ℝ) (hβ : β ≠ 0) :
    swishFirst β (swishTurningPoint / β) = (2 + swishTurningPoint) / 4 := by
  have he := swishTurningPoint_equation
  have hes := congrArg (fun q : ℝ => q * Real.sigmoid swishTurningPoint) he
  unfold swishFirst
  rw [mul_div_cancel₀ _ hβ]
  unfold sigmoidFirst
  nlinarith

theorem swishFirst_at_neg_turningPoint (β : ℝ) (hβ : β ≠ 0) :
    swishFirst β (-swishTurningPoint / β) = (2 - swishTurningPoint) / 4 := by
  rw [neg_div, swishFirst_neg, swishFirst_at_turningPoint β hβ]
  ring

end HiddenMonotonicity.SmoothDC
