import HiddenMonotonicity.ModernSwish

/-! Exact algebraic identities used by the explicit Swish DC lift. -/
namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

/-- Reflection exchanges the two asymptotic slopes. -/
theorem swishFirst_reflect (β x : ℝ) :
    swishFirst β (-x) = 1 - swishFirst β x := by
  simp only [swishFirst, mul_neg, Real.sigmoid_neg, sigmoidFirst_even]
  ring

/-- The original signed activation has the usual SiLU reflection identity. -/
theorem swish_reflect (β x : ℝ) : swish β (-x) = swish β x - x := by
  simp only [swish, mul_neg, Real.sigmoid_neg]
  ring

/-- Positive-scale Swish's derivative depends only on the scaled coordinate. -/
theorem swishFirst_rescale (β : ℝ) (hβ : β ≠ 0) (t : ℝ) :
    swishFirst β (t / β) = swishFirst 1 t := by
  simp [swishFirst, mul_div_cancel₀ _ hβ]

/-- At a positive curvature turning point the derivative has a simple exact value. -/
theorem swishFirst_at_turning_point (r : ℝ)
    (hr : r * (2 * Real.sigmoid r - 1) = 2) :
    swishFirst 1 r = (2 + r) / 4 := by
  simp only [swishFirst, one_mul, sigmoidFirst]
  have h := congrArg (fun t : ℝ => t * Real.sigmoid r) hr
  nlinarith only [hr, h]

/-- The corresponding negative turning point gives the negative slope minimum. -/
theorem swishFirst_at_negative_turning_point (r : ℝ)
    (hr : r * (2 * Real.sigmoid r - 1) = 2) :
    swishFirst 1 (-r) = (2 - r) / 4 := by
  rw [swishFirst_reflect, swishFirst_at_turning_point r hr]
  ring

/-- Beyond two in the scaled coordinate, Swish's slope is at least one. -/
theorem one_le_swishFirst_of_two_le (t : ℝ) (ht : 2 ≤ t) :
    1 ≤ swishFirst 1 t := by
  have hs : (1 / 2 : ℝ) ≤ Real.sigmoid t := by
    simpa only [Real.sigmoid_zero, one_div] using
      Real.sigmoid_monotone (show (0 : ℝ) ≤ t by linarith)
  have hs0 := Real.sigmoid_nonneg t
  have hs1 := Real.sigmoid_le_one t
  have hts : 1 ≤ t * Real.sigmoid t := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hts)
  simp only [swishFirst, sigmoidFirst, one_mul]
  nlinarith only [hp]

/-- The negative tail has nonpositive slope. -/
theorem swishFirst_nonpositive_of_le_neg_two (t : ℝ) (ht : t ≤ -2) :
    swishFirst 1 t ≤ 0 := by
  have h := one_le_swishFirst_of_two_le (-t) (by linarith)
  rw [swishFirst_reflect] at h
  linarith

/-- At the turning point even the activation value reduces to rational algebra. -/
theorem swish_at_turning_point (β r : ℝ) (hβ : β ≠ 0)
    (hr : r * (2 * Real.sigmoid r - 1) = 2) :
    swish β (r / β) = (r + 2) / (2 * β) := by
  simp only [swish, mul_div_cancel₀ _ hβ]
  field_simp
  nlinarith only [hr]

theorem swish_at_negative_turning_point (β r : ℝ) (hβ : β ≠ 0)
    (hr : r * (2 * Real.sigmoid r - 1) = 2) :
    swish β (-(r / β)) = -(r - 2) / (2 * β) := by
  rw [swish_reflect, swish_at_turning_point β r hβ hr]
  field_simp
  ring

theorem swish_left_tangent_intercept (β r : ℝ) (hβ : β ≠ 0)
    (hr : r * (2 * Real.sigmoid r - 1) = 2) :
    swish β (-(r / β)) - ((2 - r) / 4) * (-(r / β)) =
      -(r ^ 2 - 4) / (4 * β) := by
  rw [swish_at_negative_turning_point β r hβ hr]
  field_simp
  ring

theorem swish_right_tangent_intercept (β r : ℝ) (hβ : β ≠ 0)
    (hr : r * (2 * Real.sigmoid r - 1) = 2) :
    swish β (r / β) - ((2 - r) / 4) * (r / β) - (r / 2) * (r / β) =
      -(r ^ 2 - 4) / (4 * β) := by
  rw [swish_at_turning_point β r hβ hr]
  field_simp
  ring

end HiddenMonotonicity.SmoothDC
