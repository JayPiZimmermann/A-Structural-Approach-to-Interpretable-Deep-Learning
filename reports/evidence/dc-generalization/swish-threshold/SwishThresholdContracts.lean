import HiddenMonotonicity.SwishThreshold

/-! Independently authored contracts for the exact Swish turning-point claims.
These expected propositions are not extracted from declaration types. -/
open HiddenMonotonicity.SmoothDC

example : ∃ r : ℝ, 2 < r ∧ r < 4 ∧ r * (2 * Real.sigmoid r - 1) = 2 :=
  exists_swishTurningPoint

example : 2 < swishTurningPoint ∧ swishTurningPoint < 4 ∧
    swishTurningPoint * (2 * Real.sigmoid swishTurningPoint - 1) = 2 :=
  swishTurningPoint_spec

example : ∀ r : ℝ, 0 ≤ r → r * (2 * Real.sigmoid r - 1) = 2 →
    r = swishTurningPoint :=
  swishTurningPoint_unique

example : ∀ β : ℝ, 0 < β → ∀ x : ℝ,
    (0 < curvature (swish β) x ↔ |β * x| < swishTurningPoint) ∧
    (curvature (swish β) x < 0 ↔ swishTurningPoint < |β * x|) ∧
    (curvature (swish β) x = 0 ↔ |β * x| = swishTurningPoint) :=
  swish_curvature_turning_sign

example : ∀ β : ℝ, β ≠ 0 →
    swishFirst β (swishTurningPoint / β) = (2 + swishTurningPoint) / 4 :=
  swishFirst_at_turningPoint

example : ∀ β : ℝ, β ≠ 0 →
    swishFirst β (-swishTurningPoint / β) = (2 - swishTurningPoint) / 4 :=
  swishFirst_at_neg_turningPoint

-- Nonvacuity and both boundary orientations, plus strict central/tail consumers.
example : 0 < curvature (swish 1) 0 := by
  apply (swish_curvature_turning_sign 1 (by norm_num) 0).1.mpr
  simpa using swishTurningPoint_pos

example : ∀ β : ℝ, 0 < β →
    curvature (swish β) (swishTurningPoint / β) = 0 := by
  intro β hβ
  apply (swish_curvature_turning_sign β hβ _).2.2.mpr
  rw [mul_div_cancel₀ _ (ne_of_gt hβ), abs_of_pos swishTurningPoint_pos]

example : ∀ β : ℝ, 0 < β →
    curvature (swish β) (-swishTurningPoint / β) = 0 := by
  intro β hβ
  apply (swish_curvature_turning_sign β hβ _).2.2.mpr
  rw [mul_div_cancel₀ _ (ne_of_gt hβ), abs_neg, abs_of_pos swishTurningPoint_pos]

example : curvature (swish 1) 4 < 0 := by
  apply (swish_curvature_turning_sign 1 (by norm_num) 4).2.1.mpr
  simpa using swishTurningPoint_spec.2.1

example : curvature (swish 1) (-4) < 0 := by
  apply (swish_curvature_turning_sign 1 (by norm_num) (-4)).2.1.mpr
  simpa using swishTurningPoint_spec.2.1

#check @exists_swishTurningPoint
#check @swishTurningPoint_spec
#check @swishTurningPoint_unique
#check @swish_curvature_turning_sign
#check @swishFirst_at_turningPoint
#check @swishFirst_at_neg_turningPoint

#print axioms exists_swishTurningPoint
#print axioms swishTurningPoint_spec
#print axioms swishTurningPoint_unique
#print axioms swish_curvature_turning_sign
#print axioms swishFirst_at_turningPoint
#print axioms swishFirst_at_neg_turningPoint
