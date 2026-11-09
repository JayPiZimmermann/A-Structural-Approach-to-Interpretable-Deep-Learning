import HiddenMonotonicity.CurvatureMonotoneDCLift

set_option autoImplicit false
open Set MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC

/-- A negative constant is admissible under all analytic hypotheses. -/
theorem negativeConstant_admissible :
    Differentiable ℝ (fun _ : ℝ => (-1 : ℝ)) ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv (fun _ : ℝ => (-1 : ℝ))) a b) ∧
    Integrable (curvature (fun _ : ℝ => (-1 : ℝ))) := by
  refine ⟨differentiable_const _, ?_, ?_⟩
  · intro a b
    have h : deriv (fun _ : ℝ => (-1 : ℝ)) = fun _ => 0 := by
      funext x
      exact deriv_const x (-1 : ℝ)
    rw [h]
    exact contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  · simp [curvature]

/-- Normalization handles f(0)<0 at the boundary of the nonnegative quadrant. -/
example : normalizedCurvatureLiftPair (fun _ : ℝ => (-1 : ℝ)) (0,0) = (0,1) := by
  norm_num [normalizedCurvatureLiftPair, curvatureLiftPair, asymmetricLift,
    curvaturePositiveProfile, curvatureNegativeProfile, C1, C2, primitive]

/-- This actually instantiates the unconditional normalized stream theorem. -/
example : NonnegativePairActivation
    (normalizedCurvatureLiftPair (fun _ : ℝ => (-1 : ℝ))) :=
  normalizedCurvatureLiftPair_nonnegative _ negativeConstant_admissible.1
    negativeConstant_admissible.2.1 negativeConstant_admissible.2.2

/-- The original canonical pair deliberately retains the signed value at zero. -/
example : curvatureLiftPair (fun _ : ℝ => (-1 : ℝ)) (0,0) = (-1,0) := by
  norm_num [curvatureLiftPair, asymmetricLift, curvaturePositiveProfile,
    curvatureNegativeProfile, C1, C2, primitive]

#print axioms negativeConstant_admissible
