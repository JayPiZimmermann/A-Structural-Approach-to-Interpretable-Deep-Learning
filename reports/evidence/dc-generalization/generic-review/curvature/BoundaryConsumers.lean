import HiddenMonotonicity.CurvatureMonotoneDCLift

set_option autoImplicit false

open Set MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC

namespace CurvatureLiftBoundaryReview

-- Constant activations witness satisfiability of all analytic hypotheses.
theorem constant_hypotheses (c : ℝ) :
    Differentiable ℝ (fun _ : ℝ => c) ∧
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval (deriv (fun _ : ℝ => c)) a b) ∧
    Integrable (curvature (fun _ : ℝ => c)) := by
  refine ⟨differentiable_const c, ?_, ?_⟩
  · intro a b
    simpa using (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := a) (b := b)
  · simp [curvature]

-- Negative f(0) genuinely needs the common-offset normalization for orthant positivity.
theorem negative_constant_raw_pair (z : ℝ × ℝ) :
    curvatureLiftPair (fun _ : ℝ => -2) z = (-2, 0) := by
  simp [curvatureLiftPair, asymmetricLift, curvaturePositiveProfile,
    curvatureNegativeProfile, curvatureLiftWidth, curvatureSlopeShift,
    totalPositiveCurvature, totalNegativeCurvature, minusInfinitySlope,
    C1, C2, positiveCurvature, negativeCurvature, curvature,
    primitive, HiddenMonotonicity.SmoothDC.slope, cumulative]

theorem negative_constant_normalized_pair (z : ℝ × ℝ) :
    normalizedCurvatureLiftPair (fun _ : ℝ => -2) z = (0, 2) := by
  simp [normalizedCurvatureLiftPair, negative_constant_raw_pair]

theorem raw_pair_need_not_be_nonnegative :
    ¬ NonnegativePairActivation (curvatureLiftPair (fun _ : ℝ => -2)) := by
  intro h
  have hn := (h 0 0 le_rfl le_rfl).1
  norm_num [negative_constant_raw_pair] at hn

-- The headline normalization theorem applies without the f(0)≥0 assumption.
theorem normalized_negative_constant_nonnegative :
    NonnegativePairActivation (normalizedCurvatureLiftPair (fun _ : ℝ => -2)) := by
  have h := constant_hypotheses (-2)
  exact normalizedCurvatureLiftPair_nonnegative _ h.1 h.2.1 h.2.2

theorem constant_reconstruction (c : ℝ) (x y : ℝ) :
    (curvatureLiftPair (fun _ : ℝ => c) (x, y)).1 -
      (curvatureLiftPair (fun _ : ℝ => c) (x, y)).2 = c := by
  have h := constant_hypotheses c
  exact (curvature_monotone_dc_split _ h.1 h.2.1 h.2.2).2.2.2.2 x y

end CurvatureLiftBoundaryReview
