import HiddenMonotonicity.ModernMonotoneDC
import HiddenMonotonicity.TwoInflectionDC

/-! Handwritten independent boundary consumers. These examples distinguish
signed affine outputs, output positivity, and order after a signed embedding. -/
noncomputable section
set_option autoImplicit false

namespace DCGeneralizationReview
open HiddenMonotonicity HiddenMonotonicity.SmoothDC Set Matrix

theorem modern_sigmoid_valid :
    ValidPairActivation Real.sigmoid (curvatureLiftPair Real.sigmoid) :=
  (modern_curvature_pair .sigmoid).2.2.1

theorem modern_gelu_valid :
    ValidPairActivation gaussianGelu (curvatureLiftPair gaussianGelu) :=
  (modern_curvature_pair .gaussianGelu).2.2.1

theorem modern_swish_valid (β : ℝ) (hβ : 0 < β) :
    ValidPairActivation (swish β) (curvatureLiftPair (swish β)) :=
  (modern_curvature_pair (.swish β hβ)).2.2.1

theorem modern_softplus_valid (θ : ℝ) (hθ : 0 < θ) :
    ValidPairActivation (Thesis.Regularization.softplus θ)
      (curvatureLiftPair (Thesis.Regularization.softplus θ)) :=
  (modern_curvature_pair (.softplus θ hθ)).2.2.1

/-- An identity backbone and a truly ungated negative signed readout.
The first head is allowed to be negative because its bias is arbitrary. -/
theorem ungated_negative_readout :
    let heads : PairVec 1 := (Network.output 1).affineDecomposeWith
      (curvatureLiftPair gaussianGelu)
      (fun _ _ => (0 : ℝ)) (fun _ _ => (1 : ℝ))
      (fun _ => (-3 : ℝ)) (fun _ => (0 : ℝ))
      ((fun _ => (2 : ℝ)), (fun _ => (0 : ℝ)))
    heads.1 0 = -3 ∧ heads.2 0 = 2 ∧ heads.1 0 - heads.2 0 = -5 := by
  change
    ((∑ _ : Fin 1, (0 : ℝ) * 2) + (∑ _ : Fin 1, (1 : ℝ) * 0) + -3 = -3) ∧
    ((∑ _ : Fin 1, (1 : ℝ) * 2) + (∑ _ : Fin 1, (0 : ℝ) * 0) + 0 = 2) ∧
    ((∑ _ : Fin 1, (0 : ℝ) * 2) + (∑ _ : Fin 1, (1 : ℝ) * 0) + -3 -
      ((∑ _ : Fin 1, (1 : ℝ) * 2) + (∑ _ : Fin 1, (0 : ℝ) * 0) + 0) = -5)
  norm_num

/-- The readout permits a zero-width backbone and retains signed biases. -/
theorem zero_width_readout (φ : (ℝ × ℝ) → ℝ × ℝ) (bp bn : Vec 1)
    (x : PairVec 0) :
    (Network.output 0).affineDecomposeWith φ
      (0 : Matrix (Fin 1) (Fin 0) ℝ) 0 bp bn x = (bp, bn) := by
  ext i <;> simp [Network.affineDecomposeWith, Network.decomposeWith,
    preP, preN, matrixCLM]

/-- A signed-input split retains convexity, but its negative branch is not
coordinatewise nondecreasing in the original signed input. -/
theorem negative_part_not_monotone :
    ¬Monotone (fun x : ℝ => max (-x) 0) := by
  intro h
  have hh := h (show (-1 : ℝ) ≤ 0 by norm_num)
  norm_num at hh

/-- Both exact threshold branches include their boundary values. -/
theorem central_threshold_values (f d : ℝ → ℝ) (a b : ℝ) (hab : a < b) :
    centralConvexP f d a b a = f a - d a * a ∧
    centralConvexP f d a b b = f b - d a * b := by
  simp [centralConvexP, not_le.mpr hab]

theorem central_threshold_derivatives (f d : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : ∀ x, HasDerivAt f (d x) x) :
    HasDerivAt (centralConvexP f d a b) 0 a ∧
    HasDerivAt (centralConvexP f d a b) (d b - d a) b := by
  constructor
  · simpa [centralConvexPFirst] using centralConvexP_hasDerivAt f d a b hab hf a
  · simpa [centralConvexPFirst, not_le.mpr hab] using
      centralConvexP_hasDerivAt f d a b hab hf b

#print axioms modern_gelu_valid
#print axioms ungated_negative_readout
#print axioms zero_width_readout
#print axioms negative_part_not_monotone
#print axioms central_threshold_derivatives
#check @Network.convex_monotone_decomposition
#check @Network.affine_signed_input_dc_decomposition
#check @modern_curvature_affine_network
#check @centralConvex_asymmetric_split
#print axioms Network.convex_monotone_decomposition
#print axioms Network.affine_signed_input_dc_decomposition
#print axioms modern_curvature_affine_network
#print axioms centralConvex_asymmetric_split

end DCGeneralizationReview
