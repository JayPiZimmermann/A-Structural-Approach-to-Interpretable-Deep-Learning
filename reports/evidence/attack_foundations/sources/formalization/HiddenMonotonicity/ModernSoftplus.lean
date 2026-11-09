import HiddenMonotonicity.ModernSigmoid
import Thesis.Regularization
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

/-- The actual second derivative is an integrable rescaling of sigmoid'. -/
theorem softplus_curvature (θ : ℝ) (hθ : 0<θ) :
    curvature (Thesis.Regularization.softplus θ)=fun x => sigmoidFirst (x/θ)/θ := by
  funext x
  unfold curvature
  have he : deriv (Thesis.Regularization.softplus θ)=Thesis.Regularization.gate θ :=
    funext (fun y => Thesis.Regularization.deriv_softplus θ y hθ)
  rw [he]
  exact (Thesis.Regularization.hasDerivAt_gate θ x hθ).deriv

theorem softplus_curvature_integrable (θ : ℝ) (hθ : 0<θ) :
    Integrable (curvature (Thesis.Regularization.softplus θ)) := by
  rw [softplus_curvature θ hθ]
  exact (sigmoidFirst_integrable.comp_div (ne_of_gt hθ)).div_const θ

theorem softplus_derivative_locally_AC (θ : ℝ) (hθ : 0<θ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (deriv (Thesis.Regularization.softplus θ)) a b := by
  have he : deriv (Thesis.Regularization.softplus θ)=Thesis.Regularization.gate θ :=
    funext (fun y => Thesis.Regularization.deriv_softplus θ y hθ)
  rw [he]
  have hsig : ContDiff ℝ 1 Real.sigmoid := contDiff_sigmoid.of_le (by simp)
  have hlin : ContDiff ℝ 1 (fun x : ℝ => x/θ) := by fun_prop
  have hgate : ContDiff ℝ 1 (Thesis.Regularization.gate θ) := hsig.comp hlin
  exact hgate.contDiffOn.absolutelyContinuousOnInterval

/-- Softplus satisfies all the theorem hypotheses, including actual L1 curvature. -/
theorem softplus_smooth_dc_split (θ : ℝ) (hθ : 0<θ) :
    let f := Thesis.Regularization.softplus θ
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z,tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2) := by
  exact (smooth_dc_split (Thesis.Regularization.softplus θ)
    (fun x => (Thesis.Regularization.hasDerivAt_softplus θ x hθ).differentiableAt)
    (softplus_derivative_locally_AC θ hθ) (softplus_curvature_integrable θ hθ)).2.2

end HiddenMonotonicity.SmoothDC
