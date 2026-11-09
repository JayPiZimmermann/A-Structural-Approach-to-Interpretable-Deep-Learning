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

theorem softplus_curvature_nonnegative (θ : ℝ) (hθ : 0<θ) (x : ℝ) :
    0≤curvature (Thesis.Regularization.softplus θ) x := by
  rw [softplus_curvature θ hθ]
  exact div_nonneg (sigmoidFirst_nonnegative _) hθ.le

theorem softplus_negativeCurvature_zero (θ : ℝ) (hθ : 0<θ) :
    negativeCurvature (Thesis.Regularization.softplus θ)=0 := by
  funext x
  exact max_eq_right (neg_nonpos.mpr (softplus_curvature_nonnegative θ hθ x))

theorem softplus_C2_zero (θ : ℝ) (hθ : 0<θ) :
    C2 (Thesis.Regularization.softplus θ)=0 := by
  funext x
  simp [C2,softplus_negativeCurvature_zero θ hθ,primitive,slope,cumulative]

theorem softplus_C1_eq (θ : ℝ) (hθ : 0<θ) :
    C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ := by
  funext x
  have h := primitive_difference (Thesis.Regularization.softplus θ)
    (fun y => (Thesis.Regularization.hasDerivAt_softplus θ y hθ).differentiableAt)
    (softplus_derivative_locally_AC θ hθ) (softplus_curvature_integrable θ hθ) x
  simpa only [softplus_C2_zero θ hθ,Pi.zero_apply,sub_zero] using h

theorem softplus_zero_nonnegative (θ : ℝ) (hθ : 0<θ) :
    0≤Thesis.Regularization.softplus θ 0 := by
  simp only [Thesis.Regularization.softplus,zero_div,Real.exp_zero]
  exact mul_nonneg hθ.le (Real.log_nonneg (by norm_num))

/-- The source's complete softplus specialization: no negative curvature, no
negative primitive, the positive primitive is softplus itself, and split streams
remain nonnegative for nonnegative pair inputs. -/
theorem softplus_degenerate_split (θ : ℝ) (hθ : 0<θ) :
    negativeCurvature (Thesis.Regularization.softplus θ)=0 ∧
    C2 (Thesis.Regularization.softplus θ)=0 ∧
    C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ ∧
    ConvexOn ℝ univ (Thesis.Regularization.softplus θ) ∧
    NonnegativePairActivation (splitPair (Thesis.Regularization.softplus θ)) := by
  refine ⟨softplus_negativeCurvature_zero θ hθ,softplus_C2_zero θ hθ,softplus_C1_eq θ hθ,?_,?_⟩
  · rw [← softplus_C1_eq θ hθ]
    exact primitive_convex _ (positiveCurvature_integrable _ (softplus_curvature_integrable θ hθ))
      (fun _ => le_max_right _ _) _ _
  · exact smooth_pair_nonnegative _
      (fun y => (Thesis.Regularization.hasDerivAt_softplus θ y hθ).differentiableAt)
      (softplus_derivative_locally_AC θ hθ) (softplus_curvature_integrable θ hθ)
      (softplus_zero_nonnegative θ hθ)

end HiddenMonotonicity.SmoothDC
