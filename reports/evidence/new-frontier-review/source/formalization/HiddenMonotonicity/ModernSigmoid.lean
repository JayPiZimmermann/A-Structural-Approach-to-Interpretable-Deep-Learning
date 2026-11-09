import HiddenMonotonicity.SmoothValidDecomposition
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FunProp
set_option maxHeartbeats 600000

namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

/-- An everywhere nonnegative derivative of a function with finite limits at
both infinities is globally integrable. This is proved from improper FTC. -/
theorem integrable_nonnegative_derivative (g d : ℝ → ℝ)
    (hd : ∀ x,HasDerivAt g (d x) x) (hp : ∀ x,0≤d x) (lo hi : ℝ)
    (hlo : Tendsto g atBot (𝓝 lo)) (hhi : Tendsto g atTop (𝓝 hi)) : Integrable d := by
  have hr : IntegrableOn d (Ioi 0) := integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => hd x) (fun x _ => hp x) hhi
  have hneg (x : ℝ) : HasDerivAt (fun y => -g (-y)) (d (-x)) x := by
    convert ((hd (-x)).comp x (hasDerivAt_neg' x)).fun_neg using 1
    · funext y
      simp only [Function.comp_def]
    · ring
  have hnegLim : Tendsto (fun x => -g (-x)) atTop (𝓝 (-lo)) :=
    (hlo.comp tendsto_neg_atTop_atBot).neg
  have hlr : IntegrableOn (fun x => d (-x)) (Ioi 0) := integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => hneg x) (fun x _ => hp (-x)) hnegLim
  have hlr' : IntegrableOn (fun x => d (-x)) (Ioi (-(0 : ℝ))) := by
    simpa only [neg_zero] using hlr
  have hfl := hlr'.comp_neg_Iio
  have hl : IntegrableOn d (Iio 0) := by simpa only [neg_neg] using hfl
  have hlc : IntegrableOn d (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio (f:=d) (b:=(0 : ℝ)) (μ:=volume)).mpr hl
  simpa only [Iic_union_Ioi,integrableOn_univ] using hlc.union hr

noncomputable def sigmoidFirst (x : ℝ) := Real.sigmoid x*(1-Real.sigmoid x)
noncomputable def sigmoidSecond (x : ℝ) := sigmoidFirst x*(1-2*Real.sigmoid x)

theorem sigmoidFirst_nonnegative (x : ℝ) : 0≤sigmoidFirst x :=
  mul_nonneg (Real.sigmoid_nonneg x) (sub_nonneg.mpr (Real.sigmoid_le_one x))

theorem sigmoidFirst_derivative (x : ℝ) : HasDerivAt sigmoidFirst (sigmoidSecond x) x := by
  have hd := Real.hasDerivAt_sigmoid x
  convert hd.fun_mul (hd.const_sub 1) using 1
  · rfl
  · simp only [sigmoidSecond,sigmoidFirst]
    ring

theorem sigmoidFirst_integrable : Integrable sigmoidFirst :=
  integrable_nonnegative_derivative Real.sigmoid sigmoidFirst Real.hasDerivAt_sigmoid
    sigmoidFirst_nonnegative 0 1 Real.tendsto_sigmoid_atBot Real.tendsto_sigmoid_atTop

theorem sigmoidSecond_bound (x : ℝ) : |sigmoidSecond x|≤sigmoidFirst x := by
  have h0 := Real.sigmoid_nonneg x
  have h1 := Real.sigmoid_le_one x
  have ha : |1-2*Real.sigmoid x|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  unfold sigmoidSecond
  rw [abs_mul,abs_of_nonneg (sigmoidFirst_nonnegative x)]
  exact le_trans (mul_le_mul_of_nonneg_left ha (sigmoidFirst_nonnegative x)) (by simp)

theorem sigmoidSecond_integrable : Integrable sigmoidSecond := by
  apply sigmoidFirst_integrable.mono'
  · have hc : Continuous sigmoidSecond := by unfold sigmoidSecond sigmoidFirst;fun_prop
    exact hc.aestronglyMeasurable
  · exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using sigmoidSecond_bound x)

theorem sigmoid_curvature : curvature Real.sigmoid=sigmoidSecond := by
  funext x
  unfold curvature
  rw [Real.deriv_sigmoid]
  exact (sigmoidFirst_derivative x).deriv

theorem sigmoid_derivative_locally_AC (a b : ℝ) :
    AbsolutelyContinuousOnInterval (deriv Real.sigmoid) a b := by
  have h2 : ContDiff ℝ (1+1) Real.sigmoid := contDiff_sigmoid.of_le (by simp)
  exact h2.deriv'.contDiffOn.absolutelyContinuousOnInterval

/-- The logistic sigmoid genuinely satisfies every analytic assumption of
thm:smooth_dc_split; its L1 curvature is proved, not postulated. -/
theorem sigmoid_smooth_dc_split :
    let f := Real.sigmoid
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z,tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2) := by
  have hi : Integrable (curvature Real.sigmoid) := by rw [sigmoid_curvature];exact sigmoidSecond_integrable
  exact (smooth_dc_split Real.sigmoid (fun x => (Real.hasDerivAt_sigmoid x).differentiableAt)
    sigmoid_derivative_locally_AC hi).2.2

end HiddenMonotonicity.SmoothDC
