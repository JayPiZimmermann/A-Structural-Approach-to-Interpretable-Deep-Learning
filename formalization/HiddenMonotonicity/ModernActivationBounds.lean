import HiddenMonotonicity.ModernSigmoid
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Analytic bounds used by the modern activation specializations. -/
namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

/-- A continuous classical derivative gives genuine local absolute continuity. -/
theorem locally_AC_of_continuous_derivative (g d : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt g (d x) x) (hc : Continuous d) (a b : ℝ) :
    AbsolutelyContinuousOnInterval g a b := by
  have h : ContDiff ℝ 1 g := contDiff_one_iff_deriv.mpr
    ⟨fun x => (hd x).differentiableAt,by rwa [show deriv g=d from funext fun x => (hd x).deriv]⟩
  exact h.contDiffOn.absolutelyContinuousOnInterval

theorem cumulative_hasDerivAt_of_continuous (q : ℝ → ℝ) (hq : Integrable q)
    (hc : Continuous q) (x : ℝ) : HasDerivAt (cumulative q) (q x) x := by
  have he : cumulative q=fun y => cumulative q 0+∫ t in (0 : ℝ)..y,q t := by
    funext y
    have h := intervalIntegral.integral_Iic_sub_Iic (hq.integrableOn (s:=Iic 0))
      (hq.integrableOn (s:=Iic y))
    change cumulative q y-cumulative q 0=_ at h
    linarith
  rw [he]
  exact (hc.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add _

/-- Reflection supplies the missing half-line for an even integrand. -/
theorem integrable_even_of_Ioi (g : ℝ → ℝ) (he : ∀ x, g (-x)=g x)
    (hr : IntegrableOn g (Ioi 0)) : Integrable g := by
  have hr' : IntegrableOn (fun x => g (-x)) (Ioi (-(0 : ℝ))) := by simpa [he] using hr
  have hl : IntegrableOn g (Iio 0) := by simpa only [neg_neg] using hr'.comp_neg_Iio
  have hlc : IntegrableOn g (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio
    (f:=g) (b:=(0 : ℝ)) (μ:=volume)).mpr hl
  simpa only [Iic_union_Ioi,integrableOn_univ] using hlc.union hr

theorem exp_neg_abs_integrable : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  apply integrable_even_of_Ioi _ (fun x => by rw [abs_neg])
  apply (integrableOn_exp_neg_Ioi 0).congr_fun _ measurableSet_Ioi
  intro x hx
  dsimp only
  rw [abs_of_pos hx]

/-- A polynomial factor does not destroy exponential integrability, with a
proved global bound on the full real line. -/
theorem abs_mul_exp_neg_abs_integrable : Integrable (fun x : ℝ => |x| *Real.exp (-|x|)) := by
  apply integrable_even_of_Ioi _ (fun x => by rw [abs_neg])
  have hi : IntegrableOn (fun x : ℝ => x*Real.exp (-x)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_rpow (s:=1) (p:=1) (by norm_num) (by norm_num))
  apply hi.congr_fun _ measurableSet_Ioi
  intro x hx
  dsimp only
  rw [abs_of_pos hx]

theorem sigmoid_le_exp (x : ℝ) : Real.sigmoid x≤Real.exp x := by
  have he := Real.sigmoid_mul_rexp_neg (-x)
  simp only [neg_neg] at he
  rw [← he]
  exact mul_le_of_le_one_left (Real.exp_pos x).le (Real.sigmoid_le_one (-x))

theorem sigmoidFirst_even (x : ℝ) : sigmoidFirst (-x)=sigmoidFirst x := by
  unfold sigmoidFirst
  rw [Real.sigmoid_neg]
  ring

theorem sigmoidFirst_exp_bound (x : ℝ) : sigmoidFirst x≤Real.exp (-|x|) := by
  have hb (y : ℝ) : sigmoidFirst y≤Real.exp (-y) := by
    unfold sigmoidFirst
    rw [← Real.sigmoid_neg]
    exact (mul_le_of_le_one_left (Real.sigmoid_nonneg (-y)) (Real.sigmoid_le_one y)).trans
      (sigmoid_le_exp (-y))
  rcases le_total 0 x with hx | hx
  · simpa only [abs_of_nonneg hx] using hb x
  · simpa only [sigmoidFirst_even,abs_of_nonpos hx,neg_neg] using hb (-x)

/-- This weighted sigmoid bound is the integrability step needed for Swish. -/
theorem weighted_sigmoidSecond_integrable : Integrable (fun x : ℝ => x*sigmoidSecond x) := by
  apply abs_mul_exp_neg_abs_integrable.mono'
  · have hc : Continuous (fun x : ℝ => x*sigmoidSecond x) := by
      unfold sigmoidSecond sigmoidFirst; fun_prop
    exact hc.aestronglyMeasurable
  · apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left ((sigmoidSecond_bound x).trans (sigmoidFirst_exp_bound x))
      (abs_nonneg x)

end HiddenMonotonicity.SmoothDC
