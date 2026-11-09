import HiddenMonotonicity.ModernGELU
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! Analytic slope bounds for the exact Gaussian GELU at its two inflection
points. These bounds use the actual Gaussian CDF and density, including their
limits at infinity; no numerical approximation of either function is involved. -/

namespace HiddenMonotonicity.SmoothDC

open Set Filter MeasureTheory
open scoped Topology

theorem standardGaussianCDF_atBot :
    Tendsto standardGaussianCDF atBot (𝓝 0) :=
  cumulative_atBot standardGaussianDensity

theorem standardGaussianCDF_atTop :
    Tendsto standardGaussianCDF atTop (𝓝 1) := by
  change Tendsto (fun x : ℝ => ∫ t in Iic x, standardGaussianDensity t) atTop (𝓝 1)
  have h := (aecover_Iic (μ := volume) (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)).integral_tendsto_of_countably_generated
    standardGaussianDensity_integrable
  simpa only [id_eq, standardGaussianDensity_normalized] using h

/-- The linear Gaussian term vanishes at both ends of the real line. -/
theorem standardGaussianDensity_mul_id_cocompact :
    Tendsto (fun x : ℝ => x * standardGaussianDensity x) (cocompact ℝ) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have he : (fun x : ℝ => ‖x * standardGaussianDensity x‖) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|x| * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) := by
    funext x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (standardGaussianDensity_pos x),
      standardGaussianDensity_formula]
    rw [show -x ^ 2 / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  rw [he]
  simpa only [Real.rpow_one, mul_zero] using
    (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (by norm_num : (0 : ℝ) < 1 / 2) 1).const_mul
      ((Real.sqrt (2 * Real.pi))⁻¹)

theorem gaussianGeluFirst_atBot :
    Tendsto gaussianGeluFirst atBot (𝓝 0) := by
  change Tendsto (fun x => standardGaussianCDF x + x * standardGaussianDensity x) atBot (𝓝 0)
  simpa only [add_zero] using
    standardGaussianCDF_atBot.add
      (standardGaussianDensity_mul_id_cocompact.mono_left atBot_le_cocompact)

theorem gaussianGeluFirst_atTop :
    Tendsto gaussianGeluFirst atTop (𝓝 1) := by
  change Tendsto (fun x => standardGaussianCDF x + x * standardGaussianDensity x) atTop (𝓝 1)
  simpa only [add_zero] using
    standardGaussianCDF_atTop.add
      (standardGaussianDensity_mul_id_cocompact.mono_left atTop_le_cocompact)

private theorem gaussianGeluFirst_differentiable : Differentiable ℝ gaussianGeluFirst :=
  fun x => (gaussianGeluFirst_hasDerivAt x).differentiableAt

theorem gaussianGeluFirst_antitone_left :
    AntitoneOn gaussianGeluFirst (Iic (-Real.sqrt 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Iic _)
    gaussianGeluFirst_differentiable.continuous.continuousOn
    gaussianGeluFirst_differentiable.differentiableOn
  intro x hx
  have hx' : x ∈ Iic (-Real.sqrt 2) := interior_subset hx
  change x ≤ -Real.sqrt 2 at hx'
  rw [(gaussianGeluFirst_hasDerivAt x).deriv, gaussianGeluSecond]
  apply mul_nonpos_of_nonpos_of_nonneg _ (standardGaussianDensity_pos x).le
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [mul_nonneg (show 0 ≤ -Real.sqrt 2 - x by linarith)
    (show 0 ≤ Real.sqrt 2 - x by linarith)]

theorem gaussianGeluFirst_monotone_middle :
    MonotoneOn gaussianGeluFirst (Icc (-Real.sqrt 2) (Real.sqrt 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    gaussianGeluFirst_differentiable.continuous.continuousOn
    gaussianGeluFirst_differentiable.differentiableOn
  intro x hx
  have hx' : x ∈ Icc (-Real.sqrt 2) (Real.sqrt 2) := interior_subset hx
  change -Real.sqrt 2 ≤ x ∧ x ≤ Real.sqrt 2 at hx'
  rw [(gaussianGeluFirst_hasDerivAt x).deriv, gaussianGeluSecond]
  apply mul_nonneg _ (standardGaussianDensity_pos x).le
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith [mul_nonneg (show 0 ≤ Real.sqrt 2 - x by linarith [hx'.2])
    (show 0 ≤ Real.sqrt 2 + x by linarith [hx'.1])]

theorem gaussianGeluFirst_antitone_right :
    AntitoneOn gaussianGeluFirst (Ici (Real.sqrt 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    gaussianGeluFirst_differentiable.continuous.continuousOn
    gaussianGeluFirst_differentiable.differentiableOn
  intro x hx
  have hx' : x ∈ Ici (Real.sqrt 2) := interior_subset hx
  change Real.sqrt 2 ≤ x at hx'
  rw [(gaussianGeluFirst_hasDerivAt x).deriv, gaussianGeluSecond]
  apply mul_nonpos_of_nonpos_of_nonneg _ (standardGaussianDensity_pos x).le
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [mul_nonneg (show 0 ≤ x - Real.sqrt 2 by linarith)
    (show 0 ≤ x + Real.sqrt 2 by linarith)]

theorem gaussianGeluFirst_left_bounds {x : ℝ} (hx : x ≤ -Real.sqrt 2) :
    gaussianGeluFirst (-Real.sqrt 2) ≤ gaussianGeluFirst x ∧ gaussianGeluFirst x ≤ 0 := by
  constructor
  · exact gaussianGeluFirst_antitone_left hx (by simp) hx
  · apply ge_of_tendsto gaussianGeluFirst_atBot
    filter_upwards [eventually_le_atBot x] with t ht
    exact gaussianGeluFirst_antitone_left (ht.trans hx) hx ht

theorem gaussianGeluFirst_middle_bounds {x : ℝ}
    (hx : -Real.sqrt 2 ≤ x ∧ x ≤ Real.sqrt 2) :
    gaussianGeluFirst (-Real.sqrt 2) ≤ gaussianGeluFirst x ∧
      gaussianGeluFirst x ≤ gaussianGeluFirst (Real.sqrt 2) := by
  have hab : -Real.sqrt 2 ≤ Real.sqrt 2 := neg_le_self (Real.sqrt_nonneg _)
  exact ⟨gaussianGeluFirst_monotone_middle ⟨le_rfl, hab⟩ hx hx.1,
    gaussianGeluFirst_monotone_middle hx ⟨hab, le_rfl⟩ hx.2⟩

theorem gaussianGeluFirst_right_bounds {x : ℝ} (hx : Real.sqrt 2 ≤ x) :
    0 ≤ gaussianGeluFirst x ∧ gaussianGeluFirst x ≤ gaussianGeluFirst (Real.sqrt 2) := by
  constructor
  · have h : (1 : ℝ) ≤ gaussianGeluFirst x := by
      apply le_of_tendsto gaussianGeluFirst_atTop
      filter_upwards [eventually_ge_atTop x] with t ht
      exact gaussianGeluFirst_antitone_right hx (hx.trans ht) ht
    exact le_trans (by norm_num) h
  · exact gaussianGeluFirst_antitone_right (by simp) hx hx

theorem gaussianGeluFirst_inflection_signs :
    gaussianGeluFirst (-Real.sqrt 2) ≤ 0 ∧ 0 ≤ gaussianGeluFirst (Real.sqrt 2) :=
  ⟨(gaussianGeluFirst_left_bounds le_rfl).2, (gaussianGeluFirst_right_bounds le_rfl).1⟩

end HiddenMonotonicity.SmoothDC
