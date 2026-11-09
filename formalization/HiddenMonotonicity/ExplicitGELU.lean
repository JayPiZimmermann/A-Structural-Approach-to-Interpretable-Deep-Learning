import HiddenMonotonicity.GELUInflectionBounds
import HiddenMonotonicity.MonotoneDCLift

/-! A root-free closed-form convex monotone lift of exact Gaussian GELU.
The profiles are `P = 2 (GELU + φ)` and `Q = GELU + 2 φ`, with common
lift width two. Their second derivatives are `2 φ` and `x² φ`. -/

namespace HiddenMonotonicity.SmoothDC

open Set Filter
open scoped Topology

noncomputable def gaussianGeluPositiveProfile (x : ℝ) : ℝ :=
  2 * (gaussianGelu x + standardGaussianDensity x)

noncomputable def gaussianGeluNegativeProfile (x : ℝ) : ℝ :=
  gaussianGelu x + 2 * standardGaussianDensity x

noncomputable def gaussianGeluNegativeSlope (x : ℝ) : ℝ :=
  standardGaussianCDF x - x * standardGaussianDensity x

theorem standardGaussianCDF_monotone : Monotone standardGaussianCDF :=
  cumulative_monotone standardGaussianDensity standardGaussianDensity_integrable
    (fun x => (standardGaussianDensity_pos x).le)

theorem standardGaussianCDF_bounds (x : ℝ) :
    0 ≤ standardGaussianCDF x ∧ standardGaussianCDF x ≤ 1 := by
  constructor
  · apply le_of_tendsto standardGaussianCDF_atBot
    filter_upwards [eventually_le_atBot x] with t ht
    exact standardGaussianCDF_monotone ht
  · apply ge_of_tendsto standardGaussianCDF_atTop
    filter_upwards [eventually_ge_atTop x] with t ht
    exact standardGaussianCDF_monotone ht

theorem gaussianGeluPositiveProfile_derivative (x : ℝ) :
    HasDerivAt gaussianGeluPositiveProfile (2 * standardGaussianCDF x) x := by
  have h := ((gaussianGelu_hasDerivAt x).fun_add
    (standardGaussianDensity_hasDerivAt x)).const_mul 2
  convert h using 1
  · rfl
  · dsimp [gaussianGeluFirst]
    ring

theorem gaussianGeluNegativeProfile_derivative (x : ℝ) :
    HasDerivAt gaussianGeluNegativeProfile (gaussianGeluNegativeSlope x) x := by
  have h := (gaussianGelu_hasDerivAt x).fun_add
    ((standardGaussianDensity_hasDerivAt x).const_mul 2)
  convert h using 1
  · rfl
  · dsimp [gaussianGeluFirst, gaussianGeluNegativeSlope]
    ring

theorem gaussianGeluNegativeSlope_derivative (x : ℝ) :
    HasDerivAt gaussianGeluNegativeSlope (x ^ 2 * standardGaussianDensity x) x := by
  have h := (standardGaussianCDF_hasDerivAt x).fun_sub
    ((hasDerivAt_id x).fun_mul (standardGaussianDensity_hasDerivAt x))
  convert h using 1
  · rfl
  · dsimp only [id_eq]
    ring

theorem gaussianGeluProfiles_curvature (x : ℝ) :
    curvature gaussianGeluPositiveProfile x = 2 * standardGaussianDensity x ∧
      curvature gaussianGeluNegativeProfile x = x ^ 2 * standardGaussianDensity x := by
  have hp : deriv gaussianGeluPositiveProfile = fun y => 2 * standardGaussianCDF y :=
    funext fun y => (gaussianGeluPositiveProfile_derivative y).deriv
  have hq : deriv gaussianGeluNegativeProfile = gaussianGeluNegativeSlope :=
    funext fun y => (gaussianGeluNegativeProfile_derivative y).deriv
  unfold curvature
  rw [hp, hq]
  exact ⟨((standardGaussianCDF_hasDerivAt x).const_mul 2).deriv,
    (gaussianGeluNegativeSlope_derivative x).deriv⟩

theorem gaussianGeluNegativeSlope_monotone : Monotone gaussianGeluNegativeSlope := by
  apply monotone_of_deriv_nonneg
  · exact fun x => (gaussianGeluNegativeSlope_derivative x).differentiableAt
  · intro x
    rw [(gaussianGeluNegativeSlope_derivative x).deriv]
    exact mul_nonneg (sq_nonneg x) (standardGaussianDensity_pos x).le

theorem gaussianGeluNegativeSlope_atBot :
    Tendsto gaussianGeluNegativeSlope atBot (𝓝 0) := by
  change Tendsto (fun x => standardGaussianCDF x - x * standardGaussianDensity x) atBot (𝓝 0)
  simpa only [sub_zero] using standardGaussianCDF_atBot.sub
    (standardGaussianDensity_mul_id_cocompact.mono_left atBot_le_cocompact)

theorem gaussianGeluNegativeSlope_atTop :
    Tendsto gaussianGeluNegativeSlope atTop (𝓝 1) := by
  change Tendsto (fun x => standardGaussianCDF x - x * standardGaussianDensity x) atTop (𝓝 1)
  simpa only [sub_zero] using standardGaussianCDF_atTop.sub
    (standardGaussianDensity_mul_id_cocompact.mono_left atTop_le_cocompact)

theorem gaussianGeluNegativeSlope_bounds (x : ℝ) :
    0 ≤ gaussianGeluNegativeSlope x ∧ gaussianGeluNegativeSlope x ≤ 1 := by
  constructor
  · apply le_of_tendsto gaussianGeluNegativeSlope_atBot
    filter_upwards [eventually_le_atBot x] with t ht
    exact gaussianGeluNegativeSlope_monotone ht
  · apply ge_of_tendsto gaussianGeluNegativeSlope_atTop
    filter_upwards [eventually_ge_atTop x] with t ht
    exact gaussianGeluNegativeSlope_monotone ht

theorem gaussianGeluPositiveProfile_convex :
    ConvexOn ℝ univ gaussianGeluPositiveProfile := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (gaussianGeluPositiveProfile_derivative x).differentiableAt)
  intro x y hxy
  rw [(gaussianGeluPositiveProfile_derivative x).deriv,
    (gaussianGeluPositiveProfile_derivative y).deriv]
  exact mul_le_mul_of_nonneg_left (standardGaussianCDF_monotone hxy) (by norm_num)

theorem gaussianGeluNegativeProfile_convex :
    ConvexOn ℝ univ gaussianGeluNegativeProfile := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (gaussianGeluNegativeProfile_derivative x).differentiableAt)
  intro x y hxy
  rw [(gaussianGeluNegativeProfile_derivative x).deriv,
    (gaussianGeluNegativeProfile_derivative y).deriv]
  exact gaussianGeluNegativeSlope_monotone hxy

theorem gaussianGeluProfiles_difference (x : ℝ) :
    gaussianGeluPositiveProfile x - gaussianGeluNegativeProfile x = gaussianGelu x := by
  dsimp [gaussianGeluPositiveProfile, gaussianGeluNegativeProfile]
  ring

noncomputable def explicitGaussianGeluPair (z : ℝ × ℝ) : ℝ × ℝ :=
  (asymmetricLift gaussianGeluPositiveProfile 2 z,
    asymmetricLift gaussianGeluNegativeProfile 2 z)

theorem explicitGaussianGeluPair_first_monotone :
    Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).1) := by
  apply asymmetricLift_monotone gaussianGeluPositiveProfile
    (fun x => 2 * standardGaussianCDF x) gaussianGeluPositiveProfile_derivative 2
  intro x
  constructor <;> linarith [(standardGaussianCDF_bounds x).1, (standardGaussianCDF_bounds x).2]

theorem explicitGaussianGeluPair_second_monotone :
    Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).2) := by
  apply asymmetricLift_monotone gaussianGeluNegativeProfile
    gaussianGeluNegativeSlope gaussianGeluNegativeProfile_derivative 2
  intro x
  exact ⟨(gaussianGeluNegativeSlope_bounds x).1,
    (gaussianGeluNegativeSlope_bounds x).2.trans (by norm_num)⟩

theorem explicitGaussianGeluPair_valid :
    ValidPairActivation gaussianGelu explicitGaussianGeluPair := by
  intro a b
  exact asymmetricLift_difference gaussianGeluPositiveProfile gaussianGeluNegativeProfile
    gaussianGelu 2 gaussianGeluProfiles_difference (a, b)

theorem explicitGaussianGeluPair_nonnegative :
    NonnegativePairActivation explicitGaussianGeluPair := by
  intro a b ha hb
  have h0 : 0 ≤ gaussianGeluPositiveProfile 0 ∧ 0 ≤ gaussianGeluNegativeProfile 0 := by
    dsimp [gaussianGeluPositiveProfile, gaussianGeluNegativeProfile, gaussianGelu]
    constructor <;> nlinarith [(standardGaussianDensity_pos 0).le]
  have hp := explicitGaussianGeluPair_first_monotone
    (show ((0, 0) : ℝ × ℝ) ≤ (a, b) from ⟨ha, hb⟩)
  have hq := explicitGaussianGeluPair_second_monotone
    (show ((0, 0) : ℝ × ℝ) ≤ (a, b) from ⟨ha, hb⟩)
  simp only [explicitGaussianGeluPair, asymmetricLift, sub_self, mul_zero, add_zero] at hp hq
  exact ⟨h0.1.trans hp, h0.2.trans hq⟩

/-- Exact closed formulas for both streams, valid on the entire real plane. -/
theorem explicitGaussianGeluPair_formula (x y : ℝ) :
    explicitGaussianGeluPair (x, y) =
      (2 * (gaussianGelu (x - y) + standardGaussianDensity (x - y)) + 2 * y,
        gaussianGelu (x - y) + 2 * standardGaussianDensity (x - y) + 2 * y) := rfl

/-- The root-free closed form supplies convexity, coordinatewise monotonicity,
exact recovery, and preservation of nonnegative network streams. -/
theorem gaussianGelu_explicit_split :
    ConvexOn ℝ univ (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).1) ∧
    ConvexOn ℝ univ (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).2) ∧
    Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).1) ∧
    Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).2) ∧
    ValidPairActivation gaussianGelu explicitGaussianGeluPair ∧
    NonnegativePairActivation explicitGaussianGeluPair :=
  ⟨asymmetricLift_convex _ _ gaussianGeluPositiveProfile_convex,
    asymmetricLift_convex _ _ gaussianGeluNegativeProfile_convex,
    explicitGaussianGeluPair_first_monotone, explicitGaussianGeluPair_second_monotone,
    explicitGaussianGeluPair_valid, explicitGaussianGeluPair_nonnegative⟩

end HiddenMonotonicity.SmoothDC
