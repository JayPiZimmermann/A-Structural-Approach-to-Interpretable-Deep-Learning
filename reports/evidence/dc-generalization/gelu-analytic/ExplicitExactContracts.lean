import HiddenMonotonicity.ExplicitGELU

/-! Handwritten intended signatures and signed-domain consumers for the
closed-form exact-Gaussian GELU lift. No inferred-type emitter is used. -/

set_option autoImplicit false

open Set Filter
open scoped Topology
open HiddenMonotonicity HiddenMonotonicity.SmoothDC

example : ∀ x : ℝ, gaussianGeluPositiveProfile x =
    2 * (gaussianGelu x + standardGaussianDensity x) := fun _ => rfl
example : ∀ x : ℝ, gaussianGeluNegativeProfile x =
    gaussianGelu x + 2 * standardGaussianDensity x := fun _ => rfl
example : ∀ x : ℝ, gaussianGeluNegativeSlope x =
    standardGaussianCDF x - x * standardGaussianDensity x := fun _ => rfl

example : Monotone standardGaussianCDF := @standardGaussianCDF_monotone
example : ∀ x : ℝ, 0 ≤ standardGaussianCDF x ∧ standardGaussianCDF x ≤ 1 :=
  @standardGaussianCDF_bounds
example : ∀ x : ℝ, HasDerivAt gaussianGeluPositiveProfile (2 * standardGaussianCDF x) x :=
  @gaussianGeluPositiveProfile_derivative
example : ∀ x : ℝ, HasDerivAt gaussianGeluNegativeProfile (gaussianGeluNegativeSlope x) x :=
  @gaussianGeluNegativeProfile_derivative
example : ∀ x : ℝ, HasDerivAt gaussianGeluNegativeSlope (x ^ 2 * standardGaussianDensity x) x :=
  @gaussianGeluNegativeSlope_derivative
example : ∀ x : ℝ,
    curvature gaussianGeluPositiveProfile x = 2 * standardGaussianDensity x ∧
      curvature gaussianGeluNegativeProfile x = x ^ 2 * standardGaussianDensity x :=
  @gaussianGeluProfiles_curvature
example : Monotone gaussianGeluNegativeSlope := @gaussianGeluNegativeSlope_monotone
example : Tendsto gaussianGeluNegativeSlope atBot (𝓝 (0 : ℝ)) := @gaussianGeluNegativeSlope_atBot
example : Tendsto gaussianGeluNegativeSlope atTop (𝓝 (1 : ℝ)) := @gaussianGeluNegativeSlope_atTop
example : ∀ x : ℝ, 0 ≤ gaussianGeluNegativeSlope x ∧ gaussianGeluNegativeSlope x ≤ 1 :=
  @gaussianGeluNegativeSlope_bounds
example : ConvexOn ℝ univ gaussianGeluPositiveProfile := @gaussianGeluPositiveProfile_convex
example : ConvexOn ℝ univ gaussianGeluNegativeProfile := @gaussianGeluNegativeProfile_convex
example : ∀ x : ℝ, gaussianGeluPositiveProfile x - gaussianGeluNegativeProfile x = gaussianGelu x :=
  @gaussianGeluProfiles_difference
example : Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).1) :=
  @explicitGaussianGeluPair_first_monotone
example : Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).2) :=
  @explicitGaussianGeluPair_second_monotone
example : ValidPairActivation gaussianGelu explicitGaussianGeluPair := @explicitGaussianGeluPair_valid
example : NonnegativePairActivation explicitGaussianGeluPair := @explicitGaussianGeluPair_nonnegative
example : ∀ x y : ℝ, explicitGaussianGeluPair (x, y) =
    (2 * (gaussianGelu (x - y) + standardGaussianDensity (x - y)) + 2 * y,
      gaussianGelu (x - y) + 2 * standardGaussianDensity (x - y) + 2 * y) :=
  @explicitGaussianGeluPair_formula
example :
    ConvexOn ℝ univ (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).1) ∧
    ConvexOn ℝ univ (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).2) ∧
    Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).1) ∧
    Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).2) ∧
    ValidPairActivation gaussianGelu explicitGaussianGeluPair ∧
    NonnegativePairActivation explicitGaussianGeluPair :=
  @gaussianGelu_explicit_split

-- Zero, negative stream inputs, and nonnegative boundary consumers.
example : explicitGaussianGeluPair (0, 0) =
    (2 * standardGaussianDensity 0, 2 * standardGaussianDensity 0) := by
  rw [explicitGaussianGeluPair_formula]
  simp [gaussianGelu]
example : (explicitGaussianGeluPair (-2, -3)).1 -
    (explicitGaussianGeluPair (-2, -3)).2 = gaussianGelu 1 := by
  have h := explicitGaussianGeluPair_valid (-2) (-3)
  norm_num at h ⊢
  exact h
example : 0 ≤ (explicitGaussianGeluPair (0, 0)).1 ∧
    0 ≤ (explicitGaussianGeluPair (0, 0)).2 :=
  explicitGaussianGeluPair_nonnegative 0 0 le_rfl le_rfl

#print axioms standardGaussianCDF_monotone
#print axioms standardGaussianCDF_bounds
#print axioms gaussianGeluPositiveProfile_derivative
#print axioms gaussianGeluNegativeProfile_derivative
#print axioms gaussianGeluNegativeSlope_derivative
#print axioms gaussianGeluProfiles_curvature
#print axioms gaussianGeluNegativeSlope_monotone
#print axioms gaussianGeluNegativeSlope_atBot
#print axioms gaussianGeluNegativeSlope_atTop
#print axioms gaussianGeluNegativeSlope_bounds
#print axioms gaussianGeluPositiveProfile_convex
#print axioms gaussianGeluNegativeProfile_convex
#print axioms gaussianGeluProfiles_difference
#print axioms explicitGaussianGeluPair_first_monotone
#print axioms explicitGaussianGeluPair_second_monotone
#print axioms explicitGaussianGeluPair_valid
#print axioms explicitGaussianGeluPair_nonnegative
#print axioms explicitGaussianGeluPair_formula
#print axioms gaussianGelu_explicit_split
