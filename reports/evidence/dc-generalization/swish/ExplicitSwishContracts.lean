import HiddenMonotonicity.ExplicitSwish
import HiddenMonotonicity.SwishSlopeBounds

/-! Independently authored expected propositions and semantic consumers.
These statements were written from the mathematics, not inferred by reflection. -/
namespace SwishClosedContracts
open Set HiddenMonotonicity HiddenMonotonicity.SmoothDC

example : ∀ t : ℝ,
    0 ≤ Real.sigmoid t - t * (Real.sigmoid t * (1 - Real.sigmoid t)) ∧
    Real.sigmoid t - t * (Real.sigmoid t * (1 - Real.sigmoid t)) ≤ 1 := by
  intro t
  exact swishComplementSlope_bounds t

example : ∀ β : ℝ, 0 < β → ∀ z : ℝ,
    HasDerivAt (swishPositiveProfile β) (2 * Real.sigmoid (β*z)) z :=
  swishPositiveProfile_derivative

example : ∀ β : ℝ, 0 < β → ∀ z : ℝ,
    HasDerivAt (swishNegativeProfile β)
      (Real.sigmoid (β*z) - (β*z) * sigmoidFirst (β*z)) z :=
  swishNegativeProfile_derivative

example : ∀ β : ℝ, 0 < β →
    ConvexOn ℝ univ (explicitSwishFirst β) ∧
    ConvexOn ℝ univ (explicitSwishSecond β) ∧
    Monotone (explicitSwishFirst β) ∧ Monotone (explicitSwishSecond β) ∧
    ∀ z : ℝ × ℝ, explicitSwishFirst β z - explicitSwishSecond β z =
      (z.1-z.2) * Real.sigmoid (β*(z.1-z.2)) :=
  explicitSwish_lift

example : ∀ β : ℝ, ∀ z : ℝ × ℝ,
    explicitSwishFirst β z =
      2 / β * Real.log (1 + Real.exp (β * (z.1-z.2))) + 2*z.2 ∧
    explicitSwishSecond β z =
      2 / β * Real.log (1 + Real.exp (β * (z.1-z.2))) -
        (z.1-z.2)*Real.sigmoid (β*(z.1-z.2)) + 2*z.2 :=
  explicitSwish_closed

example : ∀ β : ℝ, ValidPairActivation (swish β) (explicitSwishPair β) :=
  explicitSwishPair_valid

example : ∀ β : ℝ, 0 < β → NonnegativePairActivation (explicitSwishPair β) :=
  explicitSwishPair_nonnegative

example : ∀ β r : ℝ, β ≠ 0 → r*(2*Real.sigmoid r-1)=2 →
    swish β (-(r/β)) - ((2-r)/4)*(-(r/β)) = -(r^2-4)/(4*β) :=
  swish_left_tangent_intercept

example : ∀ β r : ℝ, β ≠ 0 → r*(2*Real.sigmoid r-1)=2 →
    swish β (r/β) - ((2-r)/4)*(r/β) - (r/2)*(r/β) =
      -(r^2-4)/(4*β) :=
  swish_right_tangent_intercept

-- Center values and derivatives independently exercise normalization and scaling.
example : explicitSwishFirst 1 (0,0) = 2 * Real.log 2 ∧
    explicitSwishSecond 1 (0,0) = 2 * Real.log 2 := by
  norm_num [explicitSwishFirst, explicitSwishSecond, asymmetricLift,
    swishPositiveProfile, swishNegativeProfile, Thesis.Regularization.softplus, swish]

example : HasDerivAt (swishPositiveProfile 2) 1 0 := by
  simpa using swishPositiveProfile_derivative 2 (by norm_num) 0

example : HasDerivAt (swishNegativeProfile 2) (1/2) 0 := by
  simpa [swishComplementSlope] using swishNegativeProfile_derivative 2 (by norm_num) 0

-- The signed reconstruction is tested on both sides of the stream diagonal.
example : explicitSwishFirst 2 (1,3) - explicitSwishSecond 2 (1,3) =
    (-2) * Real.sigmoid (-4) := by
  have h := explicitSwishPair_valid 2 1 3
  norm_num [explicitSwishPair, swish] at h ⊢
  exact h

example : explicitSwishFirst 2 (3,1) - explicitSwishSecond 2 (3,1) =
    2 * Real.sigmoid 4 := by
  have h := explicitSwishPair_valid 2 3 1
  norm_num [explicitSwishPair, swish] at h ⊢
  exact h

example (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ explicitSwishFirst 1 (0,x) ∧ 0 ≤ explicitSwishSecond 1 (0,x) :=
  explicitSwishPair_nonnegative 1 (by norm_num) 0 x le_rfl hx

example (c : ℝ) : explicitSwishFirst 1 (c,c) - explicitSwishSecond 1 (c,c) = 0 := by
  simpa [explicitSwishPair, swish] using explicitSwishPair_valid 1 c c

#print axioms swishComplementSlope_bounds
#print axioms swishComplementSlope_derivative
#print axioms swishPositiveProfile_convex
#print axioms swishNegativeProfile_convex
#print axioms explicitSwish_lift
#print axioms explicitSwish_closed
#print axioms explicitSwishPair_valid
#print axioms explicitSwishPair_nonnegative
#print axioms swish_left_tangent_intercept
#print axioms swish_right_tangent_intercept
end SwishClosedContracts
