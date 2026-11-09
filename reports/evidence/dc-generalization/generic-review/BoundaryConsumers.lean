import HiddenMonotonicity.MonotoneDCLift

set_option autoImplicit false

open Set HiddenMonotonicity HiddenMonotonicity.SmoothDC

namespace GenericLiftBoundaryReview

-- All signed ReLU cases and the corner are checked against the actual definition.
theorem relu_negative_inputs :
    asymmetricLift relu 1 (-3, -2) = -2 ∧
    asymmetricLift (fun _ => 0) 1 (-3, -2) = -2 ∧
    asymmetricLift relu 1 (-2, -3) = -2 ∧
    asymmetricLift (fun _ => 0) 1 (-2, -3) = -3 := by
  norm_num [asymmetricLift, relu]

theorem relu_opposite_sign_inputs :
    asymmetricLift relu 1 (-2, 3) = 3 ∧
    asymmetricLift relu 1 (3, -2) = 3 ∧
    asymmetricLift relu 1 (0, 0) = 0 := by
  norm_num [asymmetricLift, relu]

-- The zero-width case is satisfiable, with a constant profile.
theorem zero_width_constant :
    ConvexOn ℝ univ (asymmetricLift (fun _ => (3 : ℝ)) 0) ∧
    Monotone (asymmetricLift (fun _ => (3 : ℝ)) 0) := by
  constructor
  · exact asymmetricLift_convex _ _ (convexOn_const 3 convex_univ)
  · apply (asymmetricLift_monotone_iff_increments _ _).2
    intro a b hab
    norm_num

-- Width zero cannot absorb the negative second-coordinate derivative of C(t)=t.
theorem insufficient_width :
    ¬ Monotone (asymmetricLift (fun t : ℝ => t) 0) := by
  intro h
  have hc := h (show ((0, 0) : ℝ × ℝ) ≤ (0, 1) by constructor <;> norm_num)
  norm_num [asymmetricLift] at hc

-- A negative width fails even for constant profiles.
theorem negative_width :
    ¬ Monotone (asymmetricLift (fun _ : ℝ => 0) (-1)) := by
  intro h
  have hc := h (show ((0, 0) : ℝ × ℝ) ≤ (1, 1) by constructor <;> norm_num)
  norm_num [asymmetricLift] at hc

-- Convexity of the profile is essential: C(t)=-t² violates Jensen.
theorem profile_convexity_is_required (L : ℝ) :
    ¬ ConvexOn ℝ univ (asymmetricLift (fun t : ℝ => -(t ^ 2)) L) := by
  intro h
  have hp := (asymmetricLift_convex_iff _ _).1 h
  have hc := hp.2 (mem_univ (-1 : ℝ)) (mem_univ (1 : ℝ))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num [smul_eq_mul] at hc

-- The common-shift law includes negative shifts without an orthant restriction.
theorem negative_common_shift (C : ℝ → ℝ) (L x y : ℝ) :
    asymmetricLift C L (x - 5, y - 5) = asymmetricLift C L (x, y) - 5 * L := by
  have h := asymmetricLift_common_shift C L x y (-5)
  convert h using 1 <;> ring

-- Concrete abstract-constructor consumer: P=t, Q=0 gives f=t, using width one.
theorem identity_reconstruction :
    ConvexOn ℝ univ (asymmetricLift (fun t : ℝ => t) 1) ∧
    ConvexOn ℝ univ (asymmetricLift (fun _ : ℝ => 0) 1) ∧
    Monotone (asymmetricLift (fun t : ℝ => t) 1) ∧
    Monotone (asymmetricLift (fun _ : ℝ => 0) 1) ∧
    ∀ z : ℝ × ℝ, asymmetricLift (fun t : ℝ => t) 1 z -
      asymmetricLift (fun _ : ℝ => 0) 1 z = z.1 - z.2 := by
  apply asymmetric_split (fun t : ℝ => t) (fun _ : ℝ => 0) (fun t : ℝ => t) 1
  · exact convexOn_id convex_univ
  · exact convexOn_const 0 convex_univ
  · intro a b hab
    constructor
    · exact sub_nonneg.mpr hab
    · simp
  · intro a b hab
    constructor
    · simp
    · simpa using sub_nonneg.mpr hab
  · intro t
    simp

end GenericLiftBoundaryReview
