import HiddenMonotonicity.ModernSwish
import HiddenMonotonicity.MonotoneDCLift
import Thesis.Regularization

/-! An elementary closed DC decomposition for positive-scale Swish.
Twice Softplus is a convex majorant whose difference from Swish is also convex.
This pair does not claim to equal the minimal positive/negative-curvature split. -/
namespace HiddenMonotonicity.SmoothDC
open Set

/-- The slope of the complementary profile in the scaled coordinate. -/
noncomputable def swishComplementSlope (t : ℝ) : ℝ :=
  Real.sigmoid t - t * sigmoidFirst t

theorem swishComplementSlope_nonnegative (t : ℝ) : 0 ≤ swishComplementSlope t := by
  have hs0 := Real.sigmoid_nonneg t
  have hs1 := Real.sigmoid_le_one t
  have he := Real.add_one_le_exp t
  have hid := Real.sigmoid_mul_rexp_neg (-t)
  rw [neg_neg, Real.sigmoid_neg] at hid
  have hb := mul_nonneg (sub_nonneg.mpr hs1)
    (show 0 ≤ 1 + Real.exp t - t by linarith)
  have ht : 0 ≤ 1 - t * (1 - Real.sigmoid t) := by nlinarith only [hb, hid]
  have hp := mul_nonneg hs0 ht
  unfold swishComplementSlope sigmoidFirst
  nlinarith only [hp]

theorem swishComplementSlope_reflect (t : ℝ) :
    swishComplementSlope (-t) = 1 - swishComplementSlope t := by
  simp only [swishComplementSlope, Real.sigmoid_neg, sigmoidFirst_even]
  ring

theorem swishComplementSlope_bounds (t : ℝ) :
    0 ≤ swishComplementSlope t ∧ swishComplementSlope t ≤ 1 := by
  refine ⟨swishComplementSlope_nonnegative t, ?_⟩
  have h := swishComplementSlope_nonnegative (-t)
  rw [swishComplementSlope_reflect] at h
  linarith

theorem swish_scaled_sigmoid_nonnegative (t : ℝ) :
    0 ≤ t * (2 * Real.sigmoid t - 1) := by
  rcases le_total 0 t with ht | ht
  · have hs := Real.sigmoid_monotone ht
    rw [Real.sigmoid_zero] at hs
    apply mul_nonneg ht
    norm_num at hs ⊢
    linarith
  · have hs := Real.sigmoid_monotone ht
    rw [Real.sigmoid_zero] at hs
    apply mul_nonneg_of_nonpos_of_nonpos ht
    norm_num at hs ⊢
    linarith

/-- The positive scalar profile has an elementary log-exp expression. -/
noncomputable def swishPositiveProfile (β z : ℝ) : ℝ :=
  2 * Thesis.Regularization.softplus (1 / β) z

/-- Subtracting Swish from twice Softplus gives the complementary convex profile. -/
noncomputable def swishNegativeProfile (β z : ℝ) : ℝ :=
  swishPositiveProfile β z - swish β z

theorem swishPositiveProfile_closed (β z : ℝ) :
    swishPositiveProfile β z = 2 / β * Real.log (1 + Real.exp (β * z)) := by
  simp only [swishPositiveProfile, Thesis.Regularization.softplus, div_eq_mul_inv,
    one_mul, inv_inv]
  rw [mul_comm z β]
  ring

theorem swishNegativeProfile_closed (β z : ℝ) :
    swishNegativeProfile β z =
      2 / β * Real.log (1 + Real.exp (β * z)) - z * Real.sigmoid (β * z) := by
  rw [swishNegativeProfile, swishPositiveProfile_closed]
  rfl

theorem swishPositiveProfile_derivative (β : ℝ) (hβ : 0 < β) (z : ℝ) :
    HasDerivAt (swishPositiveProfile β) (2 * Real.sigmoid (β * z)) z := by
  convert (Thesis.Regularization.hasDerivAt_softplus (1 / β) z (by positivity)).const_mul 2 using 1
  · rfl
  · simp [Thesis.Regularization.gate, mul_comm]

theorem swishNegativeProfile_derivative (β : ℝ) (hβ : 0 < β) (z : ℝ) :
    HasDerivAt (swishNegativeProfile β) (swishComplementSlope (β * z)) z := by
  convert (swishPositiveProfile_derivative β hβ z).sub (swish_hasDerivAt β z) using 1
  · rfl
  · unfold swishComplementSlope swishFirst
    ring

theorem swishComplementSlope_derivative (β z : ℝ) :
    HasDerivAt (fun t => swishComplementSlope (β * t))
      (β * sigmoidFirst (β * z) * ((β * z) * (2 * Real.sigmoid (β * z) - 1))) z := by
  have h := (((Real.hasDerivAt_sigmoid (β*z)).comp z
    ((hasDerivAt_id z).const_mul β)).const_mul 2).sub (swishFirst_hasDerivAt β z)
  convert h using 1
  · funext t
    dsimp [swishComplementSlope, swishFirst, Function.comp_def]
    ring
  · unfold swishSecond sigmoidFirst
    ring

theorem swishComplementSlope_monotone (β : ℝ) (hβ : 0 < β) :
    Monotone (fun t => swishComplementSlope (β * t)) := by
  apply monotone_of_hasDerivAt_nonneg (swishComplementSlope_derivative β)
  intro t
  exact mul_nonneg (mul_nonneg hβ.le (sigmoidFirst_nonnegative _))
    (swish_scaled_sigmoid_nonnegative _)

theorem swishPositiveProfile_convex (β : ℝ) (hβ : 0 < β) :
    ConvexOn ℝ univ (swishPositiveProfile β) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (swishPositiveProfile_derivative β hβ x).differentiableAt)
  intro a b hab
  rw [(swishPositiveProfile_derivative β hβ a).deriv,
    (swishPositiveProfile_derivative β hβ b).deriv]
  exact mul_le_mul_of_nonneg_left
    (Real.sigmoid_monotone (mul_le_mul_of_nonneg_left hab hβ.le)) (by norm_num)

theorem swishNegativeProfile_convex (β : ℝ) (hβ : 0 < β) :
    ConvexOn ℝ univ (swishNegativeProfile β) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (swishNegativeProfile_derivative β hβ x).differentiableAt)
  intro a b hab
  rw [(swishNegativeProfile_derivative β hβ a).deriv,
    (swishNegativeProfile_derivative β hβ b).deriv]
  exact swishComplementSlope_monotone β hβ hab

noncomputable def explicitSwishFirst (β : ℝ) : (ℝ × ℝ) → ℝ :=
  asymmetricLift (swishPositiveProfile β) 2

noncomputable def explicitSwishSecond (β : ℝ) : (ℝ × ℝ) → ℝ :=
  asymmetricLift (swishNegativeProfile β) 2

noncomputable def explicitSwishPair (β : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (explicitSwishFirst β z, explicitSwishSecond β z)

theorem explicitSwishPair_valid (β : ℝ) :
    ValidPairActivation (swish β) (explicitSwishPair β) := by
  intro x y
  simp only [explicitSwishPair, explicitSwishFirst, explicitSwishSecond,
    asymmetricLift, swishNegativeProfile]
  ring

/-- Both branches are globally convex and coordinatewise nondecreasing. -/
theorem explicitSwish_lift (β : ℝ) (hβ : 0 < β) :
    ConvexOn ℝ univ (explicitSwishFirst β) ∧
    ConvexOn ℝ univ (explicitSwishSecond β) ∧
    Monotone (explicitSwishFirst β) ∧ Monotone (explicitSwishSecond β) ∧
    ∀ z : ℝ × ℝ, explicitSwishFirst β z - explicitSwishSecond β z =
      swish β (z.1 - z.2) := by
  refine ⟨asymmetricLift_convex _ _ (swishPositiveProfile_convex β hβ),
    asymmetricLift_convex _ _ (swishNegativeProfile_convex β hβ), ?_, ?_, ?_⟩
  · apply asymmetricLift_monotone _ _ (swishPositiveProfile_derivative β hβ)
    intro x
    constructor
    · exact mul_nonneg (by norm_num) (Real.sigmoid_nonneg _)
    · linarith [Real.sigmoid_le_one (β*x)]
  · apply asymmetricLift_monotone _ _ (swishNegativeProfile_derivative β hβ)
    intro x
    have h := swishComplementSlope_bounds (β*x)
    exact ⟨h.1, by linarith [h.2]⟩
  · intro z
    exact explicitSwishPair_valid β z.1 z.2

/-- The elementary formulas, written directly in the two input streams. -/
theorem explicitSwish_closed (β : ℝ) (z : ℝ × ℝ) :
    explicitSwishFirst β z =
      2 / β * Real.log (1 + Real.exp (β * (z.1 - z.2))) + 2 * z.2 ∧
    explicitSwishSecond β z =
      2 / β * Real.log (1 + Real.exp (β * (z.1 - z.2))) -
        (z.1 - z.2) * Real.sigmoid (β * (z.1 - z.2)) + 2 * z.2 := by
  simp only [explicitSwishFirst, explicitSwishSecond, asymmetricLift,
    swishPositiveProfile_closed, swishNegativeProfile_closed, and_self]

theorem explicitSwishPair_nonnegative (β : ℝ) (hβ : 0 < β) :
    NonnegativePairActivation (explicitSwishPair β) := by
  have hbase : 0 ≤ swishPositiveProfile β 0 := by
    rw [swishPositiveProfile_closed]
    simp only [mul_zero, Real.exp_zero]
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by norm_num)
  have hs := explicitSwish_lift β hβ
  intro x y hx hy
  have h₁ := hs.2.2.1 (show ((0,0) : ℝ × ℝ) ≤ (x,y) from ⟨hx,hy⟩)
  have h₂ := hs.2.2.2.1 (show ((0,0) : ℝ × ℝ) ≤ (x,y) from ⟨hx,hy⟩)
  have hp0 : explicitSwishFirst β (0,0) = swishPositiveProfile β 0 := by
    simp [explicitSwishFirst, asymmetricLift]
  have hq0 : explicitSwishSecond β (0,0) = swishPositiveProfile β 0 := by
    simp [explicitSwishSecond, asymmetricLift, swishNegativeProfile, swish]
  rw [hp0] at h₁
  rw [hq0] at h₂
  exact ⟨hbase.trans h₁, hbase.trans h₂⟩

end HiddenMonotonicity.SmoothDC
