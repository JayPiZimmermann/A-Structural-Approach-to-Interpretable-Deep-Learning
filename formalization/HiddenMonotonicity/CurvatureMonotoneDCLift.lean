import HiddenMonotonicity.MonotoneDCLift
import HiddenMonotonicity.SmoothCurvatureSplit
import HiddenMonotonicity.Decomposition

/-! An asymmetric monotone DC lift built from the actual Jordan curvature
primitives.  Its common coefficient is an explicit total-curvature integral.
The established symmetric lift remains available as a separate construction. -/

namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory

noncomputable def totalPositiveCurvature (f : ℝ → ℝ) : ℝ :=
  ∫ t, positiveCurvature f t

noncomputable def totalNegativeCurvature (f : ℝ → ℝ) : ℝ :=
  ∫ t, negativeCurvature f t

noncomputable def curvatureSlopeShift (f : ℝ → ℝ) : ℝ :=
  max (-minusInfinitySlope f) 0

noncomputable def curvatureLiftWidth (f : ℝ → ℝ) : ℝ :=
  max (minusInfinitySlope f + curvatureSlopeShift f + totalPositiveCurvature f)
    (curvatureSlopeShift f + totalNegativeCurvature f)

noncomputable def curvaturePositiveProfile (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  C1 f x + curvatureSlopeShift f * x

noncomputable def curvatureNegativeProfile (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  C2 f x + curvatureSlopeShift f * x

noncomputable def curvatureLiftPair (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (asymmetricLift (curvaturePositiveProfile f) (curvatureLiftWidth f) z,
   asymmetricLift (curvatureNegativeProfile f) (curvatureLiftWidth f) z)

theorem positiveCurvature_eq_absolute (f : ℝ → ℝ) (x : ℝ) :
    positiveCurvature f x = (|curvature f x| + curvature f x) / 2 := by
  rcases le_total (curvature f x) 0 with h | h
  · simp [positiveCurvature, max_eq_right h, abs_of_nonpos h]
  · rw [abs_of_nonneg h]
    simp only [positiveCurvature, max_eq_left h]
    ring

theorem negativeCurvature_eq_absolute (f : ℝ → ℝ) (x : ℝ) :
    negativeCurvature f x = (|curvature f x| - curvature f x) / 2 := by
  rcases le_total (curvature f x) 0 with h | h
  · rw [abs_of_nonpos h]
    simp only [negativeCurvature, max_eq_left (neg_nonneg.mpr h)]
    ring
  · simp [negativeCurvature, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]

/-- The total curvature used by the construction is exactly the integral of
the absolute second derivative, rather than an unrelated envelope. -/
theorem total_curvature_eq_absolute (f : ℝ → ℝ) (hq : Integrable (curvature f)) :
    totalPositiveCurvature f + totalNegativeCurvature f = ∫ t, |curvature f t| := by
  unfold totalPositiveCurvature totalNegativeCurvature
  rw [← integral_add (positiveCurvature_integrable f hq)
    (negativeCurvature_integrable f hq)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [positiveCurvature_eq_absolute, negativeCurvature_eq_absolute]
    ring)

theorem curvatureSlopeShift_nonneg (f : ℝ → ℝ) : 0 ≤ curvatureSlopeShift f :=
  le_max_right _ _

theorem totalPositiveCurvature_nonneg (f : ℝ → ℝ) :
    0 ≤ totalPositiveCurvature f := by
  exact integral_nonneg (fun t => le_max_right (curvature f t) 0)

theorem totalNegativeCurvature_nonneg (f : ℝ → ℝ) :
    0 ≤ totalNegativeCurvature f := by
  exact integral_nonneg (fun t => le_max_right (-curvature f t) 0)

theorem curvatureLiftWidth_nonneg (f : ℝ → ℝ) : 0 ≤ curvatureLiftWidth f := by
  exact le_trans (add_nonneg (curvatureSlopeShift_nonneg f)
    (totalNegativeCurvature_nonneg f)) (le_max_right _ _)

/-- The integrated positive and negative curvature yield nonnegative bounded
slopes after the same linear shift. -/
theorem curvature_profile_slope_bounds (f : ℝ → ℝ) (hq : Integrable (curvature f))
    (x : ℝ) :
    (0 ≤ D1 f x + curvatureSlopeShift f ∧
      D1 f x + curvatureSlopeShift f ≤ curvatureLiftWidth f) ∧
    (0 ≤ D2 f x + curvatureSlopeShift f ∧
      D2 f x + curvatureSlopeShift f ≤ curvatureLiftWidth f) := by
  have hp0 : 0 ≤ cumulative (positiveCurvature f) x := by
    exact integral_nonneg (fun t => le_max_right (curvature f t) 0)
  have hn0 : 0 ≤ cumulative (negativeCurvature f) x := by
    exact integral_nonneg (fun t => le_max_right (-curvature f t) 0)
  have hp : cumulative (positiveCurvature f) x ≤ totalPositiveCurvature f := by
    exact setIntegral_le_integral (positiveCurvature_integrable f hq)
      (Eventually.of_forall (fun t => le_max_right (curvature f t) 0))
  have hn : cumulative (negativeCurvature f) x ≤ totalNegativeCurvature f := by
    exact setIntegral_le_integral (negativeCurvature_integrable f hq)
      (Eventually.of_forall (fun t => le_max_right (-curvature f t) 0))
  have hs : -minusInfinitySlope f ≤ curvatureSlopeShift f := le_max_left _ _
  have ha := curvatureSlopeShift_nonneg f
  have hwp : minusInfinitySlope f + curvatureSlopeShift f + totalPositiveCurvature f ≤
      curvatureLiftWidth f := le_max_left _ _
  have hwn : curvatureSlopeShift f + totalNegativeCurvature f ≤ curvatureLiftWidth f :=
    le_max_right _ _
  dsimp [D1, D2, slope]
  constructor <;> constructor <;> linarith

theorem curvaturePositiveProfile_hasDerivAt (f : ℝ → ℝ)
    (hq : Integrable (curvature f)) (x : ℝ) :
    HasDerivAt (curvaturePositiveProfile f) (D1 f x + curvatureSlopeShift f) x := by
  have h := (C1_hasDerivAt f hq x).fun_add
    ((hasDerivAt_id x).const_mul (curvatureSlopeShift f))
  convert h using 1
  · funext t
    simp [curvaturePositiveProfile, id_eq]
  · ring

theorem curvatureNegativeProfile_hasDerivAt (f : ℝ → ℝ)
    (hq : Integrable (curvature f)) (x : ℝ) :
    HasDerivAt (curvatureNegativeProfile f) (D2 f x + curvatureSlopeShift f) x := by
  have h := (C2_hasDerivAt f hq x).fun_add
    ((hasDerivAt_id x).const_mul (curvatureSlopeShift f))
  convert h using 1
  · funext t
    simp [curvatureNegativeProfile, id_eq]
  · ring

theorem curvaturePositiveProfile_convex (f : ℝ → ℝ)
    (hq : Integrable (curvature f)) : ConvexOn ℝ univ (curvaturePositiveProfile f) := by
  have hc : ConvexOn ℝ univ (C1 f) :=
    primitive_convex _ (positiveCurvature_integrable f hq) (fun x => le_max_right _ _) _ _
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    have h := hc.2 hx hy ha hb hab
    simp only [smul_eq_mul] at h ⊢
    dsimp [curvaturePositiveProfile]
    nlinarith only [h]

theorem curvatureNegativeProfile_convex (f : ℝ → ℝ)
    (hq : Integrable (curvature f)) : ConvexOn ℝ univ (curvatureNegativeProfile f) := by
  have hc : ConvexOn ℝ univ (C2 f) :=
    primitive_convex _ (negativeCurvature_integrable f hq) (fun x => le_max_right _ _) _ _
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    have h := hc.2 hx hy ha hb hab
    simp only [smul_eq_mul] at h ⊢
    dsimp [curvatureNegativeProfile]
    nlinarith only [h]

theorem curvature_profile_difference (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) (x : ℝ) :
    curvaturePositiveProfile f x - curvatureNegativeProfile f x = f x := by
  have h := primitive_difference f hf hAC hq x
  dsimp [curvaturePositiveProfile, curvatureNegativeProfile]
  linarith

/-- The actual curvature construction provides a convex, coordinatewise
nondecreasing pair on all of ℝ², not just on the nonnegative quadrant. -/
theorem curvature_monotone_dc_split (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) :
    ConvexOn ℝ univ (fun z => (curvatureLiftPair f z).1) ∧
    ConvexOn ℝ univ (fun z => (curvatureLiftPair f z).2) ∧
    Monotone (fun z => (curvatureLiftPair f z).1) ∧
    Monotone (fun z => (curvatureLiftPair f z).2) ∧
    ValidPairActivation f (curvatureLiftPair f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact asymmetricLift_convex _ _ (curvaturePositiveProfile_convex f hq)
  · exact asymmetricLift_convex _ _ (curvatureNegativeProfile_convex f hq)
  · exact asymmetricLift_monotone _ _ (curvaturePositiveProfile_hasDerivAt f hq) _
      (fun x => (curvature_profile_slope_bounds f hq x).1)
  · exact asymmetricLift_monotone _ _ (curvatureNegativeProfile_hasDerivAt f hq) _
      (fun x => (curvature_profile_slope_bounds f hq x).2)
  · intro x y
    have h := curvature_profile_difference f hf hAC hq (x-y)
    dsimp [curvatureLiftPair, asymmetricLift]
    linarith

/-- Normalization at the origin is sufficient for nonnegative stream outputs
on nonnegative stream inputs. -/
theorem curvatureLiftPair_nonnegative (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) (hzero : 0 ≤ f 0) :
    NonnegativePairActivation (curvatureLiftPair f) := by
  intro a b ha hb
  have hs := curvature_monotone_dc_split f hf hAC hq
  have hg := hs.2.2.1 (show ((0,0) : ℝ × ℝ) ≤ (a,b) from ⟨ha,hb⟩)
  have hh := hs.2.2.2.1 (show ((0,0) : ℝ × ℝ) ≤ (a,b) from ⟨ha,hb⟩)
  have hg0 : (curvatureLiftPair f (0,0)).1 = f 0 := by
    simp [curvatureLiftPair, asymmetricLift, curvaturePositiveProfile, C1, primitive]
  have hh0 : (curvatureLiftPair f (0,0)).2 = 0 := by
    simp [curvatureLiftPair, asymmetricLift, curvatureNegativeProfile, C2, primitive]
  dsimp only at hg hh
  rw [hg0] at hg
  rw [hh0] at hh
  exact ⟨le_trans hzero hg, hh⟩

/-- A common constant offset retains the exact difference and makes both
streams nonnegative on nonnegative inputs, with no sign condition on `f 0`. -/
noncomputable def normalizedCurvatureLiftPair (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((curvatureLiftPair f z).1 + max (-f 0) 0,
   (curvatureLiftPair f z).2 + max (-f 0) 0)

theorem normalized_curvature_monotone_dc_split (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) :
    ConvexOn ℝ univ (fun z => (normalizedCurvatureLiftPair f z).1) ∧
    ConvexOn ℝ univ (fun z => (normalizedCurvatureLiftPair f z).2) ∧
    Monotone (fun z => (normalizedCurvatureLiftPair f z).1) ∧
    Monotone (fun z => (normalizedCurvatureLiftPair f z).2) ∧
    ValidPairActivation f (normalizedCurvatureLiftPair f) := by
  have hs := curvature_monotone_dc_split f hf hAC hq
  refine ⟨hs.1.add_const _, hs.2.1.add_const _, ?_, ?_, ?_⟩
  · intro a b hab
    exact add_le_add (hs.2.2.1 hab) le_rfl
  · intro a b hab
    exact add_le_add (hs.2.2.2.1 hab) le_rfl
  · intro a b
    have h := hs.2.2.2.2 a b
    dsimp [normalizedCurvatureLiftPair]
    linarith

theorem normalizedCurvatureLiftPair_nonnegative (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) :
    NonnegativePairActivation (normalizedCurvatureLiftPair f) := by
  intro a b ha hb
  have hs := normalized_curvature_monotone_dc_split f hf hAC hq
  have hg := hs.2.2.1 (show ((0,0) : ℝ × ℝ) ≤ (a,b) from ⟨ha,hb⟩)
  have hh := hs.2.2.2.1 (show ((0,0) : ℝ × ℝ) ≤ (a,b) from ⟨ha,hb⟩)
  have hg0 : (normalizedCurvatureLiftPair f (0,0)).1 = f 0 + max (-f 0) 0 := by
    simp [normalizedCurvatureLiftPair, curvatureLiftPair, asymmetricLift,
      curvaturePositiveProfile, C1, primitive]
  have hh0 : (normalizedCurvatureLiftPair f (0,0)).2 = max (-f 0) 0 := by
    simp [normalizedCurvatureLiftPair, curvatureLiftPair, asymmetricLift,
      curvatureNegativeProfile, C2, primitive]
  dsimp only at hg hh
  rw [hg0] at hg
  rw [hh0] at hh
  have hc : -f 0 ≤ max (-f 0) 0 := le_max_left _ _
  have hc0 : 0 ≤ max (-f 0) 0 := le_max_right _ _
  exact ⟨le_trans (by linarith) hg, le_trans hc0 hh⟩

end HiddenMonotonicity.SmoothDC
