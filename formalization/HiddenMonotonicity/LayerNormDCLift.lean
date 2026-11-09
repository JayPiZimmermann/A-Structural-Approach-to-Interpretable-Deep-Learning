import HiddenMonotonicity.MonotoneDCLift
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! A convex monotone lift of the inverse square root used by epsilon LayerNorm.
The affine extension below zero is needed because intermediate DC streams may
vary independently, even though their difference represents a nonnegative variance. -/
noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity.SmoothDC
open Set Filter
open scoped Topology

def inverseSqrtSlope (ε : ℝ) : ℝ := (1 / 2 : ℝ) * ε ^ (-3 / 2 : ℝ)

def inverseSqrtExtension (ε z : ℝ) : ℝ :=
  if z ≤ 0 then ε ^ (-1 / 2 : ℝ) - inverseSqrtSlope ε * z
  else (ε + z) ^ (-1 / 2 : ℝ)

def inverseSqrtExtensionDeriv (ε z : ℝ) : ℝ :=
  if z ≤ 0 then -inverseSqrtSlope ε
  else -(1 / 2 : ℝ) * (ε + z) ^ (-3 / 2 : ℝ)

theorem inverseSqrtSlope_nonneg (ε : ℝ) (hε : 0 < ε) :
    0 ≤ inverseSqrtSlope ε := by
  exact mul_nonneg (by norm_num) (Real.rpow_nonneg hε.le _)

theorem inverseSqrtSlope_eq (ε : ℝ) (hε : 0 < ε) :
    inverseSqrtSlope ε = 1 / (2 * ε ^ (3 / 2 : ℝ)) := by
  unfold inverseSqrtSlope
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, Real.rpow_neg hε.le]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem inverseSqrt_right_deriv (ε z : ℝ) (hε : 0 < ε) (hz : 0 ≤ z) :
    HasDerivAt (fun t : ℝ => (ε + t) ^ (-1 / 2 : ℝ))
      (-(1 / 2 : ℝ) * (ε + z) ^ (-3 / 2 : ℝ)) z := by
  convert ((hasDerivAt_id z).const_add ε).rpow_const
    (p := (-1 / 2 : ℝ)) (Or.inl (ne_of_gt (by linarith : 0 < ε + z))) using 1 <;> norm_num

theorem inverseSqrtExtension_hasDerivAt (ε : ℝ) (hε : 0 < ε) (z : ℝ) :
    HasDerivAt (inverseSqrtExtension ε) (inverseSqrtExtensionDeriv ε z) z := by
  have hl (x : ℝ) : HasDerivAt
      (fun t => ε ^ (-1 / 2 : ℝ) - inverseSqrtSlope ε * t)
      (-inverseSqrtSlope ε) x := by
    convert ((hasDerivAt_id x).const_mul (inverseSqrtSlope ε)).const_sub
      (ε ^ (-1 / 2 : ℝ)) using 1 <;> simp
  rcases lt_trichotomy z 0 with hz | hz | hz
  · simp only [inverseSqrtExtensionDeriv, ite_eq_left hz.le]
    apply (hl z).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hz] with t ht
    simp [inverseSqrtExtension, ht.le]
  · subst z
    have hleft : HasDerivWithinAt (inverseSqrtExtension ε)
        (-inverseSqrtSlope ε) (Iic 0) 0 := by
      apply (hl 0).hasDerivWithinAt.congr
      · intro t ht
        simp [inverseSqrtExtension, show t ≤ 0 from ht]
      · simp [inverseSqrtExtension]
    have hright : HasDerivWithinAt (inverseSqrtExtension ε)
        (-inverseSqrtSlope ε) (Ici 0) 0 := by
      have hh := (inverseSqrt_right_deriv ε 0 hε le_rfl).hasDerivWithinAt (s := Ici 0)
      simp only [add_zero, inverseSqrtSlope, neg_mul] at hh ⊢
      apply hh.congr
      · intro t ht
        by_cases h : t ≤ 0
        · have he : t = 0 := le_antisymm h ht
          simp [he, inverseSqrtExtension]
        · simp [inverseSqrtExtension, h]
      · simp [inverseSqrtExtension]
    have hu : Iic (0 : ℝ) ∪ Ici 0 = univ := by
      ext t
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total t 0
    simpa only [hu, hasDerivWithinAt_univ, inverseSqrtExtensionDeriv, ite_eq_left le_rfl]
      using hleft.union hright
  · simp only [inverseSqrtExtensionDeriv, ite_eq_right (not_le.mpr hz)]
    apply (inverseSqrt_right_deriv ε z hε hz.le).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hz] with t ht
    simp [inverseSqrtExtension, not_le.mpr ht]

theorem inverseSqrtExtensionDeriv_bounds (ε : ℝ) (hε : 0 < ε) (z : ℝ) :
    -inverseSqrtSlope ε ≤ inverseSqrtExtensionDeriv ε z ∧
      inverseSqrtExtensionDeriv ε z ≤ 0 := by
  by_cases hz : z ≤ 0
  · simp only [inverseSqrtExtensionDeriv, ite_eq_left hz, le_refl, true_and]
    exact neg_nonpos.mpr (inverseSqrtSlope_nonneg ε hε)
  · have hpow := Real.rpow_le_rpow_of_nonpos hε
      (show ε ≤ ε + z by linarith) (show (-3 / 2 : ℝ) ≤ 0 by norm_num)
    have hp := Real.rpow_nonneg (show 0 ≤ ε + z by linarith) (-3 / 2 : ℝ)
    simp only [inverseSqrtExtensionDeriv, ite_eq_right hz, inverseSqrtSlope]
    constructor <;> nlinarith

theorem inverseSqrtExtensionDeriv_monotone (ε : ℝ) (hε : 0 < ε) :
    Monotone (inverseSqrtExtensionDeriv ε) := by
  intro x y hxy
  by_cases hx : x ≤ 0
  · by_cases hy : y ≤ 0
    · simp [inverseSqrtExtensionDeriv, hx, hy]
    · simpa only [inverseSqrtExtensionDeriv, ite_eq_left hx] using
        (inverseSqrtExtensionDeriv_bounds ε hε y).1
  · have hy : ¬ y ≤ 0 := by linarith
    have hp := Real.rpow_le_rpow_of_nonpos (show 0 < ε + x by linarith)
      (add_le_add le_rfl hxy) (show (-3 / 2 : ℝ) ≤ 0 by norm_num)
    simp only [inverseSqrtExtensionDeriv, ite_eq_right hx, ite_eq_right hy]
    nlinarith

theorem inverseSqrtExtension_convex (ε : ℝ) (hε : 0 < ε) :
    ConvexOn ℝ univ (inverseSqrtExtension ε) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun z => (inverseSqrtExtension_hasDerivAt ε hε z).differentiableAt)
  intro x y hxy
  rw [(inverseSqrtExtension_hasDerivAt ε hε x).deriv,
    (inverseSqrtExtension_hasDerivAt ε hε y).deriv]
  exact inverseSqrtExtensionDeriv_monotone ε hε hxy

def inverseSqrtProfile (ε z : ℝ) : ℝ :=
  inverseSqrtExtension ε z + inverseSqrtSlope ε * z

def inverseSqrtPair (ε : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (inverseSqrtExtension ε (z.1 - z.2) + inverseSqrtSlope ε * z.1,
    inverseSqrtSlope ε * z.1)

theorem inverseSqrtProfile_hasDerivAt (ε : ℝ) (hε : 0 < ε) (z : ℝ) :
    HasDerivAt (inverseSqrtProfile ε)
      (inverseSqrtExtensionDeriv ε z + inverseSqrtSlope ε) z := by
  change HasDerivAt (fun t => inverseSqrtExtension ε t + inverseSqrtSlope ε * t) _ z
  simpa only [mul_one, id_eq] using
    (inverseSqrtExtension_hasDerivAt ε hε z).fun_add
      ((hasDerivAt_id z).const_mul (inverseSqrtSlope ε))

theorem inverseSqrtProfile_convex (ε : ℝ) (hε : 0 < ε) :
    ConvexOn ℝ univ (inverseSqrtProfile ε) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun z => (inverseSqrtProfile_hasDerivAt ε hε z).differentiableAt)
  intro x y hxy
  rw [(inverseSqrtProfile_hasDerivAt ε hε x).deriv,
    (inverseSqrtProfile_hasDerivAt ε hε y).deriv]
  exact add_le_add (inverseSqrtExtensionDeriv_monotone ε hε hxy) le_rfl

theorem inverseSqrtPair_lifts (ε : ℝ) (z : ℝ × ℝ) :
    inverseSqrtPair ε z =
      (asymmetricLift (inverseSqrtProfile ε) (inverseSqrtSlope ε) z,
       asymmetricLift (fun t => inverseSqrtSlope ε * t) (inverseSqrtSlope ε) z) := by
  ext <;> simp only [inverseSqrtPair, asymmetricLift, inverseSqrtProfile] <;> ring

theorem inverseSqrtPair_monotone (ε : ℝ) (hε : 0 < ε) :
    Monotone (inverseSqrtPair ε) := by
  have hp := asymmetricLift_monotone (inverseSqrtProfile ε)
    (fun z => inverseSqrtExtensionDeriv ε z + inverseSqrtSlope ε)
    (inverseSqrtProfile_hasDerivAt ε hε) (inverseSqrtSlope ε)
    (fun z => by have h := inverseSqrtExtensionDeriv_bounds ε hε z; constructor <;> linarith)
  intro x y hxy
  rw [inverseSqrtPair_lifts, inverseSqrtPair_lifts]
  constructor
  · exact hp hxy
  · simp only [asymmetricLift]
    nlinarith [mul_le_mul_of_nonneg_left hxy.1 (inverseSqrtSlope_nonneg ε hε)]

theorem inverseSqrtPair_convex (ε : ℝ) (hε : 0 < ε) :
    ConvexOn ℝ univ (fun z => (inverseSqrtPair ε z).1) ∧
      ConvexOn ℝ univ (fun z => (inverseSqrtPair ε z).2) := by
  constructor
  · have he : (fun z => (inverseSqrtPair ε z).1) =
        asymmetricLift (inverseSqrtProfile ε) (inverseSqrtSlope ε) := by
      funext z
      rw [inverseSqrtPair_lifts]
    rw [he]
    exact asymmetricLift_convex _ _ (inverseSqrtProfile_convex ε hε)
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [inverseSqrtPair]
    change inverseSqrtSlope ε * (a * x.1 + b * y.1) ≤
      a * (inverseSqrtSlope ε * x.1) + b * (inverseSqrtSlope ε * y.1)
    nlinarith

theorem inverseSqrtExtension_nonneg (ε : ℝ) (hε : 0 < ε) (z : ℝ) :
    0 ≤ inverseSqrtExtension ε z := by
  by_cases hz : z ≤ 0
  · simp only [inverseSqrtExtension, ite_eq_left hz]
    exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos
      (inverseSqrtSlope_nonneg ε hε) hz).trans (Real.rpow_nonneg hε.le _))
  · simp only [inverseSqrtExtension, ite_eq_right hz]
    exact Real.rpow_nonneg (by linarith) _

theorem inverseSqrtPair_nonneg (ε : ℝ) (hε : 0 < ε) (z : ℝ × ℝ)
    (hz : 0 ≤ z) : 0 ≤ inverseSqrtPair ε z := by
  have hm := mul_nonneg (inverseSqrtSlope_nonneg ε hε) hz.1
  exact ⟨add_nonneg (inverseSqrtExtension_nonneg ε hε _) hm, hm⟩

theorem inverseSqrtPair_difference (ε : ℝ) (hε : 0 < ε) (z : ℝ × ℝ)
    (hz : 0 ≤ z.1 - z.2) :
    (inverseSqrtPair ε z).1 - (inverseSqrtPair ε z).2 =
      (Real.sqrt (ε + (z.1 - z.2)))⁻¹ := by
  have he : inverseSqrtExtension ε (z.1 - z.2) =
      (ε + (z.1 - z.2)) ^ (-1 / 2 : ℝ) := by
    by_cases hh : z.1 - z.2 ≤ 0
    · have hz0 : z.1 - z.2 = 0 := le_antisymm hh hz
      simp [hz0, inverseSqrtExtension]
    · simp [inverseSqrtExtension, hh]
  simp only [inverseSqrtPair, add_sub_cancel_right, he, Real.sqrt_eq_rpow]
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg (show 0 ≤ ε + (z.1 - z.2) by linarith)]

/-- The normalization primitive is convex and monotone even when its two
arguments vary independently. Exact inverse-square-root recovery uses only
nonnegativity of the represented variance. -/
theorem inverseSqrtPair_properties (ε : ℝ) (hε : 0 < ε) :
    Monotone (inverseSqrtPair ε) ∧
    ConvexOn ℝ univ (fun z => (inverseSqrtPair ε z).1) ∧
    ConvexOn ℝ univ (fun z => (inverseSqrtPair ε z).2) ∧
    (∀ z : ℝ × ℝ, 0 ≤ z → 0 ≤ inverseSqrtPair ε z) ∧
    (∀ z : ℝ × ℝ, 0 ≤ z.1 - z.2 →
      (inverseSqrtPair ε z).1 - (inverseSqrtPair ε z).2 =
        (Real.sqrt (ε + (z.1 - z.2)))⁻¹) :=
  ⟨inverseSqrtPair_monotone ε hε, (inverseSqrtPair_convex ε hε).1,
    (inverseSqrtPair_convex ε hε).2, inverseSqrtPair_nonneg ε hε,
    inverseSqrtPair_difference ε hε⟩

end HiddenMonotonicity.SmoothDC
