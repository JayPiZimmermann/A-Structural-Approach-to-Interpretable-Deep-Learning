import HiddenMonotonicity.ModernSigmoid
import HiddenMonotonicity.MonotoneDCLift
import HiddenMonotonicity.ExplicitSoftplus

set_option maxHeartbeats 600000

namespace HiddenMonotonicity.SmoothDC
open Set Filter
open scoped Topology

/-- The positive-curvature primitive for sigmoid: after its inflection point,
continue with the tangent line of slope `1/4`. -/
noncomputable def sigmoidPositiveProfile (x : ℝ) : ℝ :=
  if x ≤ 0 then Real.sigmoid x else 1 / 2 + x / 4

/-- The negative-curvature primitive, normalized to vanish at zero. -/
noncomputable def sigmoidNegativeProfile (x : ℝ) : ℝ :=
  sigmoidPositiveProfile x - Real.sigmoid x

noncomputable def sigmoidPositiveSlope (x : ℝ) : ℝ :=
  if x ≤ 0 then sigmoidFirst x else 1 / 4

noncomputable def sigmoidNegativeSlope (x : ℝ) : ℝ :=
  sigmoidPositiveSlope x - sigmoidFirst x

theorem sigmoidFirst_le_quarter (x : ℝ) : sigmoidFirst x ≤ 1 / 4 := by
  unfold sigmoidFirst
  nlinarith [sq_nonneg (Real.sigmoid x - 1 / 2)]

theorem sigmoidFirst_monotoneOn_nonpositive : MonotoneOn sigmoidFirst (Iic 0) := by
  intro a ha b hb hab
  have hs := Real.sigmoid_monotone hab
  have hb' := Real.sigmoid_monotone hb
  have ha' := Real.sigmoid_monotone ha
  norm_num at ha' hb'
  have hm := mul_nonneg (sub_nonneg.mpr hs)
    (show 0 ≤ 1 - Real.sigmoid a - Real.sigmoid b by linarith)
  dsimp [sigmoidFirst]
  nlinarith only [hm]

theorem sigmoidFirst_antitoneOn_nonnegative : AntitoneOn sigmoidFirst (Ici 0) := by
  intro a ha b hb hab
  have hs := Real.sigmoid_monotone hab
  have ha' := Real.sigmoid_monotone ha
  have hb' := Real.sigmoid_monotone hb
  norm_num at ha' hb'
  have hm := mul_nonneg (sub_nonneg.mpr hs)
    (show 0 ≤ Real.sigmoid a + Real.sigmoid b - 1 by linarith)
  dsimp [sigmoidFirst]
  nlinarith only [hm]

theorem sigmoidPositiveSlope_bounds (x : ℝ) :
    0 ≤ sigmoidPositiveSlope x ∧ sigmoidPositiveSlope x ≤ 1 / 4 := by
  by_cases hx : x ≤ 0
  · simpa [sigmoidPositiveSlope, hx] using
      And.intro (sigmoidFirst_nonnegative x) (sigmoidFirst_le_quarter x)
  · norm_num [sigmoidPositiveSlope, hx]

theorem sigmoidNegativeSlope_bounds (x : ℝ) :
    0 ≤ sigmoidNegativeSlope x ∧ sigmoidNegativeSlope x ≤ 1 / 4 := by
  by_cases hx : x ≤ 0
  · simp [sigmoidNegativeSlope, sigmoidPositiveSlope, hx]
  · simp only [sigmoidNegativeSlope, sigmoidPositiveSlope, ite_eq_right hx]
    constructor <;> linarith [sigmoidFirst_nonnegative x, sigmoidFirst_le_quarter x]

theorem sigmoidPositiveSlope_monotone : Monotone sigmoidPositiveSlope := by
  intro a b hab
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · simpa [sigmoidPositiveSlope, ha, hb] using
        sigmoidFirst_monotoneOn_nonpositive ha hb hab
    · simpa [sigmoidPositiveSlope, ha, hb] using sigmoidFirst_le_quarter a
  · have hb : ¬b ≤ 0 := by linarith
    simp [sigmoidPositiveSlope, ha, hb]

theorem sigmoidNegativeSlope_monotone : Monotone sigmoidNegativeSlope := by
  intro a b hab
  by_cases ha : a ≤ 0
  · have hz : sigmoidNegativeSlope a = 0 := by
      simp [sigmoidNegativeSlope, sigmoidPositiveSlope, ha]
    rw [hz]
    exact (sigmoidNegativeSlope_bounds b).1
  · have hb : ¬b ≤ 0 := by linarith
    have hs := sigmoidFirst_antitoneOn_nonnegative
      (show a ∈ Ici 0 by exact le_of_lt (lt_of_not_ge ha))
      (show b ∈ Ici 0 by exact le_of_lt (lt_of_not_ge hb)) hab
    simp only [sigmoidNegativeSlope, sigmoidPositiveSlope, ite_eq_right ha, ite_eq_right hb]
    linarith

theorem sigmoidPositiveProfile_derivative_zero :
    HasDerivAt sigmoidPositiveProfile (1 / 4) 0 := by
  have hs : HasDerivAt Real.sigmoid (1 / 4) 0 := by
    convert Real.hasDerivAt_sigmoid 0 using 1
    norm_num
  have hl : HasDerivWithinAt sigmoidPositiveProfile (1 / 4) (Iic 0) 0 := by
    apply hs.hasDerivWithinAt.congr
    · intro y hy
      change y ≤ 0 at hy
      simp [sigmoidPositiveProfile, hy]
    · simp [sigmoidPositiveProfile]
  have ha : HasDerivAt (fun y : ℝ => 1 / 2 + y / 4) (1 / 4) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const 4).const_add (1 / 2)
  have hr : HasDerivWithinAt sigmoidPositiveProfile (1 / 4) (Ici 0) 0 := by
    apply ha.hasDerivWithinAt.congr
    · intro y hy
      by_cases he : y = 0
      · subst y
        norm_num [sigmoidPositiveProfile]
      · have hn : ¬ y ≤ 0 := by change 0 ≤ y at hy; exact lt_of_le_of_ne hy (Ne.symm he) |>.not_ge
        simp [sigmoidPositiveProfile, hn]
    · norm_num [sigmoidPositiveProfile]
  have hu : Iic (0 : ℝ) ∪ Ici 0 = univ := by ext y; simp
  exact hasDerivWithinAt_univ.mp (hu ▸ hl.union hr)

theorem sigmoidPositiveProfile_derivative (x : ℝ) :
    HasDerivAt sigmoidPositiveProfile (sigmoidPositiveSlope x) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have he : sigmoidPositiveProfile =ᶠ[𝓝 x] Real.sigmoid := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      change y < 0 at hy
      simp [sigmoidPositiveProfile, le_of_lt hy]
    simpa [sigmoidPositiveSlope, le_of_lt hx, sigmoidFirst] using
      (Real.hasDerivAt_sigmoid x).congr_of_eventuallyEq he
  · subst x
    convert sigmoidPositiveProfile_derivative_zero using 1
    norm_num [sigmoidPositiveSlope, sigmoidFirst]
  · have he : sigmoidPositiveProfile =ᶠ[𝓝 x] (fun y : ℝ => 1 / 2 + y / 4) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change 0 < y at hy
      simp [sigmoidPositiveProfile, not_le.mpr hy]
    have hd : HasDerivAt (fun y : ℝ => 1 / 2 + y / 4) (1 / 4) x := by
      simpa using ((hasDerivAt_id x).div_const 4).const_add (1 / 2)
    simpa [sigmoidPositiveSlope, not_le.mpr hx] using hd.congr_of_eventuallyEq he

theorem sigmoidNegativeProfile_derivative (x : ℝ) :
    HasDerivAt sigmoidNegativeProfile (sigmoidNegativeSlope x) x := by
  exact (sigmoidPositiveProfile_derivative x).sub (Real.hasDerivAt_sigmoid x)

theorem sigmoidPositiveProfile_convex : ConvexOn ℝ univ sigmoidPositiveProfile := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (sigmoidPositiveProfile_derivative x).differentiableAt)
  intro a b hab
  rw [(sigmoidPositiveProfile_derivative a).deriv,
    (sigmoidPositiveProfile_derivative b).deriv]
  exact sigmoidPositiveSlope_monotone hab

theorem sigmoidNegativeProfile_convex : ConvexOn ℝ univ sigmoidNegativeProfile := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (sigmoidNegativeProfile_derivative x).differentiableAt)
  intro a b hab
  rw [(sigmoidNegativeProfile_derivative a).deriv,
    (sigmoidNegativeProfile_derivative b).deriv]
  exact sigmoidNegativeSlope_monotone hab

/-- Explicit globally convex and coordinatewise monotone sigmoid branches. -/
noncomputable def sigmoidExplicitPair (z : ℝ × ℝ) : ℝ × ℝ :=
  (asymmetricLift sigmoidPositiveProfile (1 / 4) z,
   asymmetricLift sigmoidNegativeProfile (1 / 4) z)

/-- The two lifted branches can be evaluated without integrals or derivatives. -/
theorem sigmoidExplicitPair_closed_form (x y : ℝ) :
    sigmoidExplicitPair (x, y) =
      (if x ≤ y then Real.sigmoid (x - y) + y / 4 else 1 / 2 + x / 4,
       if x ≤ y then y / 4 else 1 / 2 + x / 4 - Real.sigmoid (x - y)) := by
  by_cases hxy : x ≤ y <;>
    ext <;> simp [sigmoidExplicitPair, asymmetricLift, sigmoidPositiveProfile,
      sigmoidNegativeProfile, hxy] <;> ring

theorem sigmoid_explicit_split :
    ConvexOn ℝ univ (fun z => (sigmoidExplicitPair z).1) ∧
    ConvexOn ℝ univ (fun z => (sigmoidExplicitPair z).2) ∧
    Monotone sigmoidExplicitPair ∧ ValidPairActivation Real.sigmoid sigmoidExplicitPair ∧
    NonnegativePairActivation sigmoidExplicitPair := by
  have hp : Monotone (asymmetricLift sigmoidPositiveProfile (1 / 4)) :=
    asymmetricLift_monotone sigmoidPositiveProfile sigmoidPositiveSlope
      sigmoidPositiveProfile_derivative (1 / 4) sigmoidPositiveSlope_bounds
  have hn : Monotone (asymmetricLift sigmoidNegativeProfile (1 / 4)) :=
    asymmetricLift_monotone sigmoidNegativeProfile sigmoidNegativeSlope
      sigmoidNegativeProfile_derivative (1 / 4) sigmoidNegativeSlope_bounds
  refine ⟨asymmetricLift_convex _ _ sigmoidPositiveProfile_convex,
    asymmetricLift_convex _ _ sigmoidNegativeProfile_convex,
    (fun _ _ h => ⟨hp h, hn h⟩), ?_, ?_⟩
  · intro a b
    dsimp [sigmoidExplicitPair, asymmetricLift, sigmoidNegativeProfile]
    ring
  · intro a b ha hb
    have hp' := hp (show ((0, 0) : ℝ × ℝ) ≤ (a, b) from ⟨ha, hb⟩)
    have hn' := hn (show ((0, 0) : ℝ × ℝ) ≤ (a, b) from ⟨ha, hb⟩)
    have hp0 : asymmetricLift sigmoidPositiveProfile (1 / 4) (0, 0) = 1 / 2 := by
      norm_num [asymmetricLift, sigmoidPositiveProfile]
    have hn0 : asymmetricLift sigmoidNegativeProfile (1 / 4) (0, 0) = 0 := by
      norm_num [asymmetricLift, sigmoidNegativeProfile, sigmoidPositiveProfile]
    rw [hp0] at hp'
    rw [hn0] at hn'
    exact ⟨le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hp', hn'⟩

end HiddenMonotonicity.SmoothDC
