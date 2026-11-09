import HiddenMonotonicity.ExplicitSoftplus
import HiddenMonotonicity.MonotoneDCLift

/-! A smooth, root-free sigmoid split.  The positive and negative profiles use
only Softplus and sigmoid; their common slope bound is one half. -/

namespace HiddenMonotonicity.SmoothDC
open Set

noncomputable def sigmoidSmoothP (x : ℝ) : ℝ :=
  (Thesis.Regularization.softplus 1 x + Real.sigmoid x) / 2

noncomputable def sigmoidSmoothQ (x : ℝ) : ℝ :=
  (Thesis.Regularization.softplus 1 x - Real.sigmoid x) / 2

noncomputable def sigmoidSmoothPFirst (x : ℝ) : ℝ :=
  Real.sigmoid x - Real.sigmoid x ^ 2 / 2

noncomputable def sigmoidSmoothQFirst (x : ℝ) : ℝ :=
  Real.sigmoid x ^ 2 / 2

theorem sigmoidSmooth_profiles_contDiff :
    ContDiff ℝ ⊤ sigmoidSmoothP ∧ ContDiff ℝ ⊤ sigmoidSmoothQ := by
  have he : ContDiff ℝ ⊤ (fun x : ℝ => 1 + Real.exp x) := by fun_prop
  have hs := he.log (fun x => by positivity : ∀ x : ℝ, 1 + Real.exp x ≠ 0)
  have hsig : ContDiff ℝ ⊤ Real.sigmoid := contDiff_sigmoid.of_le le_top
  constructor
  · change ContDiff ℝ ⊤ (fun x => (Thesis.Regularization.softplus 1 x + Real.sigmoid x) / 2)
    simpa [Thesis.Regularization.softplus] using
      (hs.add hsig).div_const 2
  · change ContDiff ℝ ⊤ (fun x => (Thesis.Regularization.softplus 1 x - Real.sigmoid x) / 2)
    simpa [Thesis.Regularization.softplus] using
      (hs.sub hsig).div_const 2

theorem sigmoidSmoothP_derivative (x : ℝ) :
    HasDerivAt sigmoidSmoothP (sigmoidSmoothPFirst x) x := by
  have hs : HasDerivAt (Thesis.Regularization.softplus 1) (Real.sigmoid x) x := by
    simpa [Thesis.Regularization.gate] using
      Thesis.Regularization.hasDerivAt_softplus 1 x (by norm_num)
  convert (hs.add (Real.hasDerivAt_sigmoid x)).div_const 2 using 1
  · rfl
  · unfold sigmoidSmoothPFirst
    ring

theorem sigmoidSmoothQ_derivative (x : ℝ) :
    HasDerivAt sigmoidSmoothQ (sigmoidSmoothQFirst x) x := by
  have hs : HasDerivAt (Thesis.Regularization.softplus 1) (Real.sigmoid x) x := by
    simpa [Thesis.Regularization.gate] using
      Thesis.Regularization.hasDerivAt_softplus 1 x (by norm_num)
  convert (hs.sub (Real.hasDerivAt_sigmoid x)).div_const 2 using 1
  · rfl
  · unfold sigmoidSmoothQFirst
    ring

theorem sigmoidSmoothPFirst_derivative (x : ℝ) :
    HasDerivAt sigmoidSmoothPFirst (sigmoidFirst x * (1 - Real.sigmoid x)) x := by
  have h := Real.hasDerivAt_sigmoid x
  convert h.sub ((h.pow 2).div_const 2) using 1
  · rfl
  · unfold sigmoidFirst
    ring

theorem sigmoidSmoothQFirst_derivative (x : ℝ) :
    HasDerivAt sigmoidSmoothQFirst (Real.sigmoid x * sigmoidFirst x) x := by
  convert ((Real.hasDerivAt_sigmoid x).pow 2).div_const 2 using 1
  · rfl
  · unfold sigmoidFirst
    ring

theorem sigmoidSmoothPFirst_bounds (x : ℝ) :
    0 ≤ sigmoidSmoothPFirst x ∧ sigmoidSmoothPFirst x ≤ 1 / 2 := by
  have h0 := Real.sigmoid_nonneg x
  have h1 := Real.sigmoid_le_one x
  have hsq := sq_nonneg (1 - Real.sigmoid x)
  have hp := mul_nonneg h0 (sub_nonneg.mpr h1)
  dsimp [sigmoidSmoothPFirst]
  constructor <;> nlinarith only [h0, h1, hsq, hp]

theorem sigmoidSmoothQFirst_bounds (x : ℝ) :
    0 ≤ sigmoidSmoothQFirst x ∧ sigmoidSmoothQFirst x ≤ 1 / 2 := by
  have h0 := Real.sigmoid_nonneg x
  have h1 := Real.sigmoid_le_one x
  have hp := mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ 1 + Real.sigmoid x by linarith)
  dsimp [sigmoidSmoothQFirst]
  constructor
  · positivity
  · nlinarith only [hp]

theorem sigmoidSmoothPFirst_monotone : Monotone sigmoidSmoothPFirst := by
  apply monotone_of_deriv_nonneg
  · exact fun x => (sigmoidSmoothPFirst_derivative x).differentiableAt
  · intro x
    rw [(sigmoidSmoothPFirst_derivative x).deriv]
    exact mul_nonneg (sigmoidFirst_nonnegative x)
      (sub_nonneg.mpr (Real.sigmoid_le_one x))

theorem sigmoidSmoothQFirst_monotone : Monotone sigmoidSmoothQFirst := by
  apply monotone_of_deriv_nonneg
  · exact fun x => (sigmoidSmoothQFirst_derivative x).differentiableAt
  · intro x
    rw [(sigmoidSmoothQFirst_derivative x).deriv]
    exact mul_nonneg (Real.sigmoid_nonneg x) (sigmoidFirst_nonnegative x)

theorem sigmoidSmoothP_convex : ConvexOn ℝ univ sigmoidSmoothP := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (sigmoidSmoothP_derivative x).differentiableAt)
  intro a b hab
  rw [(sigmoidSmoothP_derivative a).deriv, (sigmoidSmoothP_derivative b).deriv]
  exact sigmoidSmoothPFirst_monotone hab

theorem sigmoidSmoothQ_convex : ConvexOn ℝ univ sigmoidSmoothQ := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (sigmoidSmoothQ_derivative x).differentiableAt)
  intro a b hab
  rw [(sigmoidSmoothQ_derivative a).deriv, (sigmoidSmoothQ_derivative b).deriv]
  exact sigmoidSmoothQFirst_monotone hab

theorem sigmoidSmooth_profile_difference (x : ℝ) :
    sigmoidSmoothP x - sigmoidSmoothQ x = Real.sigmoid x := by
  unfold sigmoidSmoothP sigmoidSmoothQ
  ring

/-- Both profiles have nonnegative values at the origin, so the monotone lift
preserves the nonnegative quadrant without adding a normalization constant. -/
theorem sigmoidSmooth_profiles_zero_nonnegative :
    0 ≤ sigmoidSmoothP 0 ∧ 0 ≤ sigmoidSmoothQ 0 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at h ⊢
    exact h
  norm_num [sigmoidSmoothP, sigmoidSmoothQ, Thesis.Regularization.softplus]
  constructor <;> linarith

noncomputable def explicitSigmoidSmoothPair (z : ℝ × ℝ) : ℝ × ℝ :=
  (asymmetricLift sigmoidSmoothP (1 / 2) z,
   asymmetricLift sigmoidSmoothQ (1 / 2) z)

theorem explicitSigmoidSmoothPair_contDiff : ContDiff ℝ ⊤ explicitSigmoidSmoothPair := by
  have hd : ContDiff ℝ ⊤ (fun z : ℝ × ℝ => z.1 - z.2) :=
    contDiff_fst.sub contDiff_snd
  have hy : ContDiff ℝ ⊤ (fun z : ℝ × ℝ => (1 / 2 : ℝ) * z.2) :=
    contDiff_const.mul contDiff_snd
  exact ((sigmoidSmooth_profiles_contDiff.1.comp hd).add hy).prodMk
    ((sigmoidSmooth_profiles_contDiff.2.comp hd).add hy)

theorem explicitSigmoidSmoothPair_first_monotone :
    Monotone (fun z => (explicitSigmoidSmoothPair z).1) :=
  asymmetricLift_monotone sigmoidSmoothP sigmoidSmoothPFirst
    sigmoidSmoothP_derivative (1 / 2) sigmoidSmoothPFirst_bounds

theorem explicitSigmoidSmoothPair_second_monotone :
    Monotone (fun z => (explicitSigmoidSmoothPair z).2) :=
  asymmetricLift_monotone sigmoidSmoothQ sigmoidSmoothQFirst
    sigmoidSmoothQ_derivative (1 / 2) sigmoidSmoothQFirst_bounds

theorem explicitSigmoidSmoothPair_valid :
    ValidPairActivation Real.sigmoid explicitSigmoidSmoothPair := by
  intro a b
  exact asymmetricLift_difference sigmoidSmoothP sigmoidSmoothQ Real.sigmoid
    (1 / 2) sigmoidSmooth_profile_difference (a, b)

theorem explicitSigmoidSmoothPair_nonnegative :
    NonnegativePairActivation explicitSigmoidSmoothPair := by
  intro a b ha hb
  have hxy : ((0, 0) : ℝ × ℝ) ≤ (a, b) := ⟨ha, hb⟩
  have hp : 0 ≤ (explicitSigmoidSmoothPair (0, 0)).1 := by
    simpa [explicitSigmoidSmoothPair, asymmetricLift] using
      sigmoidSmooth_profiles_zero_nonnegative.1
  have hq : 0 ≤ (explicitSigmoidSmoothPair (0, 0)).2 := by
    simpa [explicitSigmoidSmoothPair, asymmetricLift] using
      sigmoidSmooth_profiles_zero_nonnegative.2
  exact ⟨hp.trans (explicitSigmoidSmoothPair_first_monotone hxy),
    hq.trans (explicitSigmoidSmoothPair_second_monotone hxy)⟩

/-- Closed smooth formula using only exponential and logarithm through the
standard unit-temperature Softplus and sigmoid. -/
theorem explicitSigmoidSmoothPair_closed_form (x y : ℝ) :
    explicitSigmoidSmoothPair (x, y) =
      ((Thesis.Regularization.softplus 1 (x - y) + Real.sigmoid (x - y) + y) / 2,
       (Thesis.Regularization.softplus 1 (x - y) - Real.sigmoid (x - y) + y) / 2) := by
  ext <;> simp only [explicitSigmoidSmoothPair, asymmetricLift, sigmoidSmoothP,
    sigmoidSmoothQ] <;> ring

theorem explicitSigmoidSmoothPair_logsumexp (x y : ℝ) :
    explicitSigmoidSmoothPair (x, y) =
      ((Real.log (Real.exp x + Real.exp y) + Real.sigmoid (x - y)) / 2,
       (Real.log (Real.exp x + Real.exp y) - Real.sigmoid (x - y)) / 2) := by
  have h := explicitSoftplusFirst_logsumexp 1 (by norm_num) x y
  simp only [explicitSoftplusFirst, div_one, one_mul] at h
  rw [explicitSigmoidSmoothPair_closed_form]
  ext <;> dsimp only <;> linarith only [h]

/-- A globally valid, smooth sigmoid pair with convex coordinatewise-monotone
branches and nonnegative-quadrant preservation. -/
theorem sigmoid_smooth_explicit_split :
    ConvexOn ℝ univ (fun z => (explicitSigmoidSmoothPair z).1) ∧
    ConvexOn ℝ univ (fun z => (explicitSigmoidSmoothPair z).2) ∧
    Monotone (fun z => (explicitSigmoidSmoothPair z).1) ∧
    Monotone (fun z => (explicitSigmoidSmoothPair z).2) ∧
    ValidPairActivation Real.sigmoid explicitSigmoidSmoothPair ∧
    NonnegativePairActivation explicitSigmoidSmoothPair :=
  ⟨asymmetricLift_convex sigmoidSmoothP (1 / 2) sigmoidSmoothP_convex,
   asymmetricLift_convex sigmoidSmoothQ (1 / 2) sigmoidSmoothQ_convex,
   explicitSigmoidSmoothPair_first_monotone, explicitSigmoidSmoothPair_second_monotone,
   explicitSigmoidSmoothPair_valid, explicitSigmoidSmoothPair_nonnegative⟩

end HiddenMonotonicity.SmoothDC
