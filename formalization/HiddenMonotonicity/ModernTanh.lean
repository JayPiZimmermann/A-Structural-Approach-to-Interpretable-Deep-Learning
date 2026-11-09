import HiddenMonotonicity.ModernSigmoid
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The genuine global hyperbolic-tangent case, including L1 curvature and
its curvature signs. No nonnegative-activation restriction is imposed. -/
namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

/-- The exact bridge to the library hyperbolic tangent. -/
theorem tanh_eq_scaled_sigmoid (x : ℝ) : Real.tanh x=2*Real.sigmoid (2*x)-1 := by
  have he : Real.exp x*Real.exp (-x)=1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hd1 : Real.exp x+Real.exp (-x)≠0 := ne_of_gt (by positivity)
  have hd2 : 1+Real.exp (-x)*Real.exp (-x)≠0 := ne_of_gt (by positivity)
  rw [Real.tanh_eq,Real.sigmoid_def,
    show -(2*x)=(-x)+(-x) by ring,Real.exp_add]
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*Real.exp (-x)) he]

noncomputable def tanhFirst (x : ℝ) := 4*sigmoidFirst (2*x)
noncomputable def tanhSecond (x : ℝ) := 8*sigmoidSecond (2*x)

theorem tanh_hasDerivAt (x : ℝ) : HasDerivAt Real.tanh (tanhFirst x) x := by
  have h := (((Real.hasDerivAt_sigmoid (2*x)).comp x
    ((hasDerivAt_id x).const_mul 2)).const_mul 2).sub_const 1
  have he : (fun y : ℝ => 2*Real.sigmoid (2*y)-1)=Real.tanh :=
    funext fun y => (tanh_eq_scaled_sigmoid y).symm
  convert h using 1
  · exact he.symm
  · simp only [tanhFirst,sigmoidFirst]; ring

theorem tanhFirst_hasDerivAt (x : ℝ) : HasDerivAt tanhFirst (tanhSecond x) x := by
  have h := ((sigmoidFirst_derivative (2*x)).comp x ((hasDerivAt_id x).const_mul 2)).const_mul 4
  convert h using 1
  · funext y; rfl
  · unfold tanhSecond; ring

theorem tanh_curvature : curvature Real.tanh=tanhSecond := by
  funext x
  unfold curvature
  rw [show deriv Real.tanh=tanhFirst from funext fun y => (tanh_hasDerivAt y).deriv]
  exact (tanhFirst_hasDerivAt x).deriv

theorem tanh_curvature_integrable : Integrable (curvature Real.tanh) := by
  rw [tanh_curvature]
  exact (sigmoidSecond_integrable.comp_mul_left' (by norm_num : (2 : ℝ)≠0)).const_mul 8

theorem tanh_derivative_locally_AC (a b : ℝ) :
    AbsolutelyContinuousOnInterval (deriv Real.tanh) a b := by
  rw [show deriv Real.tanh=tanhFirst from funext fun y => (tanh_hasDerivAt y).deriv]
  have hs : ContDiff ℝ 1 (fun x : ℝ => Real.sigmoid (2*x)) :=
    (contDiff_sigmoid.of_le (by simp)).comp (by fun_prop)
  have hc : ContDiff ℝ 1 tanhFirst :=
    contDiff_const.mul (hs.mul (contDiff_const.sub hs))
  exact hc.contDiffOn.absolutelyContinuousOnInterval

theorem tanhSecond_eq (x : ℝ) :
    tanhSecond x=-2*Real.tanh x*(1-Real.tanh x^2) := by
  rw [tanh_eq_scaled_sigmoid]
  unfold tanhSecond sigmoidSecond sigmoidFirst
  ring

theorem tanh_curvature_sech (x : ℝ) :
    curvature Real.tanh x=-2*Real.tanh x/(Real.cosh x)^2 := by
  have hc : Real.cosh x≠0 := ne_of_gt (Real.cosh_pos x)
  have he : 1-Real.tanh x^2=1/(Real.cosh x)^2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [tanh_curvature,tanhSecond_eq,he]
  ring

/-- The positive part vanishes on the positive half-line and the negative part
vanishes on the negative half-line, including the zero-curvature boundary. -/
theorem tanh_curvature_support (x : ℝ) :
    (0≤x → positiveCurvature Real.tanh x=0) ∧
    (x≤0 → negativeCurvature Real.tanh x=0) := by
  have hsign : (0≤x → 0≤Real.tanh x) ∧ (x≤0 → Real.tanh x≤0) := by
    rw [tanh_eq_scaled_sigmoid]
    constructor
    · intro hx
      have hs := Real.sigmoid_monotone (show (0 : ℝ)≤2*x by linarith)
      rw [Real.sigmoid_zero] at hs
      norm_num at hs
      linarith
    · intro hx
      have hs := Real.sigmoid_monotone (show 2*x≤(0 : ℝ) by linarith)
      rw [Real.sigmoid_zero] at hs
      norm_num at hs
      linarith
  constructor
  · intro hx
    apply max_eq_right
    rw [tanh_curvature_sech]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hsign.1 hx))
      (sq_nonneg _)
  · intro hx
    apply max_eq_right
    apply neg_nonpos.mpr
    rw [tanh_curvature_sech]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (hsign.2 hx)) (sq_nonneg _)

/-- Complete global tanh specialization, including the nonnegative split-pair
conclusion justified by tanh(0)=0. -/
theorem tanh_smooth_dc_split :
    Integrable (curvature Real.tanh) ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv Real.tanh) a b) ∧
    ConvexOn ℝ univ (tilt (C1 Real.tanh) (commonTilt Real.tanh)) ∧
    ConvexOn ℝ univ (tilt (C2 Real.tanh) (commonTilt Real.tanh)) ∧
    Monotone (tilt (C1 Real.tanh) (commonTilt Real.tanh)) ∧
    Monotone (tilt (C2 Real.tanh) (commonTilt Real.tanh)) ∧
    ValidPairActivation Real.tanh (splitPair Real.tanh) ∧
    NonnegativePairActivation (splitPair Real.tanh) := by
  have hd : Differentiable ℝ Real.tanh := fun x => (tanh_hasDerivAt x).differentiableAt
  have hs := smooth_dc_split Real.tanh hd tanh_derivative_locally_AC tanh_curvature_integrable
  exact ⟨tanh_curvature_integrable,tanh_derivative_locally_AC,hs.2.2.1,hs.2.2.2.1,
    hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    smooth_pair_valid Real.tanh hd tanh_derivative_locally_AC tanh_curvature_integrable,
    smooth_pair_nonnegative Real.tanh hd tanh_derivative_locally_AC tanh_curvature_integrable
      (by simp)⟩

end HiddenMonotonicity.SmoothDC
