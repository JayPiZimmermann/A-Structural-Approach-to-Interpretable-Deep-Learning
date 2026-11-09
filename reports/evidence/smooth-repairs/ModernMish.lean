import HiddenMonotonicity.ModernActivationBounds
import HiddenMonotonicity.ModernTanh
import HiddenMonotonicity.ModernSoftplus

/-! Genuine Mish, x*tanh(log(1+exp x)), with global integrable curvature.
The proof bounds the two derivatives of its gate by exponential tails. -/
namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

noncomputable def mishGate (x : ℝ) := Real.tanh (Thesis.Regularization.softplus 1 x)
noncomputable def mishGateFirst (x : ℝ) :=
  tanhFirst (Thesis.Regularization.softplus 1 x)*Real.sigmoid x
noncomputable def mishGateSecond (x : ℝ) :=
  mishGateFirst x*(1-Real.sigmoid x-2*mishGate x*Real.sigmoid x)
noncomputable def mish (x : ℝ) := x*mishGate x
noncomputable def mishFirst (x : ℝ) := mishGate x+x*mishGateFirst x
noncomputable def mishSecond (x : ℝ) := 2*mishGateFirst x+x*mishGateSecond x

theorem mish_formula (x : ℝ) : mish x=x*Real.tanh (Real.log (1+Real.exp x)) := by
  simp [mish,mishGate,Thesis.Regularization.softplus]

theorem tanhFirst_one_sub_sq (x : ℝ) : tanhFirst x=1-Real.tanh x^2 := by
  rw [tanh_eq_scaled_sigmoid]
  unfold tanhFirst sigmoidFirst
  ring

theorem mishGate_hasDerivAt (x : ℝ) : HasDerivAt mishGate (mishGateFirst x) x := by
  have h := (tanh_hasDerivAt (Thesis.Regularization.softplus 1 x)).comp x
    (Thesis.Regularization.hasDerivAt_softplus 1 x (by norm_num))
  convert h using 1
  · rfl
  · simp only [mishGateFirst,Thesis.Regularization.gate,div_one]

theorem mishGateFirst_hasDerivAt (x : ℝ) : HasDerivAt mishGateFirst (mishGateSecond x) x := by
  have h := ((tanhFirst_hasDerivAt (Thesis.Regularization.softplus 1 x)).comp x
    (Thesis.Regularization.hasDerivAt_softplus 1 x (by norm_num))).fun_mul (Real.hasDerivAt_sigmoid x)
  convert h using 1
  · rfl
  · rw [tanhSecond_eq,← tanhFirst_one_sub_sq]
    simp only [mishGateSecond,mishGateFirst,mishGate,Thesis.Regularization.gate,div_one,Function.comp_def]
    ring

theorem mishGate_continuous : Continuous mishGate :=
  continuous_iff_continuousAt.mpr fun x => (mishGate_hasDerivAt x).continuousAt

theorem mishGateFirst_continuous : Continuous mishGateFirst :=
  continuous_iff_continuousAt.mpr fun x => (mishGateFirst_hasDerivAt x).continuousAt

theorem mishGateFirst_nonnegative (x : ℝ) : 0≤mishGateFirst x :=
  mul_nonneg (mul_nonneg (by norm_num) (sigmoidFirst_nonnegative _)) (Real.sigmoid_nonneg x)

theorem mishGate_abs_le_one (x : ℝ) : |mishGate x|≤1 := by
  unfold mishGate
  rw [tanh_eq_scaled_sigmoid]
  have h0 := Real.sigmoid_nonneg (2*Thesis.Regularization.softplus 1 x)
  have h1 := Real.sigmoid_le_one (2*Thesis.Regularization.softplus 1 x)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem mishGateFirst_exp_bound (x : ℝ) : mishGateFirst x≤4*Real.exp (-|x|) := by
  let s := Thesis.Regularization.softplus 1 x
  have ht : tanhFirst s≤1 := by rw [tanhFirst_one_sub_sq]; nlinarith [sq_nonneg (Real.tanh s)]
  have ht0 : 0≤tanhFirst s := mul_nonneg (by norm_num) (sigmoidFirst_nonnegative _)
  rcases le_total 0 x with hx | hx
  · have hsp := (Thesis.Regularization.softplus_relu_bounds 1 x (by norm_num)).1
    have hsx : x≤s := (le_max_left _ _).trans hsp
    have hs0 : 0≤s := hx.trans hsx
    have hleft : mishGateFirst x≤tanhFirst s :=
      mul_le_of_le_one_right ht0 (Real.sigmoid_le_one x)
    have hdecay : tanhFirst s≤4*Real.exp (-x) := by
      calc
        tanhFirst s ≤ 4*Real.exp (-|2*s|) :=
          mul_le_mul_of_nonneg_left (sigmoidFirst_exp_bound (2*s)) (by norm_num)
        _ ≤ 4*Real.exp (-x) := by
          rw [abs_of_nonneg (mul_nonneg (by norm_num) hs0)]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.exp_le_exp.mpr (by linarith)
    simpa only [abs_of_nonneg hx] using hleft.trans hdecay
  · have hleft : mishGateFirst x≤Real.sigmoid x :=
      mul_le_of_le_one_left (Real.sigmoid_nonneg x) ht
    calc
      mishGateFirst x ≤ Real.exp x := hleft.trans (sigmoid_le_exp x)
      _ ≤ 4*Real.exp (-|x|) := by
        rw [abs_of_nonpos hx,neg_neg]
        nlinarith [Real.exp_pos x]

theorem mishGateSecond_bound (x : ℝ) : |mishGateSecond x|≤3*mishGateFirst x := by
  have hs0 := Real.sigmoid_nonneg x
  have hs1 := Real.sigmoid_le_one x
  have ht := mishGate_abs_le_one x
  have hm : |mishGate x| *Real.sigmoid x≤1 :=
    (mul_le_mul ht hs1 hs0 (by norm_num)).trans_eq (by ring)
  have hfac : |1-Real.sigmoid x-2*mishGate x*Real.sigmoid x|≤3 := by
    calc
      _ ≤ |1-Real.sigmoid x|+|2*mishGate x*Real.sigmoid x| := by
        simpa only [sub_zero,zero_sub,abs_neg] using
          (abs_sub_le (1-Real.sigmoid x) 0 (2*mishGate x*Real.sigmoid x))
      _ = 1-Real.sigmoid x+2*(|mishGate x| *Real.sigmoid x) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hs1),abs_mul,abs_mul,abs_of_nonneg hs0]
        norm_num
        ring
      _ ≤ 3 := by linarith
  unfold mishGateSecond
  rw [abs_mul,abs_of_nonneg (mishGateFirst_nonnegative x)]
  nlinarith [mul_le_mul_of_nonneg_left hfac (mishGateFirst_nonnegative x)]

theorem mishGateFirst_integrable : Integrable mishGateFirst := by
  apply (exp_neg_abs_integrable.const_mul 4).mono' mishGateFirst_continuous.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mishGateFirst_nonnegative x)]
    exact mishGateFirst_exp_bound x

theorem weighted_mishGateSecond_integrable : Integrable (fun x : ℝ => x*mishGateSecond x) := by
  have hc : Continuous (fun x : ℝ => x*mishGateSecond x) := by
    unfold mishGateSecond
    exact continuous_id.mul (mishGateFirst_continuous.mul
      ((continuous_const.sub continuous_sigmoid).sub
        ((continuous_const.mul mishGate_continuous).mul continuous_sigmoid)))
  apply (abs_mul_exp_neg_abs_integrable.const_mul 12).mono' hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_mul]
  calc
    |x| * |mishGateSecond x| ≤ |x| * (3*mishGateFirst x) :=
      mul_le_mul_of_nonneg_left (mishGateSecond_bound x) (abs_nonneg x)
    _ ≤ |x| * (3*(4*Real.exp (-|x|))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mishGateFirst_exp_bound x) (by norm_num)) (abs_nonneg x)
    _ = 12*(|x| * Real.exp (-|x|)) := by ring

theorem mish_hasDerivAt (x : ℝ) : HasDerivAt mish (mishFirst x) x := by
  have h := (hasDerivAt_id x).fun_mul (mishGate_hasDerivAt x)
  convert h using 1
  · rfl
  · simp only [mishFirst,id_eq]; ring

theorem mishFirst_hasDerivAt (x : ℝ) : HasDerivAt mishFirst (mishSecond x) x := by
  have h := (mishGate_hasDerivAt x).fun_add ((hasDerivAt_id x).fun_mul (mishGateFirst_hasDerivAt x))
  convert h using 1
  · rfl
  · simp only [mishSecond,id_eq]; ring

theorem mish_curvature : curvature mish=mishSecond := by
  funext x
  unfold curvature
  rw [show deriv mish=mishFirst from funext fun y => (mish_hasDerivAt y).deriv]
  exact (mishFirst_hasDerivAt x).deriv

theorem mish_curvature_integrable : Integrable (curvature mish) := by
  rw [mish_curvature]
  exact (mishGateFirst_integrable.const_mul 2).add weighted_mishGateSecond_integrable

theorem mish_derivative_locally_AC (a b : ℝ) :
    AbsolutelyContinuousOnInterval (deriv mish) a b := by
  rw [show deriv mish=mishFirst from funext fun y => (mish_hasDerivAt y).deriv]
  apply locally_AC_of_continuous_derivative _ mishSecond mishFirst_hasDerivAt
  have hc : Continuous mishGateSecond := by
    unfold mishGateSecond
    exact mishGateFirst_continuous.mul ((continuous_const.sub continuous_sigmoid).sub
      ((continuous_const.mul mishGate_continuous).mul continuous_sigmoid))
  exact (continuous_const.mul mishGateFirst_continuous).add (continuous_id.mul hc)

/-- Complete global Mish specialization with proved integrability and regularity. -/
theorem mish_smooth_dc_split :
    Integrable (curvature mish) ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv mish) a b) ∧
    ConvexOn ℝ univ (tilt (C1 mish) (commonTilt mish)) ∧
    ConvexOn ℝ univ (tilt (C2 mish) (commonTilt mish)) ∧
    Monotone (tilt (C1 mish) (commonTilt mish)) ∧
    Monotone (tilt (C2 mish) (commonTilt mish)) ∧
    ValidPairActivation mish (splitPair mish) ∧
    NonnegativePairActivation (splitPair mish) := by
  have hd : Differentiable ℝ mish := fun x => (mish_hasDerivAt x).differentiableAt
  have hs := smooth_dc_split mish hd mish_derivative_locally_AC mish_curvature_integrable
  exact ⟨mish_curvature_integrable,mish_derivative_locally_AC,hs.2.2.1,hs.2.2.2.1,
    hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    smooth_pair_valid mish hd mish_derivative_locally_AC mish_curvature_integrable,
    smooth_pair_nonnegative mish hd mish_derivative_locally_AC mish_curvature_integrable
      (by simp [mish])⟩

end HiddenMonotonicity.SmoothDC
