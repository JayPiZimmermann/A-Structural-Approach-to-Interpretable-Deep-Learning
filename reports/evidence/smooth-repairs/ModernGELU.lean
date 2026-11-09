import HiddenMonotonicity.ModernActivationBounds
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Exact Gaussian GELU on the entire real line. The CDF is the integral of
mathlib's normalized standard Gaussian density, not a sigmoid approximation. -/
namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

noncomputable def standardGaussianDensity : ℝ → ℝ := ProbabilityTheory.gaussianPDFReal 0 1
noncomputable def standardGaussianCDF : ℝ → ℝ := cumulative standardGaussianDensity
noncomputable def gaussianGelu (x : ℝ) := x*standardGaussianCDF x
noncomputable def gaussianGeluFirst (x : ℝ) := standardGaussianCDF x+x*standardGaussianDensity x
noncomputable def gaussianGeluSecond (x : ℝ) := (2-x^2)*standardGaussianDensity x

theorem standardGaussianDensity_formula (x : ℝ) :
    standardGaussianDensity x=(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/2) := by
  simp [standardGaussianDensity,ProbabilityTheory.gaussianPDFReal]

theorem standardGaussianDensity_integrable : Integrable standardGaussianDensity :=
  ProbabilityTheory.integrable_gaussianPDFReal 0 1

theorem standardGaussianDensity_normalized : ∫ x, standardGaussianDensity x=1 :=
  ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by norm_num)

theorem standardGaussianDensity_pos (x : ℝ) : 0<standardGaussianDensity x :=
  ProbabilityTheory.gaussianPDFReal_pos 0 1 x (by norm_num)

theorem standardGaussianDensity_continuous : Continuous standardGaussianDensity := by
  have he : standardGaussianDensity=fun x => (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/2) :=
    funext standardGaussianDensity_formula
  rw [he]
  fun_prop

theorem standardGaussianDensity_hasDerivAt (x : ℝ) :
    HasDerivAt standardGaussianDensity (-x*standardGaussianDensity x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert h using 1
  · funext y; exact standardGaussianDensity_formula y
  · rw [standardGaussianDensity_formula]
    simp only [Pi.neg_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    ring

theorem standardGaussianCDF_hasDerivAt (x : ℝ) :
    HasDerivAt standardGaussianCDF (standardGaussianDensity x) x :=
  cumulative_hasDerivAt_of_continuous standardGaussianDensity standardGaussianDensity_integrable
    standardGaussianDensity_continuous x

theorem gaussianGelu_hasDerivAt (x : ℝ) : HasDerivAt gaussianGelu (gaussianGeluFirst x) x := by
  have h := (hasDerivAt_id x).fun_mul (standardGaussianCDF_hasDerivAt x)
  convert h using 1
  · rfl
  · simp only [gaussianGeluFirst,id_eq]; ring

theorem gaussianGeluFirst_hasDerivAt (x : ℝ) :
    HasDerivAt gaussianGeluFirst (gaussianGeluSecond x) x := by
  have h := (standardGaussianCDF_hasDerivAt x).fun_add
    ((hasDerivAt_id x).fun_mul (standardGaussianDensity_hasDerivAt x))
  convert h using 1
  · rfl
  · simp only [gaussianGeluSecond,id_eq]; ring

theorem gaussianGelu_curvature : curvature gaussianGelu=gaussianGeluSecond := by
  funext x
  unfold curvature
  rw [show deriv gaussianGelu=gaussianGeluFirst from funext fun y => (gaussianGelu_hasDerivAt y).deriv]
  exact (gaussianGeluFirst_hasDerivAt x).deriv

theorem gaussianGelu_curvature_integrable : Integrable (curvature gaussianGelu) := by
  have hi : Integrable (fun x : ℝ => x^2*Real.exp (-(1/2 : ℝ)*x^2)) := by
    simpa only [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq (b:=(1/2 : ℝ)) (s:=2) (by norm_num) (by norm_num))
  have hw : Integrable (fun x : ℝ => x^2*standardGaussianDensity x) := by
    convert hi.const_mul ((Real.sqrt (2*Real.pi))⁻¹) using 1
    funext x
    rw [standardGaussianDensity_formula]
    rw [show -x^2/2=-(1/2 : ℝ)*x^2 by ring]
    ring
  rw [gaussianGelu_curvature]
  convert (standardGaussianDensity_integrable.const_mul 2).sub hw using 1
  funext x
  change (2-x^2)*standardGaussianDensity x=2*standardGaussianDensity x-x^2*standardGaussianDensity x
  ring

theorem gaussianGelu_derivative_locally_AC (a b : ℝ) :
    AbsolutelyContinuousOnInterval (deriv gaussianGelu) a b := by
  rw [show deriv gaussianGelu=gaussianGeluFirst from funext fun x => (gaussianGelu_hasDerivAt x).deriv]
  apply locally_AC_of_continuous_derivative _ gaussianGeluSecond gaussianGeluFirst_hasDerivAt
  exact (continuous_const.sub (continuous_id.pow 2)).mul standardGaussianDensity_continuous

theorem gaussianGelu_curvature_sign (x : ℝ) :
    (0<curvature gaussianGelu x ↔ x^2<2) ∧
    (curvature gaussianGelu x<0 ↔ 2<x^2) ∧
    (curvature gaussianGelu x=0 ↔ x^2=2) := by
  rw [gaussianGelu_curvature]
  have hp := standardGaussianDensity_pos x
  unfold gaussianGeluSecond
  constructor
  · rw [mul_pos_iff_of_pos_right hp,sub_pos]
  constructor
  · simp only [mul_neg_iff,hp,not_lt.mpr hp.le,and_true,and_false,false_or,or_false,sub_neg]
  · rw [mul_eq_zero]
    simp only [ne_of_gt hp,or_false]
    rw [sub_eq_zero,eq_comm]

/-- The displayed source sign regions, with their exact square-root boundary. -/
theorem gaussianGelu_curvature_interval (x : ℝ) :
    (0<curvature gaussianGelu x ↔ |x|<Real.sqrt 2) ∧
    (curvature gaussianGelu x<0 ↔ Real.sqrt 2< |x|) := by
  constructor
  · rw [(gaussianGelu_curvature_sign x).1]
    simpa only [sq_abs,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)] using
      (sq_lt_sq₀ (abs_nonneg x) (Real.sqrt_nonneg (2 : ℝ)))
  · rw [(gaussianGelu_curvature_sign x).2.1]
    simpa only [sq_abs,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)] using
      (sq_lt_sq₀ (Real.sqrt_nonneg (2 : ℝ)) (abs_nonneg x))

/-- Full exact-Gaussian specialization, with global signed-domain scope. -/
theorem gaussianGelu_smooth_dc_split :
    Integrable (curvature gaussianGelu) ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv gaussianGelu) a b) ∧
    ConvexOn ℝ univ (tilt (C1 gaussianGelu) (commonTilt gaussianGelu)) ∧
    ConvexOn ℝ univ (tilt (C2 gaussianGelu) (commonTilt gaussianGelu)) ∧
    Monotone (tilt (C1 gaussianGelu) (commonTilt gaussianGelu)) ∧
    Monotone (tilt (C2 gaussianGelu) (commonTilt gaussianGelu)) ∧
    ValidPairActivation gaussianGelu (splitPair gaussianGelu) ∧
    NonnegativePairActivation (splitPair gaussianGelu) := by
  have hd : Differentiable ℝ gaussianGelu := fun x => (gaussianGelu_hasDerivAt x).differentiableAt
  have hs := smooth_dc_split gaussianGelu hd gaussianGelu_derivative_locally_AC gaussianGelu_curvature_integrable
  exact ⟨gaussianGelu_curvature_integrable,gaussianGelu_derivative_locally_AC,hs.2.2.1,hs.2.2.2.1,
    hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    smooth_pair_valid gaussianGelu hd gaussianGelu_derivative_locally_AC gaussianGelu_curvature_integrable,
    smooth_pair_nonnegative gaussianGelu hd gaussianGelu_derivative_locally_AC gaussianGelu_curvature_integrable
      (by simp [gaussianGelu])⟩

end HiddenMonotonicity.SmoothDC
