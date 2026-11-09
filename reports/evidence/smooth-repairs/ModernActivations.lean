import HiddenMonotonicity.ModernGELU
import HiddenMonotonicity.ModernSwish
import HiddenMonotonicity.ModernMish

/-! Complete source-facing six-case modern-activation corollary. The activation
data contain only the choice of formula and positive temperature/scale parameters. -/
namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

inductive ModernActivation where
  | gaussianGelu
  | swish (β : ℝ) (positive : 0<β)
  | mish
  | tanh
  | sigmoid
  | softplus (θ : ℝ) (positive : 0<θ)

noncomputable def ModernActivation.eval : ModernActivation → ℝ → ℝ
  | .gaussianGelu => HiddenMonotonicity.SmoothDC.gaussianGelu
  | .swish β _ => HiddenMonotonicity.SmoothDC.swish β
  | .mish => HiddenMonotonicity.SmoothDC.mish
  | .tanh => Real.tanh
  | .sigmoid => Real.sigmoid
  | .softplus θ _ => Thesis.Regularization.softplus θ

/-- All analytic hypotheses are established for each actual formula, rather
than assumed in the activation datatype. -/
theorem modern_activation_regularity (a : ModernActivation) :
    Differentiable ℝ a.eval ∧
    (∀ l r, AbsolutelyContinuousOnInterval (deriv a.eval) l r) ∧
    Integrable (curvature a.eval) ∧ 0≤a.eval 0 := by
  cases a with
  | gaussianGelu =>
      exact ⟨fun x => (gaussianGelu_hasDerivAt x).differentiableAt,
        gaussianGelu_derivative_locally_AC,gaussianGelu_curvature_integrable,by simp [ModernActivation.eval,gaussianGelu]⟩
  | swish β hβ =>
      exact ⟨fun x => (swish_hasDerivAt β x).differentiableAt,
        swish_derivative_locally_AC β,swish_curvature_integrable β hβ,by simp [ModernActivation.eval,swish]⟩
  | mish =>
      exact ⟨fun x => (mish_hasDerivAt x).differentiableAt,
        mish_derivative_locally_AC,mish_curvature_integrable,by simp [ModernActivation.eval,mish]⟩
  | tanh =>
      exact ⟨fun x => (tanh_hasDerivAt x).differentiableAt,
        tanh_derivative_locally_AC,tanh_curvature_integrable,by simp [ModernActivation.eval]⟩
  | sigmoid =>
      refine ⟨fun x => (Real.hasDerivAt_sigmoid x).differentiableAt,sigmoid_derivative_locally_AC,?_,Real.sigmoid_nonneg 0⟩
      change Integrable (curvature Real.sigmoid)
      rw [sigmoid_curvature]
      exact sigmoidSecond_integrable
  | softplus θ hθ =>
      exact ⟨fun x => (Thesis.Regularization.hasDerivAt_softplus θ x hθ).differentiableAt,
        softplus_derivative_locally_AC θ hθ,softplus_curvature_integrable θ hθ,softplus_zero_nonnegative θ hθ⟩

/-- Every case satisfies the whole smooth theorem, including its hypotheses,
negative-infinity slope, bounded derivative, exact identity and nonnegative pair. -/
theorem modern_activation_split (a : ModernActivation) :
    let f := a.eval
    Differentiable ℝ f ∧
    (∀ l r, AbsolutelyContinuousOnInterval (deriv f) l r) ∧
    Integrable (curvature f) ∧ 0≤f 0 ∧
    Tendsto (deriv f) atBot (𝓝 (minusInfinitySlope f)) ∧
    (∃ B : ℝ, ∀ x, |deriv f x|≤B) ∧
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
    (∀ z : ℝ × ℝ, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2)) ∧
    NonnegativePairActivation (splitPair f) := by
  obtain ⟨hd,hAC,hi,h0⟩ := modern_activation_regularity a
  have hs := smooth_dc_split a.eval hd hAC hi
  exact ⟨hd,hAC,hi,h0,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,
    hs.2.2.2.2.2.1,hs.2.2.2.2.2.2,smooth_pair_nonnegative _ hd hAC hi h0⟩

/-- cor:modern_activations, with all six global analytic cases and all displayed
curvature, sign, softplus-degeneration and nonnegative-initial-value clauses. -/
theorem modern_activations :
    (∀ a : ModernActivation,
      let f := a.eval
      Differentiable ℝ f ∧
      (∀ l r, AbsolutelyContinuousOnInterval (deriv f) l r) ∧
      Integrable (curvature f) ∧ 0≤f 0 ∧
      Tendsto (deriv f) atBot (𝓝 (minusInfinitySlope f)) ∧
      (∃ B : ℝ, ∀ x, |deriv f x|≤B) ∧
      ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
      ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
      Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
      (∀ z : ℝ × ℝ, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2)) ∧
      NonnegativePairActivation (splitPair f)) ∧
    (∀ x, curvature gaussianGelu x=(2-x^2)*standardGaussianDensity x ∧
      (0<curvature gaussianGelu x ↔ |x|<Real.sqrt 2) ∧
      (curvature gaussianGelu x<0 ↔ Real.sqrt 2< |x|)) ∧
    (∀ β : ℝ, 0<β →
      (∀ x, curvature (swish β) x=β*sigmoidFirst (β*x)*(2+β*x*(1-2*Real.sigmoid (β*x)))) ∧
      ∃ ε R : ℝ, 0<ε ∧ 0<R ∧ (∀ x, |x|<ε → 0<curvature (swish β) x) ∧
        (∀ x, R< |x| → curvature (swish β) x<0)) ∧
    (∀ x, mish x=x*Real.tanh (Real.log (1+Real.exp x))) ∧
    (∀ x, curvature Real.tanh x=-2*Real.tanh x/(Real.cosh x)^2 ∧
      (0≤x → positiveCurvature Real.tanh x=0) ∧ (x≤0 → negativeCurvature Real.tanh x=0)) ∧
    (∀ x, curvature Real.sigmoid x=sigmoidFirst x*(1-2*Real.sigmoid x)) ∧
    (∀ θ : ℝ, 0<θ →
      (∀ x, curvature (Thesis.Regularization.softplus θ) x=sigmoidFirst (x/θ)/θ) ∧
      negativeCurvature (Thesis.Regularization.softplus θ)=0 ∧
      C2 (Thesis.Regularization.softplus θ)=0 ∧
      C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ) := by
  refine ⟨modern_activation_split,?_,?_,mish_formula,?_,?_,?_⟩
  · intro x
    exact ⟨congrFun gaussianGelu_curvature x,gaussianGelu_curvature_interval x⟩
  · intro β hβ
    exact ⟨fun x => congrFun (swish_curvature β) x,swish_curvature_sign_regions β hβ⟩
  · intro x
    exact ⟨tanh_curvature_sech x,tanh_curvature_support x⟩
  · intro x
    exact congrFun sigmoid_curvature x
  · intro θ hθ
    exact ⟨fun x => congrFun (softplus_curvature θ hθ) x,
      softplus_negativeCurvature_zero θ hθ,softplus_C2_zero θ hθ,softplus_C1_eq θ hθ⟩

end HiddenMonotonicity.SmoothDC
