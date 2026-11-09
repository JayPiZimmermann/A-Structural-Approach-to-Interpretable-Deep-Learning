import HiddenMonotonicity.CurvatureMinimality
import HiddenMonotonicity.DistributionalRegularity
import HiddenMonotonicity.ModernActivationCorollary
import HiddenMonotonicity.ModernActivations
import HiddenMonotonicity.ModernGELU
import HiddenMonotonicity.ModernMish
import HiddenMonotonicity.ModernSigmoid
import HiddenMonotonicity.ModernSoftplus
import HiddenMonotonicity.ModernSwish
import HiddenMonotonicity.ModernTanh
import HiddenMonotonicity.SmoothCurvatureSplit
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology ContDiff

example : ∀ (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)),
    Tendsto (deriv f) atBot (𝓝 (minusInfinitySlope f)) ∧
    (∃ B : ℝ, ∀ x, |deriv f x| ≤ B) ∧
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧
    Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z : ℝ × ℝ, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2) := @HiddenMonotonicity.SmoothDC.smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.smooth_dc_split

example : ∀ (f : ℝ → ℝ) (hq : Integrable (curvature f)),
    ∀ L, Monotone (tilt (C1 f) L) → Monotone (tilt (C2 f) L) → commonTilt f≤L := @HiddenMonotonicity.SmoothDC.canonical_tilt_minimality
#print axioms HiddenMonotonicity.SmoothDC.canonical_tilt_minimality

example :     let f := Real.sigmoid
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2) := @HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split

example : ∀ (θ : ℝ) (hθ : 0<θ),
    let f := Thesis.Regularization.softplus θ
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2) := @HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split

example : ∀ (f c1 c2 : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hfAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f))
    (hc1 : ConvexOn ℝ univ c1) (hd1 : Differentiable ℝ c1)
    (hAC1 : ∀ a b, AbsolutelyContinuousOnInterval (deriv c1) a b)
    (heq : ∀ x, f x=c1 x-c2 x)
    (hminimal : ∀ᵐ x, curvature c1 x=positiveCurvature f x),
    ∃ a b : ℝ, (∀ x, c1 x=C1 f x+a*x+b) ∧ (∀ x, c2 x=C2 f x+a*x+b) := @HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature
#print axioms HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature

example : ∀ (f c1 c2 : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hfAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f))
    (hc1 : ConvexOn ℝ univ c1) (hc2 : ConvexOn ℝ univ c2)
    (hd1 : Differentiable ℝ c1) (hd2 : Differentiable ℝ c2)
    (hAC1 : ∀ a b, AbsolutelyContinuousOnInterval (deriv c1) a b)
    (heq : ∀ x, f x=c1 x-c2 x),
    (∀ᵐ x, positiveCurvature f x≤curvature c1 x ∧ negativeCurvature f x≤curvature c2 x) ∧
    ((∀ᵐ x, curvature c1 x=positiveCurvature f x ∧ curvature c2 x=negativeCurvature f x) →
      ∃ a b : ℝ, (∀ x, c1 x=C1 f x+a*x+b) ∧ (∀ x, c2 x=C2 f x+a*x+b)) ∧
    (∀ L, Monotone (tilt (C1 f) L) → Monotone (tilt (C2 f) L) → commonTilt f≤L) := @HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC
#print axioms HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC

example : ∀ x : ℝ, curvature Real.tanh x=-2*Real.tanh x/(Real.cosh x)^2 := @HiddenMonotonicity.SmoothDC.tanh_curvature_sech
#print axioms HiddenMonotonicity.SmoothDC.tanh_curvature_sech

example : ∀ x : ℝ, (0≤x → positiveCurvature Real.tanh x=0) ∧
    (x≤0 → negativeCurvature Real.tanh x=0) := @HiddenMonotonicity.SmoothDC.tanh_curvature_support
#print axioms HiddenMonotonicity.SmoothDC.tanh_curvature_support

example : Integrable (curvature Real.tanh) ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv Real.tanh) a b) ∧
    ConvexOn ℝ univ (tilt (C1 Real.tanh) (commonTilt Real.tanh)) ∧
    ConvexOn ℝ univ (tilt (C2 Real.tanh) (commonTilt Real.tanh)) ∧
    Monotone (tilt (C1 Real.tanh) (commonTilt Real.tanh)) ∧
    Monotone (tilt (C2 Real.tanh) (commonTilt Real.tanh)) ∧
    ValidPairActivation Real.tanh (splitPair Real.tanh) ∧
    NonnegativePairActivation (splitPair Real.tanh) := @HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split

example : ∀ (θ : ℝ) (hθ : 0<θ),
    negativeCurvature (Thesis.Regularization.softplus θ)=0 ∧
    C2 (Thesis.Regularization.softplus θ)=0 ∧
    C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ ∧
    ConvexOn ℝ univ (Thesis.Regularization.softplus θ) ∧
    NonnegativePairActivation (splitPair (Thesis.Regularization.softplus θ)) := @HiddenMonotonicity.SmoothDC.softplus_degenerate_split
#print axioms HiddenMonotonicity.SmoothDC.softplus_degenerate_split

example : (∀ a : ModernActivation,
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
  C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ) := @HiddenMonotonicity.SmoothDC.modern_activations
#print axioms HiddenMonotonicity.SmoothDC.modern_activations

example : Integrable (curvature gaussianGelu) ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv gaussianGelu) a b) ∧
ConvexOn ℝ univ (tilt (C1 gaussianGelu) (commonTilt gaussianGelu)) ∧
ConvexOn ℝ univ (tilt (C2 gaussianGelu) (commonTilt gaussianGelu)) ∧
Monotone (tilt (C1 gaussianGelu) (commonTilt gaussianGelu)) ∧
Monotone (tilt (C2 gaussianGelu) (commonTilt gaussianGelu)) ∧
ValidPairActivation gaussianGelu (splitPair gaussianGelu) ∧
NonnegativePairActivation (splitPair gaussianGelu) := @HiddenMonotonicity.SmoothDC.gaussianGelu_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.gaussianGelu_smooth_dc_split

example : Integrable (curvature mish) ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv mish) a b) ∧
ConvexOn ℝ univ (tilt (C1 mish) (commonTilt mish)) ∧
ConvexOn ℝ univ (tilt (C2 mish) (commonTilt mish)) ∧
Monotone (tilt (C1 mish) (commonTilt mish)) ∧
Monotone (tilt (C2 mish) (commonTilt mish)) ∧
ValidPairActivation mish (splitPair mish) ∧
NonnegativePairActivation (splitPair mish) := @HiddenMonotonicity.SmoothDC.mish_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.mish_smooth_dc_split

example : ∀ (β : ℝ) (hβ : 0<β),
Integrable (curvature (swish β)) ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv (swish β)) a b) ∧
ConvexOn ℝ univ (tilt (C1 (swish β)) (commonTilt (swish β))) ∧
ConvexOn ℝ univ (tilt (C2 (swish β)) (commonTilt (swish β))) ∧
Monotone (tilt (C1 (swish β)) (commonTilt (swish β))) ∧
Monotone (tilt (C2 (swish β)) (commonTilt (swish β))) ∧
ValidPairActivation (swish β) (splitPair (swish β)) ∧
NonnegativePairActivation (splitPair (swish β)) := @HiddenMonotonicity.SmoothDC.swish_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.swish_smooth_dc_split

example : ∀ (f q : ℝ → ℝ)
(hf : Continuous f) (hw : HasSecondDistributionalDerivative f q),
Differentiable ℝ f ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b) ∧
(∀ᵐ x, curvature f x=q x) ∧
∃ a b : ℝ, ∀ x, f x=localPrimitive (localPrimitive q) x+a*x+b := @HiddenMonotonicity.SmoothDC.distributional_second_derivative_regular
#print axioms HiddenMonotonicity.SmoothDC.distributional_second_derivative_regular

example : ∀ (f c1 c2 q1 q2 : ℝ → ℝ)
(hf : Differentiable ℝ f)
(hfAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
(hq : Integrable (curvature f))
(hc1 : ConvexOn ℝ univ c1) (hc2 : ConvexOn ℝ univ c2)
(hw1 : HasSecondDistributionalDerivative c1 q1)
(hw2 : HasSecondDistributionalDerivative c2 q2)
(heq : ∀ x, f x=c1 x-c2 x),
Differentiable ℝ c1 ∧ Differentiable ℝ c2 ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv c1) a b) ∧
(∀ a b, AbsolutelyContinuousOnInterval (deriv c2) a b) ∧
(∀ᵐ x, curvature c1 x=q1 x ∧ curvature c2 x=q2 x) ∧
(∀ᵐ x, positiveCurvature f x≤q1 x ∧ negativeCurvature f x≤q2 x) ∧
((∀ᵐ x, q1 x=positiveCurvature f x ∧ q2 x=negativeCurvature f x) →
  ∃ a b : ℝ, (∀ x, c1 x=C1 f x+a*x+b) ∧ (∀ x, c2 x=C2 f x+a*x+b)) ∧
(∀ L, Monotone (tilt (C1 f) L) → Monotone (tilt (C2 f) L) → commonTilt f≤L) := @HiddenMonotonicity.SmoothDC.curvature_minimality_distributional
#print axioms HiddenMonotonicity.SmoothDC.curvature_minimality_distributional

example : (∀ a : ModernActivation,
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
  (∀ x, curvature (Thesis.Regularization.softplus θ) x=sigmoidFirst (x/θ)/θ ∧
    0≤curvature (Thesis.Regularization.softplus θ) x) ∧
  negativeCurvature (Thesis.Regularization.softplus θ)=0 ∧
  C2 (Thesis.Regularization.softplus θ)=0 ∧
  C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ ∧
  ConvexOn ℝ univ (Thesis.Regularization.softplus θ)) := @HiddenMonotonicity.SmoothDC.modern_activations_complete
#print axioms HiddenMonotonicity.SmoothDC.modern_activations_complete
