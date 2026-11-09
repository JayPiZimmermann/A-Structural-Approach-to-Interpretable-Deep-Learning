import HiddenMonotonicity.ModernActivations

/-! Source-facing six-case activation corollary, including explicit original
softplus convexity and nonnegative curvature alongside the full analytic cases. -/
namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

/-- Complete cor:modern_activations, with every displayed specialization clause. -/
theorem modern_activations_complete :
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
      (∀ x, curvature (Thesis.Regularization.softplus θ) x=sigmoidFirst (x/θ)/θ ∧
        0≤curvature (Thesis.Regularization.softplus θ) x) ∧
      negativeCurvature (Thesis.Regularization.softplus θ)=0 ∧
      C2 (Thesis.Regularization.softplus θ)=0 ∧
      C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ ∧
      ConvexOn ℝ univ (Thesis.Regularization.softplus θ)) := by
  obtain ⟨ha,hg,hw,hm,ht,hs,hsp⟩ := modern_activations
  refine ⟨ha,hg,hw,hm,ht,hs,?_⟩
  intro θ hθ
  obtain ⟨hformula,hN,h2,h1⟩ := hsp θ hθ
  exact ⟨fun x => ⟨hformula x,softplus_curvature_nonnegative θ hθ x⟩,
    hN,h2,h1,(softplus_degenerate_split θ hθ).2.2.2.1⟩

end HiddenMonotonicity.SmoothDC
