import HiddenMonotonicity.CurvatureMinimality
import HiddenMonotonicity.ModernTanh
import HiddenMonotonicity.ModernSoftplus
noncomputable section
open Set Filter MeasureTheory HiddenMonotonicity HiddenMonotonicity.SmoothDC
open scoped Topology

-- SMOOTH-smooth_dc_split
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
#check @HiddenMonotonicity.SmoothDC.smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.smooth_dc_split

-- SMOOTH-canonical_tilt_minimality
example : ∀ (f : ℝ → ℝ) (hq : Integrable (curvature f)),
    ∀ L, Monotone (tilt (C1 f) L) → Monotone (tilt (C2 f) L) → commonTilt f≤L := @HiddenMonotonicity.SmoothDC.canonical_tilt_minimality
#check @HiddenMonotonicity.SmoothDC.canonical_tilt_minimality
#print axioms HiddenMonotonicity.SmoothDC.canonical_tilt_minimality

-- SMOOTH-sigmoid_smooth_dc_split
example :     let f := Real.sigmoid
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2) := @HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split
#check @HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split

-- SMOOTH-softplus_smooth_dc_split
example : ∀ (θ : ℝ) (hθ : 0<θ),
    let f := Thesis.Regularization.softplus θ
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧ Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2) := @HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split
#check @HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split

-- SMOOTH-common_affine_of_minimal_curvature
example : ∀ (f c1 c2 : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hfAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f))
    (hc1 : ConvexOn ℝ univ c1) (hd1 : Differentiable ℝ c1)
    (hAC1 : ∀ a b, AbsolutelyContinuousOnInterval (deriv c1) a b)
    (heq : ∀ x, f x=c1 x-c2 x)
    (hminimal : ∀ᵐ x, curvature c1 x=positiveCurvature f x),
    ∃ a b : ℝ, (∀ x, c1 x=C1 f x+a*x+b) ∧ (∀ x, c2 x=C2 f x+a*x+b) := @HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature
#check @HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature
#print axioms HiddenMonotonicity.SmoothDC.common_affine_of_minimal_curvature

-- SMOOTH-curvature_minimality_locally_AC
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
#check @HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC
#print axioms HiddenMonotonicity.SmoothDC.curvature_minimality_locally_AC

-- SMOOTH-tanh_curvature_sech
example : ∀ x : ℝ, curvature Real.tanh x=-2*Real.tanh x/(Real.cosh x)^2 := @HiddenMonotonicity.SmoothDC.tanh_curvature_sech
#check @HiddenMonotonicity.SmoothDC.tanh_curvature_sech
#print axioms HiddenMonotonicity.SmoothDC.tanh_curvature_sech

-- SMOOTH-tanh_curvature_support
example : ∀ x : ℝ, (0≤x → positiveCurvature Real.tanh x=0) ∧
    (x≤0 → negativeCurvature Real.tanh x=0) := @HiddenMonotonicity.SmoothDC.tanh_curvature_support
#check @HiddenMonotonicity.SmoothDC.tanh_curvature_support
#print axioms HiddenMonotonicity.SmoothDC.tanh_curvature_support

-- SMOOTH-tanh_smooth_dc_split
example : Integrable (curvature Real.tanh) ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv Real.tanh) a b) ∧
    ConvexOn ℝ univ (tilt (C1 Real.tanh) (commonTilt Real.tanh)) ∧
    ConvexOn ℝ univ (tilt (C2 Real.tanh) (commonTilt Real.tanh)) ∧
    Monotone (tilt (C1 Real.tanh) (commonTilt Real.tanh)) ∧
    Monotone (tilt (C2 Real.tanh) (commonTilt Real.tanh)) ∧
    ValidPairActivation Real.tanh (splitPair Real.tanh) ∧
    NonnegativePairActivation (splitPair Real.tanh) := @HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split
#check @HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.tanh_smooth_dc_split

-- SMOOTH-softplus_degenerate_split
example : ∀ (θ : ℝ) (hθ : 0<θ),
    negativeCurvature (Thesis.Regularization.softplus θ)=0 ∧
    C2 (Thesis.Regularization.softplus θ)=0 ∧
    C1 (Thesis.Regularization.softplus θ)=Thesis.Regularization.softplus θ ∧
    ConvexOn ℝ univ (Thesis.Regularization.softplus θ) ∧
    NonnegativePairActivation (splitPair (Thesis.Regularization.softplus θ)) := @HiddenMonotonicity.SmoothDC.softplus_degenerate_split
#check @HiddenMonotonicity.SmoothDC.softplus_degenerate_split
#print axioms HiddenMonotonicity.SmoothDC.softplus_degenerate_split
