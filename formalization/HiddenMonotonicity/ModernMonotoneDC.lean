import HiddenMonotonicity.CurvatureMonotoneDCLift
import HiddenMonotonicity.ConvexMonotoneReadout
import HiddenMonotonicity.ModernActivations

/-! The absolute-curvature construction instantiated at the actual modern
activation formulas, and composed through the same finite network parameters.
Analytic hypotheses are proved for each formula in `ModernActivations`; they
are not extra assumptions on the activation data. -/

noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity.SmoothDC
open Set

/-- All six actual activation formulas have a globally convex and monotone
asymmetric lift. Nonnegative output values are asserted on the input quadrant. -/
theorem modern_curvature_pair (a : ModernActivation) :
    ConvexPairActivation (curvatureLiftPair a.eval) ∧
    Monotone (curvatureLiftPair a.eval) ∧
    ValidPairActivation a.eval (curvatureLiftPair a.eval) ∧
    NonnegativePairActivation (curvatureLiftPair a.eval) := by
  obtain ⟨hd, hAC, hi, h0⟩ := modern_activation_regularity a
  obtain ⟨hc₁, hc₂, hm₁, hm₂, hv⟩ :=
    curvature_monotone_dc_split a.eval hd hAC hi
  refine ⟨⟨hc₁, hc₂⟩, ?_, hv, curvatureLiftPair_nonnegative a.eval hd hAC hi h0⟩
  intro x y hxy
  exact ⟨hm₁ hxy, hm₂ hxy⟩

/-- Entire networks using GELU, positive-scale Swish, Mish, tanh, sigmoid, or
positive-temperature Softplus admit this same-parameter decomposition. The
split weights are nonnegative, while affine biases may be arbitrary. -/
theorem modern_curvature_network {n m : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (a : ModernActivation) :
    Monotone (net.decomposeWith (curvatureLiftPair a.eval)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n =>
      (net.decomposeWith (curvatureLiftPair a.eval) x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n =>
      (net.decomposeWith (curvatureLiftPair a.eval) x).2 i)) ∧
    ∀ x : PairVec n,
      (net.decomposeWith (curvatureLiftPair a.eval) x).1 -
        (net.decomposeWith (curvatureLiftPair a.eval) x).2 =
      net.forwardWith a.eval (x.1 - x.2) := by
  obtain ⟨hc, hm, hv, _⟩ := modern_curvature_pair a
  exact net.convex_monotone_decomposition hw a.eval (curvatureLiftPair a.eval) hv hm hc

/-- Nonnegative stream values additionally require nonnegative split biases
and input streams; these hypotheses are unnecessary for convexity or recovery. -/
theorem modern_curvature_network_nonnegative {n m : ℕ} (net : Network n m)
    (hp : net.NonnegativeParameters) (a : ModernActivation)
    (x : PairVec n) (hx : 0 ≤ x.1 ∧ 0 ≤ x.2) :
    0 ≤ (net.decomposeWith (curvatureLiftPair a.eval) x).1 ∧
    0 ≤ (net.decomposeWith (curvatureLiftPair a.eval) x).2 := by
  exact net.decomposition_nonnegative hp (curvatureLiftPair a.eval)
    (modern_curvature_pair a).2.2.2 x hx

/-- The modern-activation corollary includes a genuine signed affine output
layer. The readout is not passed through an additional activation. -/
theorem modern_curvature_affine_network {n m k : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (a : ModernActivation)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) (bp bn : Vec k) :
    Monotone (net.affineDecomposeWith (curvatureLiftPair a.eval) wp wn bp bn) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n =>
      (net.affineDecomposeWith (curvatureLiftPair a.eval) wp wn bp bn x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n =>
      (net.affineDecomposeWith (curvatureLiftPair a.eval) wp wn bp bn x).2 i)) ∧
    ∀ x : PairVec n,
      (net.affineDecomposeWith (curvatureLiftPair a.eval) wp wn bp bn x).1 -
        (net.affineDecomposeWith (curvatureLiftPair a.eval) wp wn bp bn x).2 =
      affineLayer wp wn bp bn (net.forwardWith a.eval (x.1 - x.2)) := by
  obtain ⟨hc, hm, hv, _⟩ := modern_curvature_pair a
  exact net.affine_convex_monotone_decomposition hw a.eval (curvatureLiftPair a.eval)
    hv hm hc wp wn hwp hwn bp bn

end HiddenMonotonicity.SmoothDC
