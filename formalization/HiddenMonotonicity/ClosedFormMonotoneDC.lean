import HiddenMonotonicity.ExplicitGELU
import HiddenMonotonicity.ExplicitSwish
import HiddenMonotonicity.ExplicitSigmoidSmooth
import HiddenMonotonicity.ConvexMonotoneReadout

/-! The displayed root-free activation formulas, including max/identity for
ReLU, instantiate the generic finite-network theorem directly. These explicit
profiles need not coincide with the canonical absolute-curvature profiles. -/

noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity.SmoothDC
open Set

inductive ClosedFormActivation where
  | relu
  | gaussianGelu
  | swish (β : ℝ) (positive : 0 < β)
  | sigmoid
  | softplus (θ : ℝ) (positive : 0 < θ)

def ClosedFormActivation.eval : ClosedFormActivation → ℝ → ℝ
  | .relu => HiddenMonotonicity.relu
  | .gaussianGelu => HiddenMonotonicity.SmoothDC.gaussianGelu
  | .swish β _ => HiddenMonotonicity.SmoothDC.swish β
  | .sigmoid => Real.sigmoid
  | .softplus θ _ => Thesis.Regularization.softplus θ

def ClosedFormActivation.pair : ClosedFormActivation → (ℝ × ℝ) → ℝ × ℝ
  | .relu => fun z => (asymmetricLift HiddenMonotonicity.relu 1 z,
      asymmetricLift (fun _ => 0) 1 z)
  | .gaussianGelu => explicitGaussianGeluPair
  | .swish β _ => explicitSwishPair β
  | .sigmoid => explicitSigmoidSmoothPair
  | .softplus θ _ => explicitSoftplusPair θ

theorem ClosedFormActivation.relu_pair (x y : ℝ) :
    ClosedFormActivation.relu.pair (x,y) = (max x y,y) := by
  exact Prod.ext (asymmetricLift_relu (x,y)).1 (asymmetricLift_relu (x,y)).2

/-- Each actual displayed formula satisfies the complete scalar interface.
No differentiability assumption is needed for the ReLU case. -/
theorem closed_form_activation_properties (a : ClosedFormActivation) :
    ConvexPairActivation a.pair ∧ Monotone a.pair ∧
    ValidPairActivation a.eval a.pair ∧ NonnegativePairActivation a.pair := by
  cases a with
  | relu =>
      obtain ⟨hc₁, hc₂, hm₁, hm₂, hv⟩ := relu_asymmetric_split
      refine ⟨⟨hc₁, hc₂⟩, ?_, ?_, ?_⟩
      · intro x y hxy
        exact ⟨hm₁ hxy, hm₂ hxy⟩
      · intro x y
        exact hv (x,y)
      · intro x y hx hy
        rw [ClosedFormActivation.relu_pair]
        exact ⟨le_trans hx (le_max_left x y), hy⟩
  | gaussianGelu =>
      obtain ⟨hc₁, hc₂, hm₁, hm₂, hv, hn⟩ := gaussianGelu_explicit_split
      refine ⟨⟨hc₁, hc₂⟩, ?_, hv, hn⟩
      intro x y hxy
      exact ⟨hm₁ hxy, hm₂ hxy⟩
  | swish β hβ =>
      obtain ⟨hc₁, hc₂, hm₁, hm₂, _⟩ := explicitSwish_lift β hβ
      refine ⟨⟨hc₁, hc₂⟩, ?_, explicitSwishPair_valid β,
        explicitSwishPair_nonnegative β hβ⟩
      intro x y hxy
      exact ⟨hm₁ hxy, hm₂ hxy⟩
  | sigmoid =>
      obtain ⟨hc₁, hc₂, hm₁, hm₂, hv, hn⟩ := sigmoid_smooth_explicit_split
      refine ⟨⟨hc₁, hc₂⟩, ?_, hv, hn⟩
      intro x y hxy
      exact ⟨hm₁ hxy, hm₂ hxy⟩
  | softplus θ hθ =>
      obtain ⟨hc₁, hc₂, hm₁, hm₂, hv, hn⟩ := softplus_explicit_split θ hθ
      refine ⟨⟨hc₁, hc₂⟩, ?_, hv, hn⟩
      intro x y hxy
      exact ⟨hm₁ hxy, hm₂ hxy⟩

/-- The literal closed forms supply complete convex monotone network streams,
including the genuine final signed affine readout and exact recovery. -/
theorem closed_form_affine_network {n m k : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (a : ClosedFormActivation)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) (bp bn : Vec k) :
    Monotone (net.affineDecomposeWith a.pair wp wn bp bn) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n =>
      (net.affineDecomposeWith a.pair wp wn bp bn x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n =>
      (net.affineDecomposeWith a.pair wp wn bp bn x).2 i)) ∧
    ∀ x : PairVec n,
      (net.affineDecomposeWith a.pair wp wn bp bn x).1 -
        (net.affineDecomposeWith a.pair wp wn bp bn x).2 =
      affineLayer wp wn bp bn (net.forwardWith a.eval (x.1 - x.2)) := by
  obtain ⟨hc, hm, hv, _⟩ := closed_form_activation_properties a
  exact net.affine_convex_monotone_decomposition hw a.eval a.pair
    hv hm hc wp wn hwp hwn bp bn

/-- Using the affine input embedding gives ordinary-input convex monotone
heads, with no sign restriction on the input and no extra output activation. -/
theorem closed_form_affine_dc {n m k : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (a : ClosedFormActivation)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) (bp bn : Vec k) :
    Monotone (fun x : Vec n => net.affineDecomposeWith a.pair wp wn bp bn (x,0)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : Vec n =>
      (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : Vec n =>
      (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).2 i)) ∧
    ∀ x : Vec n,
      (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).1 -
        (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).2 =
      affineLayer wp wn bp bn (net.forwardWith a.eval x) := by
  obtain ⟨hc, hm, hv, _⟩ := closed_form_activation_properties a
  exact net.affine_dc_decomposition hw a.eval a.pair hv hm hc wp wn hwp hwn bp bn

end HiddenMonotonicity.SmoothDC
