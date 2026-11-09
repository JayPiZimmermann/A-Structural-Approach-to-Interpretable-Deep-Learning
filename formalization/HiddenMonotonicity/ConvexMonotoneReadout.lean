import HiddenMonotonicity.ConvexMonotoneNetwork
import Mathlib.Analysis.Convex.Function

/-! An ungated signed affine readout for arbitrary valid pair activations.
The readout biases are unrestricted for recovery, monotonicity, and convexity.
Only the split weight matrices must be entrywise nonnegative for the latter two.
-/
noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity
open Set Matrix

/-- Append the actual split affine output, without applying another activation. -/
def Network.affineDecomposeWith {n m k : ℕ} (net : Network n m)
    (φ : (ℝ × ℝ) → ℝ × ℝ) (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (bp bn : Vec k) (x : PairVec n) : PairVec k :=
  (preP wp wn (net.decomposeWith φ x) + bp,
   preN wp wn (net.decomposeWith φ x) + bn)

/-- The split affine heads recover an arbitrary signed logit, including negative
outputs and arbitrary affine biases. No positivity of the target is assumed. -/
theorem Network.affineDecomposeWith_recovery {n m k : ℕ} (net : Network n m)
    (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ) (hv : ValidPairActivation σ φ)
    (wp wn : Matrix (Fin k) (Fin m) ℝ) (bp bn : Vec k) (x : PairVec n) :
    (net.affineDecomposeWith φ wp wn bp bn x).1 -
      (net.affineDecomposeWith φ wp wn bp bn x).2 =
      affineLayer wp wn bp bn (net.forwardWith σ (x.1-x.2)) := by
  unfold Network.affineDecomposeWith
  rw [preactivation_difference, net.valid_decomposition_recovery σ φ hv]

/-- Nonnegative split weights preserve the order of the two backbone streams. -/
theorem Network.affineDecomposeWith_monotone_of_monotone {n m k : ℕ}
    (net : Network n m) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hm : Monotone (net.decomposeWith φ))
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j)
    (bp bn : Vec k) : Monotone (net.affineDecomposeWith φ wp wn bp bn) := by
  intro x y hxy
  have h := hm hxy
  constructor
  · exact add_le_add (add_le_add
      (positive_matrix_monotone wp hwp h.1)
      (positive_matrix_monotone wn hwn h.2)) le_rfl
  · exact add_le_add (add_le_add
      (positive_matrix_monotone wn hwn h.1)
      (positive_matrix_monotone wp hwp h.2)) le_rfl

/-- A nonnegative matrix preserves coordinatewise convexity on split inputs. -/
theorem matrix_convex_pair_input {n m k : ℕ}
    (W : Matrix (Fin k) (Fin m) ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (f : PairVec n → Vec m)
    (hf : ∀ j, ConvexOn ℝ univ (fun x => f x j)) (i : Fin k) :
    ConvexOn ℝ univ (fun x => W.mulVec (f x) i) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
  calc
    _ ≤ ∑ j, W i j * (a * f x j + b * f y j) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        ((hf j).2 (mem_univ x) (mem_univ y) ha hb hab) (hW i j)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Appending the split affine readout preserves both convex backbone heads. -/
theorem Network.affineDecomposeWith_convex_of_convex {n m k : ℕ}
    (net : Network n m) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hp : ∀ j, ConvexOn ℝ univ (fun x => (net.decomposeWith φ x).1 j))
    (hn : ∀ j, ConvexOn ℝ univ (fun x => (net.decomposeWith φ x).2 j))
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j)
    (bp bn : Vec k) :
    (∀ i, ConvexOn ℝ univ (fun x => (net.affineDecomposeWith φ wp wn bp bn x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x => (net.affineDecomposeWith φ wp wn bp bn x).2 i)) := by
  constructor
  · intro i
    exact ((matrix_convex_pair_input wp hwp _ hp i).add
      (matrix_convex_pair_input wn hwn _ hn i)).add_const (bp i)
  · intro i
    exact ((matrix_convex_pair_input wn hwn _ hp i).add
      (matrix_convex_pair_input wp hwp _ hn i)).add_const (bn i)

/-- The actual finite split network followed by an ungated affine output is
coordinatewise nondecreasing whenever the pair activation is. -/
theorem Network.affineDecomposeWith_monotone {n m k : ℕ}
    (net : Network n m) (hw : net.Nonnegative) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hm : Monotone φ) (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) (bp bn : Vec k) :
    Monotone (net.affineDecomposeWith φ wp wn bp bn) :=
  net.affineDecomposeWith_monotone_of_monotone φ
    (net.decomposeWith_monotone hw φ hm) wp wn hwp hwn bp bn

/-- Every ungated output coordinate has convex heads, under only local
activation conditions and nonnegative split weight matrices. -/
theorem Network.affineDecomposeWith_convex {n m k : ℕ}
    (net : Network n m) (hw : net.Nonnegative) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hm : Monotone φ) (hc : ConvexPairActivation φ)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) (bp bn : Vec k) :
    (∀ i, ConvexOn ℝ univ (fun x => (net.affineDecomposeWith φ wp wn bp bn x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x => (net.affineDecomposeWith φ wp wn bp bn x).2 i)) :=
  net.affineDecomposeWith_convex_of_convex φ
    (net.decomposeWith_convexOn hw φ hm hc).1
    (net.decomposeWith_convexOn hw φ hm hc).2 wp wn hwp hwn bp bn

/-- Full decomposition theorem with the actual signed affine output. Recovery
holds for every input, and both heads are jointly convex and monotone on the
full split-input space. No output activation or positivity assumption is used. -/
theorem Network.affine_convex_monotone_decomposition {n m k : ℕ}
    (net : Network n m) (hw : net.Nonnegative)
    (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hv : ValidPairActivation σ φ) (hm : Monotone φ) (hc : ConvexPairActivation φ)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) (bp bn : Vec k) :
    Monotone (net.affineDecomposeWith φ wp wn bp bn) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n =>
      (net.affineDecomposeWith φ wp wn bp bn x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n =>
      (net.affineDecomposeWith φ wp wn bp bn x).2 i)) ∧
    ∀ x : PairVec n,
      (net.affineDecomposeWith φ wp wn bp bn x).1 -
        (net.affineDecomposeWith φ wp wn bp bn x).2 =
        affineLayer wp wn bp bn (net.forwardWith σ (x.1-x.2)) := by
  exact ⟨net.affineDecomposeWith_monotone hw φ hm wp wn hwp hwn bp bn,
    (net.affineDecomposeWith_convex hw φ hm hc wp wn hwp hwn bp bn).1,
    (net.affineDecomposeWith_convex hw φ hm hc wp wn hwp hwn bp bn).2,
    net.affineDecomposeWith_recovery σ φ hv wp wn bp bn⟩

/-- Restricting a jointly convex pair function to the affine embedding
`x ↦ (x,0)` gives a convex function on the original signed input space. -/
theorem convex_pair_zero_input {n : ℕ} (f : PairVec n → ℝ)
    (hf : ConvexOn ℝ univ f) :
    ConvexOn ℝ univ (fun x : Vec n => f (x,0)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simpa using hf.2 (mem_univ (x,0)) (mem_univ (y,0)) ha hb hab

/-- A DC decomposition on ordinary signed inputs, including an arbitrary
signed affine output. Both heads are convex and coordinatewise nondecreasing;
their difference recovers the original network with no input sign restriction. -/
theorem Network.affine_dc_decomposition {n m k : ℕ}
    (net : Network n m) (hw : net.Nonnegative)
    (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hv : ValidPairActivation σ φ) (hm : Monotone φ) (hc : ConvexPairActivation φ)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) (bp bn : Vec k) :
    Monotone (fun x : Vec n => net.affineDecomposeWith φ wp wn bp bn (x,0)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : Vec n =>
      (net.affineDecomposeWith φ wp wn bp bn (x,0)).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : Vec n =>
      (net.affineDecomposeWith φ wp wn bp bn (x,0)).2 i)) ∧
    ∀ x : Vec n,
      (net.affineDecomposeWith φ wp wn bp bn (x,0)).1 -
        (net.affineDecomposeWith φ wp wn bp bn (x,0)).2 =
        affineLayer wp wn bp bn (net.forwardWith σ x) := by
  have h := net.affine_convex_monotone_decomposition hw σ φ hv hm hc wp wn hwp hwn bp bn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact h.1 ⟨hxy, le_rfl⟩
  · intro i
    exact convex_pair_zero_input _ (h.2.1 i)
  · intro i
    exact convex_pair_zero_input _ (h.2.2.1 i)
  · intro x
    simpa using h.2.2.2 (x,0)

/-- Convex input branches can be composed with the actual affine readout.
The branches need not be monotone functions of the raw input. -/
theorem Network.affineDecomposeWith_convex_input {d n m k : ℕ}
    (net : Network n m) (hw : net.Nonnegative) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hm : Monotone φ) (hc : ConvexPairActivation φ)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) (bp bn : Vec k)
    (p q : Vec d → Vec n)
    (hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
    (hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)) :
    (∀ i, ConvexOn ℝ univ (fun x =>
      (net.affineDecomposeWith φ wp wn bp bn (p x,q x)).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x =>
      (net.affineDecomposeWith φ wp wn bp bn (p x,q x)).2 i)) := by
  have hmono := net.affineDecomposeWith_monotone hw φ hm wp wn hwp hwn bp bn
  have hconv := net.affineDecomposeWith_convex hw φ hm hc wp wn hwp hwn bp bn
  constructor
  · intro i
    exact convex_monotone_pair_input _ (fun _ _ hxy => (hmono hxy).1 i)
      (hconv.1 i) p q hp hq
  · intro i
    exact convex_monotone_pair_input _ (fun _ _ hxy => (hmono hxy).2 i)
      (hconv.2 i) p q hp hq

/-- The standard nonnegative two-stream representation of a signed input. -/
def signedInput {n : ℕ} (x : Vec n) : PairVec n :=
  ((fun i => max (x i) 0), (fun i => max (-x i) 0))

theorem signedInput_nonnegative {n : ℕ} (x : Vec n) : 0 ≤ signedInput x :=
  ⟨fun i => le_max_right (x i) 0, fun i => le_max_right (-x i) 0⟩

theorem signedInput_difference {n : ℕ} (x : Vec n) :
    (signedInput x).1 - (signedInput x).2 = x := by
  funext i
  change max (x i) 0 - max (-x i) 0 = x i
  rcases le_total 0 (x i) with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    ring

theorem signedInput_convex {n : ℕ} :
    (∀ i, ConvexOn ℝ univ (fun x : Vec n => (signedInput x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : Vec n => (signedInput x).2 i)) := by
  constructor
  · intro i
    have h : ConvexOn ℝ univ (fun x : Vec n => x i) :=
      ⟨convex_univ, fun _ _ _ _ _ _ _ _ _ => le_rfl⟩
    exact h.sup (convexOn_const 0 convex_univ)
  · intro i
    have h : ConvexOn ℝ univ (fun x : Vec n => -x i) := by
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b _ _ _
      apply le_of_eq
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact h.sup (convexOn_const 0 convex_univ)

/-- The familiar positive/negative input split gives convex heads and exact
recovery for the full network with signed affine readout. Raw-input monotonicity
is not asserted, since the negative input branch is order reversing. -/
theorem Network.affine_signed_input_dc_decomposition {n m k : ℕ}
    (net : Network n m) (hw : net.Nonnegative)
    (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hv : ValidPairActivation σ φ) (hm : Monotone φ) (hc : ConvexPairActivation φ)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) (bp bn : Vec k) :
    (∀ i, ConvexOn ℝ univ (fun x : Vec n =>
      (net.affineDecomposeWith φ wp wn bp bn (signedInput x)).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : Vec n =>
      (net.affineDecomposeWith φ wp wn bp bn (signedInput x)).2 i)) ∧
    ∀ x : Vec n,
      (net.affineDecomposeWith φ wp wn bp bn (signedInput x)).1 -
        (net.affineDecomposeWith φ wp wn bp bn (signedInput x)).2 =
        affineLayer wp wn bp bn (net.forwardWith σ x) := by
  have hconv := net.affineDecomposeWith_convex_input hw φ hm hc wp wn hwp hwn bp bn
    (fun x => (signedInput x).1) (fun x => (signedInput x).2)
    signedInput_convex.1 signedInput_convex.2
  refine ⟨hconv.1, hconv.2, ?_⟩
  intro x
  rw [net.affineDecomposeWith_recovery σ φ hv wp wn bp bn, signedInput_difference]

end HiddenMonotonicity
