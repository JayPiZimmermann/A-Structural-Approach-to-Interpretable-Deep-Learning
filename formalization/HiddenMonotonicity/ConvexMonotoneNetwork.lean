import HiddenMonotonicity.Decomposition
import Mathlib.Analysis.Convex.Function

/-! Composition of a convex monotone pair activation through the actual finite
network. Weight positivity is needed; affine biases may have either sign. -/
noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity
open Set Matrix

/-- Each scalar output of the pair activation is jointly convex in its two inputs. -/
def ConvexPairActivation (φ : (ℝ × ℝ) → ℝ × ℝ) : Prop :=
  ConvexOn ℝ univ (fun z => (φ z).1) ∧
  ConvexOn ℝ univ (fun z => (φ z).2)

/-- A monotone convex scalar function remains convex after substituting convex
coordinate functions in both input streams. -/
theorem convex_monotone_pair_input {d n : ℕ} (f : PairVec n → ℝ)
    (hm : Monotone f) (hf : ConvexOn ℝ univ f)
    (p q : Vec d → Vec n)
    (hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
    (hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)) :
    ConvexOn ℝ univ (fun x => f (p x,q x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have huv : (p (a • x+b • y),q (a • x+b • y)) ≤
      a • (p x,q x)+b • (p y,q y) := by
    constructor
    · intro i
      exact (hp i).2 (mem_univ x) (mem_univ y) ha hb hab
    · intro i
      exact (hq i).2 (mem_univ x) (mem_univ y) ha hb hab
  exact (hm huv).trans (hf.2 (mem_univ (p x,q x)) (mem_univ (p y,q y)) ha hb hab)

theorem convex_pair_jensen (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hφ : ConvexPairActivation φ) (x y : ℝ × ℝ)
    (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    φ (t • x + (1-t) • y) ≤ t • φ x + (1-t) • φ y := by
  constructor
  · exact hφ.1.2 (mem_univ x) (mem_univ y) ht (sub_nonneg.mpr ht') (by ring)
  · exact hφ.2.2 (mem_univ x) (mem_univ y) ht (sub_nonneg.mpr ht') (by ring)

/-- Monotonicity of the complete same-parameter split network, for any monotone
pair activation and arbitrary affine biases. -/
theorem Network.decomposeWith_monotone {n m : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (φ : (ℝ × ℝ) → ℝ × ℝ) (hφ : Monotone φ) :
    Monotone (net.decomposeWith φ) := by
  induction net with
  | output n => exact monotone_id
  | layer wp wn bp bn tail ih =>
      rcases hw with ⟨hwp, hwn, htail⟩
      intro x y hxy
      apply ih htail
      have hp : preP wp wn x + bp ≤ preP wp wn y + bp :=
        add_le_add (add_le_add
          (positive_matrix_monotone wp hwp hxy.1)
          (positive_matrix_monotone wn hwn hxy.2)) le_rfl
      have hn : preN wp wn x + bn ≤ preN wp wn y + bn :=
        add_le_add (add_le_add
          (positive_matrix_monotone wn hwn hxy.1)
          (positive_matrix_monotone wp hwp hxy.2)) le_rfl
      exact ⟨fun i => (hφ ⟨hp i, hn i⟩).1,
        fun i => (hφ ⟨hp i, hn i⟩).2⟩

/-- Jensen inequality for both complete split streams. The scalar activation
need not itself be convex or monotone; only its two-stream lift must be. -/
theorem Network.decomposeWith_convex {n m : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hm : Monotone φ) (hc : ConvexPairActivation φ)
    (p q p' q' : Vec n) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (net.decomposeWith φ (mix t p p', mix t q q')).1 ≤
      mix t (net.decomposeWith φ (p,q)).1 (net.decomposeWith φ (p',q')).1 ∧
    (net.decomposeWith φ (mix t p p', mix t q q')).2 ≤
      mix t (net.decomposeWith φ (p,q)).2 (net.decomposeWith φ (p',q')).2 := by
  induction net with
  | output n => exact ⟨le_rfl, le_rfl⟩
  | layer wp wn bp bn tail ih =>
      rcases hw with ⟨_, _, htail⟩
      let zp := layerPos wp wn bp p q
      let zn := layerPos wn wp bn p q
      let zp' := layerPos wp wn bp p' q'
      let zn' := layerPos wn wp bn p' q'
      have hφ (i) := convex_pair_jensen φ hc (zp i,zn i) (zp' i,zn' i) t ht ht'
      have hp : (fun i => (φ ((mix t zp zp') i,(mix t zn zn') i)).1) ≤
          mix t (fun i => (φ (zp i,zn i)).1) (fun i => (φ (zp' i,zn' i)).1) := by
        intro i
        exact (hφ i).1
      have hn : (fun i => (φ ((mix t zp zp') i,(mix t zn zn') i)).2) ≤
          mix t (fun i => (φ (zp i,zn i)).2) (fun i => (φ (zp' i,zn' i)).2) := by
        intro i
        exact (hφ i).2
      have huv :
          ((fun i => (φ ((mix t zp zp') i,(mix t zn zn') i)).1),
           (fun i => (φ ((mix t zp zp') i,(mix t zn zn') i)).2)) ≤
          (mix t (fun i => (φ (zp i,zn i)).1) (fun i => (φ (zp' i,zn' i)).1),
           mix t (fun i => (φ (zp i,zn i)).2) (fun i => (φ (zp' i,zn' i)).2)) := ⟨hp,hn⟩
      have hmono := tail.decomposeWith_monotone htail φ hm huv
      have hconv := ih htail (fun i => (φ (zp i,zn i)).1)
        (fun i => (φ (zp i,zn i)).2) (fun i => (φ (zp' i,zn' i)).1)
        (fun i => (φ (zp' i,zn' i)).2)
      change (tail.decomposeWith φ
        ((fun i => (φ ((layerPos wp wn bp (mix t p p') (mix t q q')) i,
          (layerPos wn wp bn (mix t p p') (mix t q q')) i)).1),
         (fun i => (φ ((layerPos wp wn bp (mix t p p') (mix t q q')) i,
          (layerPos wn wp bn (mix t p p') (mix t q q')) i)).2))).1 ≤ _ ∧
        (tail.decomposeWith φ
        ((fun i => (φ ((layerPos wp wn bp (mix t p p') (mix t q q')) i,
          (layerPos wn wp bn (mix t p p') (mix t q q')) i)).1),
         (fun i => (φ ((layerPos wp wn bp (mix t p p') (mix t q q')) i,
          (layerPos wn wp bn (mix t p p') (mix t q q')) i)).2))).2 ≤ _
      rw [affine_layer_mix, affine_layer_mix]
      exact ⟨le_trans hmono.1 hconv.1, le_trans hmono.2 hconv.2⟩

/-- Both output coordinates are genuinely jointly convex functions on the full
two-stream input space; this includes zero widths and arbitrary affine biases. -/
theorem Network.decomposeWith_convexOn {n m : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hm : Monotone φ) (hc : ConvexPairActivation φ) :
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n => (net.decomposeWith φ x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n => (net.decomposeWith φ x).2 i)) := by
  have hj (x y : PairVec n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
      (net.decomposeWith φ (a • x+b • y)).1 ≤
        a • (net.decomposeWith φ x).1+b • (net.decomposeWith φ y).1 ∧
      (net.decomposeWith φ (a • x+b • y)).2 ≤
        a • (net.decomposeWith φ x).2+b • (net.decomposeWith φ y).2 := by
    have he : 1-a=b := by linarith
    have h := net.decomposeWith_convex hw φ hm hc
      x.1 x.2 y.1 y.2 a ha (by linarith)
    have hp : (a • x.1+b • y.1, a • x.2+b • y.2) = a • x+b • y := by
      ext i <;> rfl
    simpa only [mix, he, hp, Prod.mk.eta] using h
  constructor
  · intro i
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    exact (hj x y a b ha hb hab).1 i
  · intro i
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    exact (hj x y a b ha hb hab).2 i

/-- A valid convex monotone scalar lift yields an exact convex monotone
decomposition of the complete finite network, not merely a neuronwise identity. -/
theorem Network.convex_monotone_decomposition {n m : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hv : ValidPairActivation σ φ) (hm : Monotone φ) (hc : ConvexPairActivation φ) :
    Monotone (net.decomposeWith φ) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n => (net.decomposeWith φ x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n => (net.decomposeWith φ x).2 i)) ∧
    ∀ x : PairVec n, (net.decomposeWith φ x).1-(net.decomposeWith φ x).2 =
      net.forwardWith σ (x.1-x.2) := by
  exact ⟨net.decomposeWith_monotone hw φ hm,
    (net.decomposeWith_convexOn hw φ hm hc).1,
    (net.decomposeWith_convexOn hw φ hm hc).2,
    net.valid_decomposition_recovery σ φ hv⟩

/-- Convexity survives arbitrary coordinatewise convex input streams. This
includes the positive/negative-part embedding of an unrestricted signed input. -/
theorem Network.decomposeWith_convex_input {d n m : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hm : Monotone φ) (hc : ConvexPairActivation φ)
    (p q : Vec d → Vec n)
    (hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
    (hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)) :
    (∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith φ (p x,q x)).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith φ (p x,q x)).2 i)) := by
  have hj (x y : Vec d) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
      (net.decomposeWith φ (p (a • x+b • y),q (a • x+b • y))).1 ≤
        a • (net.decomposeWith φ (p x,q x)).1+b • (net.decomposeWith φ (p y,q y)).1 ∧
      (net.decomposeWith φ (p (a • x+b • y),q (a • x+b • y))).2 ≤
        a • (net.decomposeWith φ (p x,q x)).2+b • (net.decomposeWith φ (p y,q y)).2 := by
    have he : 1-a=b := by linarith
    have hp' : p (a • x+b • y) ≤ mix a (p x) (p y) := by
      intro i
      simpa [mix, he] using (hp i).2 (mem_univ x) (mem_univ y) ha hb hab
    have hq' : q (a • x+b • y) ≤ mix a (q x) (q y) := by
      intro i
      simpa [mix, he] using (hq i).2 (mem_univ x) (mem_univ y) ha hb hab
    have huv : (p (a • x+b • y),q (a • x+b • y)) ≤
        (mix a (p x) (p y),mix a (q x) (q y)) := ⟨hp',hq'⟩
    have hmono := net.decomposeWith_monotone hw φ hm huv
    have hconv := net.decomposeWith_convex hw φ hm hc
      (p x) (q x) (p y) (q y) a ha (by linarith)
    simpa [mix, he] using And.intro (hmono.1.trans hconv.1) (hmono.2.trans hconv.2)
  constructor
  · intro i
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    exact (hj x y a b ha hb hab).1 i
  · intro i
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    exact (hj x y a b ha hb hab).2 i

end HiddenMonotonicity
