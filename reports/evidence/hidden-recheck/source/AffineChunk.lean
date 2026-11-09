import HiddenMonotonicity.OriginalTrace
import HiddenMonotonicity.Convexity

namespace HiddenMonotonicity
open Matrix

/-- The ungated biased affine chunk on two streams. -/
noncomputable def affineChunk {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) : PairVec k :=
  (preP wp wn x + bp, preN wp wn x + bn)

theorem affineChunk_recovery {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) :
    (affineChunk wp wn bp bn x).1 - (affineChunk wp wn bp bn x).2 =
      affineLayer wp wn bp bn (x.1-x.2) := preactivation_difference wp wn bp bn x

theorem affineChunk_nonnegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (hw : ∀ i j, 0≤wp i j ∧ 0≤wn i j)
    (hb : 0≤bp ∧ 0≤bn) (x : PairVec n) (hx : 0≤x) :
    0≤affineChunk wp wn bp bn x := by
  have hm (w : Matrix (Fin k) (Fin n) ℝ) (h : ∀ i j, 0≤w i j)
      (z : Vec n) (hz : 0≤z) : 0≤w.mulVec z := by
    intro i
    change 0 ≤ ∑ j, w i j * z j
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (h i j) (hz j))
  exact ⟨add_nonneg (add_nonneg (hm wp (fun i j => (hw i j).1) x.1 hx.1)
    (hm wn (fun i j => (hw i j).2) x.2 hx.2)) hb.1,
    add_nonneg (add_nonneg (hm wn (fun i j => (hw i j).2) x.1 hx.1)
    (hm wp (fun i j => (hw i j).1) x.2 hx.2)) hb.2⟩

theorem affineChunk_monotone {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (hw : ∀ i j, 0≤wp i j ∧ 0≤wn i j) :
    Monotone (affineChunk wp wn bp bn) := by
  intro x y h
  exact ⟨add_le_add (add_le_add
    (positive_matrix_monotone wp (fun i j => (hw i j).1) h.1)
    (positive_matrix_monotone wn (fun i j => (hw i j).2) h.2)) (le_refl bp),
    add_le_add (add_le_add
    (positive_matrix_monotone wn (fun i j => (hw i j).2) h.1)
    (positive_matrix_monotone wp (fun i j => (hw i j).1) h.2)) (le_refl bn)⟩

/-- Exact affine dependence on both inputs, with arbitrary signed biases. -/
theorem affineChunk_affine {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x y : PairVec n) (a b : ℝ) (hab : a+b=1) :
    affineChunk wp wn bp bn (a • x+b • y) =
      a • affineChunk wp wn bp bn x+b • affineChunk wp wn bp bn y := by
  apply Prod.ext <;> funext i
  · change preP wp wn (a • x+b • y) i+bp i =
      a*(preP wp wn x i+bp i)+b*(preP wp wn y i+bp i)
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -(bp i)*hab
  · change preN wp wn (a • x+b • y) i+bn i =
      a*(preN wp wn x i+bn i)+b*(preN wp wn y i+bn i)
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -(bn i)*hab

theorem affineChunk_convex {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (i : Fin k) :
    ConvexOn ℝ Set.univ (fun x => (affineChunk wp wn bp bn x).1 i) ∧
    ConvexOn ℝ Set.univ (fun x => (affineChunk wp wn bp bn x).2 i) := by
  constructor <;> refine ⟨convex_univ, ?_⟩ <;> intro x _ y _ a b _ _ hab
  · dsimp only
    rw [affineChunk_affine wp wn bp bn x y a b hab]
    exact le_rfl
  · dsimp only
    rw [affineChunk_affine wp wn bp bn x y a b hab]
    exact le_rfl

/-- Source-facing linear-chunk theorem: affine recovery, nonnegative outputs,
coordinatewise monotonicity, affine dependence and convexity are all included.
Nonnegative sign parts include the canonical split of arbitrary signed A,c. -/
theorem linear_chunk_properties {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (hw : ∀ i j, 0≤wp i j ∧ 0≤wn i j) (hb : 0≤bp ∧ 0≤bn) :
    (∀ x, (affineChunk wp wn bp bn x).1-(affineChunk wp wn bp bn x).2 =
      affineLayer wp wn bp bn (x.1-x.2)) ∧
    (∀ x, 0≤x → 0≤affineChunk wp wn bp bn x) ∧
    Monotone (affineChunk wp wn bp bn) ∧
    (∀ x y (a b : ℝ), a+b=1 → affineChunk wp wn bp bn (a • x+b • y) =
      a • affineChunk wp wn bp bn x+b • affineChunk wp wn bp bn y) ∧
    (∀ i, ConvexOn ℝ Set.univ (fun x => (affineChunk wp wn bp bn x).1 i) ∧
      ConvexOn ℝ Set.univ (fun x => (affineChunk wp wn bp bn x).2 i)) :=
  ⟨affineChunk_recovery wp wn bp bn, affineChunk_nonnegative wp wn bp bn hw hb,
    affineChunk_monotone wp wn bp bn hw, affineChunk_affine wp wn bp bn,
    affineChunk_convex wp wn bp bn⟩

end HiddenMonotonicity
