import HiddenMonotonicity.Network

namespace HiddenMonotonicity
open Matrix

def Network.Nonnegative {n m} : Network n m → Prop
  | .output _ => True
  | .layer wp wn _ _ tail => (∀ i j, 0 ≤ wp i j) ∧ (∀ i j, 0 ≤ wn i j) ∧ tail.Nonnegative

theorem positive_matrix_monotone {n k} (W : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ i j, 0 ≤ W i j) {x y : Fin n → ℝ} (h : x ≤ y) :
    W.mulVec x ≤ W.mulVec y := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (h j) (hw i j)

/-- Both heads of the actual whole split network are coordinatewise monotone. -/
theorem Network.monotone {n m} (net : Network n m) (hw : net.Nonnegative)
    (p q p' q' : Fin n → ℝ) (hp : p ≤ p') (hq : q ≤ q') :
    (net.split p q).1 ≤ (net.split p' q').1 ∧
    (net.split p q).2 ≤ (net.split p' q').2 := by
  induction net with
  | output n => exact ⟨hp,hq⟩
  | layer wp wn bp bn tail ih =>
      rcases hw with ⟨hwp,hwn,htail⟩
      apply ih htail
      · intro i
        apply max_le_max
        · exact add_le_add (add_le_add
            (positive_matrix_monotone wp hwp hp i)
            (positive_matrix_monotone wn hwn hq i)) (le_refl (bp i))
        · exact add_le_add (add_le_add
            (positive_matrix_monotone wn hwn hp i)
            (positive_matrix_monotone wp hwp hq i)) (le_refl (bn i))
      · exact add_le_add (add_le_add
          (positive_matrix_monotone wn hwn hp)
          (positive_matrix_monotone wp hwp hq)) (le_refl bn)

def mix {n : ℕ} (t : ℝ) (x y : Fin n → ℝ) : Fin n → ℝ :=
  t • x + (1-t) • y

def layerPos {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (b : Fin k → ℝ) (p q : Fin n → ℝ) := wp.mulVec p + wn.mulVec q + b

theorem affine_layer_mix {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (b : Fin k → ℝ) (p q p' q' : Fin n → ℝ) (t : ℝ) :
    layerPos wp wn b (mix t p p') (mix t q q') =
      mix t (layerPos wp wn b p q) (layerPos wp wn b p' q') := by
  simp only [layerPos, mix, mulVec_add, mulVec_smul]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem max_jensen (a b c d t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    max (t*a+(1-t)*c) (t*b+(1-t)*d) ≤ t*max a b+(1-t)*max c d := by
  apply max_le
  · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left a b) ht)
      (mul_le_mul_of_nonneg_left (le_max_left c d) (sub_nonneg.mpr ht'))
  · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right a b) ht)
      (mul_le_mul_of_nonneg_left (le_max_right c d) (sub_nonneg.mpr ht'))

/-- Jensen convexity of both heads, including arbitrary affine biases. -/
theorem Network.convex {n m} (net : Network n m) (hw : net.Nonnegative)
    (p q p' q' : Fin n → ℝ) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (net.split (mix t p p') (mix t q q')).1 ≤
      mix t (net.split p q).1 (net.split p' q').1 ∧
    (net.split (mix t p p') (mix t q q')).2 ≤
      mix t (net.split p q).2 (net.split p' q').2 := by
  induction net with
  | output n => exact ⟨le_rfl,le_rfl⟩
  | layer wp wn bp bn tail ih =>
      rcases hw with ⟨_,_,htail⟩
      let zp := layerPos wp wn bp p q
      let zn := layerPos wn wp bn p q
      let zp' := layerPos wp wn bp p' q'
      let zn' := layerPos wn wp bn p' q'
      have hpos :
          (fun i => max ((mix t zp zp') i) ((mix t zn zn') i)) ≤
          mix t (fun i => max (zp i) (zn i)) (fun i => max (zp' i) (zn' i)) := by
        intro i
        exact max_jensen _ _ _ _ t ht ht'
      have hmono := tail.monotone htail _ _ _ _ hpos (le_refl (mix t zn zn'))
      have hconv := ih htail (fun i => max (zp i) (zn i)) zn
        (fun i => max (zp' i) (zn' i)) zn'
      simp only [Network.split]
      change
        (tail.split (fun i => max ((layerPos wp wn bp (mix t p p') (mix t q q')) i)
          ((layerPos wn wp bn (mix t p p') (mix t q q')) i))
          (layerPos wn wp bn (mix t p p') (mix t q q'))).1 ≤ _ ∧
        (tail.split (fun i => max ((layerPos wp wn bp (mix t p p') (mix t q q')) i)
          ((layerPos wn wp bn (mix t p p') (mix t q q')) i))
          (layerPos wn wp bn (mix t p p') (mix t q q'))).2 ≤ _
      rw [affine_layer_mix, affine_layer_mix]
      exact ⟨le_trans hmono.1 hconv.1, le_trans hmono.2 hconv.2⟩

end HiddenMonotonicity
