import HiddenMonotonicity.Decomposition
import HiddenMonotonicity.AffineHeads
import Mathlib.Analysis.Convex.Function

/-! Convex input lifts composed with the actual monotone split network.
No differentiability, gate strictness, or affine-input restriction is needed. -/
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity
open Set Matrix Finset

theorem Network.split_convex_input {d n m : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (p q : Vec d → Vec n)
    (hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
    (hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)) :
    (∀ i, ConvexOn ℝ univ (fun x => (net.split (p x) (q x)).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x => (net.split (p x) (q x)).2 i)) := by
  have hj (x y : Vec d) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
      (net.split (p (a • x+b • y)) (q (a • x+b • y))).1 ≤
        a • (net.split (p x) (q x)).1+b • (net.split (p y) (q y)).1 ∧
      (net.split (p (a • x+b • y)) (q (a • x+b • y))).2 ≤
        a • (net.split (p x) (q x)).2+b • (net.split (p y) (q y)).2 := by
    have he : 1-a=b := by linarith
    have hp' : p (a • x+b • y) ≤ mix a (p x) (p y) := by
      intro i
      simpa [mix, he] using (hp i).2 (mem_univ x) (mem_univ y) ha hb hab
    have hq' : q (a • x+b • y) ≤ mix a (q x) (q y) := by
      intro i
      simpa [mix, he] using (hq i).2 (mem_univ x) (mem_univ y) ha hb hab
    have hm := net.monotone hw _ _ _ _ hp' hq'
    have hc := net.convex hw (p x) (q x) (p y) (q y) a ha (by linarith)
    simpa [mix, he] using And.intro (hm.1.trans hc.1) (hm.2.trans hc.2)
  constructor
  · intro i
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    exact (hj x y a b ha hb hab).1 i
  · intro i
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    exact (hj x y a b ha hb hab).2 i

theorem coefficientRow_convex {d m : ℕ} (w : Vec m) (hw : ∀ i, 0 ≤ w i)
    (f : Vec d → Vec m) (hf : ∀ i, ConvexOn ℝ univ (fun x => f x i)) :
    ConvexOn ℝ univ (fun x => coefficientRow w (f x)) := by
  simp only [coefficientRow_apply]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  calc
    _ ≤ ∑ i, w i * (a*f x i+b*f y i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left ((hf i).2 (mem_univ x) (mem_univ y) ha hb hab) (hw i)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Both actual affine split heads stay convex for arbitrary coordinatewise
convex input lifts and arbitrary readout biases. -/
theorem Network.affine_heads_convex_input {d n m : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (p q : Vec d → Vec n)
    (hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
    (hq : ∀ i, ConvexOn ℝ univ (fun x => q x i))
    (wp wn : Vec m) (hwp : ∀ i, 0 ≤ wp i) (hwn : ∀ i, 0 ≤ wn i) (bp bn : ℝ) :
    ConvexOn ℝ univ (fun x => (net.affineHeads (coefficientRow wp)
      (coefficientRow wn) bp bn (p x,q x)).1) ∧
    ConvexOn ℝ univ (fun x => (net.affineHeads (coefficientRow wp)
      (coefficientRow wn) bp bn (p x,q x)).2) := by
  obtain ⟨hp',hq'⟩ := net.split_convex_input hw p q hp hq
  constructor
  · exact ((coefficientRow_convex wp hwp _ hp').add
      (coefficientRow_convex wn hwn _ hq')).add_const bp
  · exact ((coefficientRow_convex wn hwn _ hp').add
      (coefficientRow_convex wp hwp _ hq')).add_const bn

/-- The eta=1 mixing network is the same split, so the thesis's convex-input
conclusion applies to every actual hidden output coordinate. -/
theorem Network.mixing_one_convex_input {d n m : ℕ} (net : Network n m)
    (hw : net.Nonnegative) (p q : Vec d → Vec n)
    (hp : ∀ i, ConvexOn ℝ univ (fun x => p x i))
    (hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)) :
    (∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith (mixPair 1) (p x,q x)).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith (mixPair 1) (p x,q x)).2 i)) ∧
    (∀ x, (net.decomposeWith (mixPair 1) (p x,q x)).1 -
      (net.decomposeWith (mixPair 1) (p x,q x)).2 = net.eval (p x-q x)) := by
  simp only [net.mixing_one_is_split]
  exact ⟨(net.split_convex_input hw p q hp hq).1,
    (net.split_convex_input hw p q hp hq).2, fun x => net.correct (p x) (q x)⟩

end HiddenMonotonicity
