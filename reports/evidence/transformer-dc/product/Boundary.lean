import HiddenMonotonicity.PolarizedProductDC

set_option autoImplicit false
open Set HiddenMonotonicity.TransformerDC

example : productSplit ((0, 0), (0, 0)) = (0, 0) := by
  norm_num [productSplit]

example : productSplit ((3, 1), (2, 5)) = (61 / 2, 73 / 2) := by
  norm_num [productSplit]

example : (productSplit ((3, 1), (2, 5))).1 -
    (productSplit ((3, 1), (2, 5))).2 = -6 := by
  norm_num [productSplit]

example (a c : ℝ) :
    productSplit ((a, 0), (c, 0)) = ((a + c)^2 / 2, (a^2 + c^2) / 2) := by
  simp [productSplit]

example : productSplit ((0, 0), (0, 0)) ≤ productSplit ((1, 0), (0, 2)) := by
  apply productSplit_monotoneOn <;> constructor <;> constructor <;> norm_num

-- Global convexity does not imply global coordinatewise monotonicity.
example : ¬ Monotone productSplit := by
  intro h
  have hbad := h (show ((-1, 0), (0, 0)) ≤ (((0, 0), (0, 0)) : FourStreams) by
    constructor <;> constructor <;> norm_num)
  norm_num [productSplit] at hbad

-- A globally nonnegative convex stream can be composed even when it is not monotone.
example : ConvexOn ℝ univ
    (fun x : ℝ => (productSplit ((x^2, 0), (1, 0))).1) := by
  have hsq : ConvexOn ℝ univ (fun x : ℝ => x^2) :=
    Even.convexOn_pow (show Even 2 from ⟨1, rfl⟩)
  exact (productSplit_convex_composition univ (fun x : ℝ => x^2)
    (fun _ => 0) (fun _ => 1) (fun _ => 0)
    hsq (convexOn_const 0 convex_univ) (convexOn_const 1 convex_univ)
    (convexOn_const 0 convex_univ)
    (fun x _ => sq_nonneg x) (by intros; norm_num)
    (by intros; norm_num) (by intros; norm_num)).1

example (x : ℝ) :
    (productSplit ((x^2, 0), (1, 0))).1 -
    (productSplit ((x^2, 0), (1, 0))).2 = x^2 := by
  simpa using productSplit_exact ((x^2, 0), (1, 0))

example : MonotoneOn (fun x : ℝ => productSplit ((x, 0), (1, 0))) (Ici 0) := by
  apply productSplit_monotone_composition
  · intro x _ y _ hxy; exact hxy
  · intro x _ y _ _; exact le_rfl
  · intro x _ y _ _; exact le_rfl
  · intro x _ y _ _; exact le_rfl
  · intro x hx; exact hx
  · intros; norm_num
  · intros; norm_num
  · intros; norm_num

-- Removing nonnegativity from the convex-composition premise is false.
example : ¬ ConvexOn ℝ univ
    (fun x : ℝ => (productSplit ((x^2 - 2, 0), (0, 0))).1) := by
  intro h
  have hbad := h.2 (mem_univ (-1 : ℝ)) (mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  norm_num [productSplit] at hbad
