import HiddenMonotonicity.TransformerPairCalculus

set_option autoImplicit false
open Set HiddenMonotonicity.TransformerDC

example : constPair (-2) = (0, 2) := by norm_num [constPair]

example : scalePair (-3) (2, 5) = (15, 6) := by norm_num [scalePair]

example : scalePair 0 (2, 5) = (0, 0) := by norm_num [scalePair]

example : addPair (constPair (-2)) (constPair 5) = (5, 2) := by
  norm_num [addPair, constPair]

example : value (mulPair (2, 5) (7, 1)) = -18 := by
  norm_num [mulPair, productSplit, value]

example : mulPair (0, 0) (3, 4) = (25 / 2, 25 / 2) := by
  norm_num [mulPair, productSplit]

example : Regular (univ : Set ℝ) (fun _ => constPair (-2)) := by
  exact Regular.const convex_univ (-2)

example : Regular (∅ : Set ℝ) (fun _ => constPair (-2)) := by
  exact Regular.const convex_empty (-2)

example : Regular (univ : Set ℝ) (fun x => scalePair (-3) (constPair (2 : ℝ))) := by
  exact (Regular.const convex_univ (2 : ℝ)).scale (-3)

example : ¬ Monotone (fun x : ℝ => (productSplit ((x, 0), (0, 0))).1) := by
  intro h
  have hm := h (show (-2 : ℝ) ≤ -1 by norm_num)
  norm_num [productSplit] at hm
