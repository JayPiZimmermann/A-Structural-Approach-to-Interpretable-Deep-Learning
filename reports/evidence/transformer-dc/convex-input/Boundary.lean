import HiddenMonotonicity.TransformerConvexInput

set_option autoImplicit false
open Set HiddenMonotonicity.TransformerDC

example : ConvexOn ℝ univ (fun x : Unit → ℝ =>
    max (x ()) 0 + max (-x ()) 0) := by
  apply convex_signed_input_lift (fun z : (Unit → ℝ) × (Unit → ℝ) => z.1 () + z.2 ())
  · refine ⟨?_, ?_⟩
    · intro x hx y hy a b ha hb hab
      exact ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)),
        fun i => add_nonneg (mul_nonneg ha (hx.2 i)) (mul_nonneg hb (hy.2 i))⟩
    · intro x hx y hy a b ha hb hab
      change (a * x.1 () + b * y.1 ()) + (a * x.2 () + b * y.2 ()) ≤
        a * (x.1 () + x.2 ()) + b * (y.1 () + y.2 ())
      nlinarith only
  · intro x hx y hy hxy
    exact add_le_add (hxy.1 ()) (hxy.2 ())

example : ¬ Monotone (fun x : ℝ => max (-x) 0) := by
  intro h
  have hm := h (show (-1 : ℝ) ≤ 0 by norm_num)
  norm_num at hm
