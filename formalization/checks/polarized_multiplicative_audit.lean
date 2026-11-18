import Thesis.PolarizedMultiplicative

noncomputable section
open HiddenMonotonicity.TransformerDC Set

example {ι : Type} (e : Expr ι) :
    ConvexOn ℝ (Ici (0 : DoubledInput ι)) (fun x => (e.decompose x).1) ∧
    ConvexOn ℝ (Ici (0 : DoubledInput ι)) (fun x => (e.decompose x).2) ∧
    MonotoneOn e.decompose (Ici (0 : DoubledInput ι)) ∧
    (∀ x : DoubledInput ι, 0 ≤ x → 0 ≤ e.decompose x) ∧
    (∀ x : DoubledInput ι,
      (e.decompose x).1 - (e.decompose x).2 = e.eval (x.1 - x.2)) ∧
    ConvexOn ℝ univ (fun x : ι → ℝ => (e.rawDecompose x).1) ∧
    ConvexOn ℝ univ (fun x : ι → ℝ => (e.rawDecompose x).2) ∧
    (∀ x : ι → ℝ, 0 ≤ e.rawDecompose x) ∧
    (∀ x : ι → ℝ,
      (e.rawDecompose x).1 - (e.rawDecompose x).2 = e.eval x) := by
  obtain ⟨h, exactness, raw⟩ := Thesis.PolarizedMultiplicative.polarized_expression_dc e
  exact ⟨h.convex_fst, h.convex_snd, h.monotone, h.nonnegative, exactness, raw⟩

example {ι : Type} (a b : Expr ι) (x : DoubledInput ι) :
    (Expr.mul a b).decompose x = productSplit (a.decompose x, b.decompose x) := rfl

#print axioms Thesis.PolarizedMultiplicative.polarized_expression_dc
