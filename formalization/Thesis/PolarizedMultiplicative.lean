import HiddenMonotonicity.TransformerExprProperties

/-! The polarized recursive evaluator gives a DC decomposition of every finite
scalar expression. Multiplicative ReLU networks use inputs, constants, sums,
signed scaling, products, and ReLU; max a b is ReLU (a-b) + b.
No new product operation or assumed convexity certificate is introduced. -/
noncomputable section
set_option autoImplicit false
namespace Thesis.PolarizedMultiplicative
open HiddenMonotonicity.TransformerDC Set
universe u

/-- Combined contract of the existing polarized algorithm, valid at every finite
expression depth, on independent nonnegative input pairs and on raw signed inputs. -/
theorem polarized_expression_dc {ι : Type u} (e : Expr ι) :
    Regular (Ici (0 : DoubledInput ι)) e.decompose ∧
    (∀ x : DoubledInput ι,
      (e.decompose x).1 - (e.decompose x).2 = e.eval (x.1 - x.2)) ∧
    ConvexOn ℝ univ (fun x : ι → ℝ => (e.rawDecompose x).1) ∧
    ConvexOn ℝ univ (fun x : ι → ℝ => (e.rawDecompose x).2) ∧
    (∀ x : ι → ℝ, 0 ≤ e.rawDecompose x) ∧
    (∀ x : ι → ℝ,
      (e.rawDecompose x).1 - (e.rawDecompose x).2 = e.eval x) := by
  exact ⟨e.decompose_regular, e.decompose_exact,
    e.rawDecompose_convex.1, e.rawDecompose_convex.2,
    e.rawDecompose_nonnegative, e.rawDecompose_exact⟩

end Thesis.PolarizedMultiplicative
