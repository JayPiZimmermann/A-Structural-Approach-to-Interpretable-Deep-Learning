import HiddenMonotonicity.TransformerExpr

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open HiddenMonotonicity.TransformerDC
open Set
open scoped BigOperators

namespace ExprReview

example (x : ℝ × ℝ) : (Expr.input ()).splitEval (fun _ => x) = x := rfl

example : (Expr.const (-3) : Expr Unit).splitEval (fun _ => (0,0)) = (0,3) := by
  norm_num [Expr.splitEval, constPair]

example : (Expr.scale (-2) (Expr.input ())).splitEval (fun _ => (5,3)) = (6,10) := by
  norm_num [Expr.splitEval, scalePair]

example : (Expr.sum 0 Fin.elim0 : Expr Unit).splitEval (fun _ => (1,2)) = 0 := by
  simp [Expr.splitEval]

example : (Expr.sum 0 Fin.elim0 : Expr Unit).eval (fun _ => -9) = 0 := by simp

def productExpr : Expr Bool := Expr.mul (Expr.input false) (Expr.input true)

example : value (productExpr.splitEval (fun b => if b then (3,-4) else (-2,1))) = -21 := by
  rw [Expr.splitEval_exact]
  norm_num [productExpr, Expr.eval, value]

def softTwo : Expr (Fin 2) := Expr.softmax 2 (fun i => Expr.input i) 0

example (x : Fin 2 → ℝ × ℝ) : value (softTwo.splitEval x) =
    Real.exp (value (x 0)) / (Real.exp (value (x 0)) + Real.exp (value (x 1))) := by
  rw [Expr.splitEval_exact]
  simp [softTwo, HiddenMonotonicity.SoftmaxDC.softmax,
    HiddenMonotonicity.SoftmaxDC.expSum, Fin.sum_univ_two]

example (x : ℝ × ℝ) :
    value ((Expr.softmax 1 (fun _ => Expr.input ()) 0).splitEval (fun _ => x)) = 1 := by
  rw [Expr.splitEval_exact]
  simp [HiddenMonotonicity.SoftmaxDC.softmax, HiddenMonotonicity.SoftmaxDC.expSum,
    Real.exp_ne_zero]

example (ε : ℝ) (hε : 0 < ε) (x : ℝ × ℝ) :
    value ((Expr.layerNorm 1 ε hε (fun _ => -2) (fun _ => 3)
      (fun _ => Expr.input ()) 0).splitEval (fun _ => x)) = 3 := by
  rw [Expr.splitEval_exact]
  simp [layerNorm, layerMean, layerVariance]

example (ε : ℝ) (hε : 0 < ε) (x : ℝ × ℝ) :
    value ((Expr.layerNorm 2 ε hε (fun _ => -5) (fun _ => -7)
      (fun _ => Expr.input ()) 0).splitEval (fun _ => x)) = -7 := by
  rw [Expr.splitEval_exact]
  simp [layerNorm, layerMean, layerVariance, Fin.sum_univ_two]

/-- Actual nonlinear nesting, including nontrivial coupled softmax and signed scale. -/
def nested (ε : ℝ) (hε : 0 < ε) : Expr (Fin 2) :=
  Expr.add (Expr.scale (-3) softTwo)
    (Expr.activation HiddenMonotonicity.SmoothDC.ClosedFormActivation.gaussianGelu
      (Expr.layerNorm 2 ε hε (fun _ => 2) (fun _ => -1)
        (fun i => Expr.input i) 1))

example (ε : ℝ) (hε : 0 < ε) (x : Fin 2 → ℝ × ℝ) :
    value ((nested ε hε).splitEval x) =
      (-3) * HiddenMonotonicity.SoftmaxDC.softmax (fun i => value (x i)) 0 +
      HiddenMonotonicity.SmoothDC.gaussianGelu
        (layerNorm ε (fun _ => 2) (fun _ => -1) (fun i => value (x i)) 1) := by
  rw [Expr.splitEval_exact]
  rfl

/-- Constant inputs provide a nonempty regularity witness without assuming the conclusion. -/
example (ε : ℝ) (hε : 0 < ε) :
    Regular (univ : Set ℝ)
      (fun t => (nested ε hε).splitEval (fun i => constPair (if i = 0 then -2 else 4))) := by
  exact Expr.splitEval_regular (nested ε hε) univ convex_univ
    (fun i _ => constPair (if i = 0 then -2 else 4))
    (fun i => Regular.const convex_univ _)

/-- Independent coordinates form a nonconstant input witness on the orthant. -/
theorem variable_regular (e : Expr (Fin 2)) :
    Regular (Ici (0 : Fin 2 → ℝ × ℝ))
      (fun x => e.splitEval x) := by
  have hf (i : Fin 2) :
      Regular (Ici (0 : Fin 2 → ℝ × ℝ)) (fun x => x i) := by
    refine ⟨⟨convex_Ici 0, ?_⟩, ⟨convex_Ici 0, ?_⟩, ?_, ?_⟩
    · intro x hx y hy a b ha hb hab
      exact le_rfl
    · intro x hx y hy a b ha hb hab
      exact le_rfl
    · intro x hx y hy hxy
      exact hxy i
    · intro x hx
      exact hx i
  exact Expr.splitEval_regular (E := Fin 2 → ℝ × ℝ) e
    (Ici (0 : Fin 2 → ℝ × ℝ)) (convex_Ici _)
    (fun i (x : Fin 2 → ℝ × ℝ) => x i) hf

/-- The whole nonlinear expression receives nonconstant independent stream inputs. -/
example (ε : ℝ) (hε : 0 < ε) :
    Regular (Ici (0 : Fin 2 → ℝ × ℝ))
      (fun x => (nested ε hε).splitEval x) := variable_regular _

/-- The product construction does not accidentally assert raw global isotonicity. -/
example : ¬ Monotone (fun z : ℝ × ℝ =>
    ((Expr.mul (Expr.input ()) (Expr.input ())).splitEval (fun _ => z)).1) := by
  intro hm
  have h := hm (show ((-2,-2) : ℝ × ℝ) ≤ (-1,-1) by constructor <;> norm_num)
  norm_num [Expr.splitEval, mulPair, productSplit] at h

end ExprReview
