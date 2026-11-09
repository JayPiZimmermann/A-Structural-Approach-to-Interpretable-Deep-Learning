import HiddenMonotonicity.TransformerPairCalculus
import HiddenMonotonicity.LayerNormDC
import HiddenMonotonicity.ExplicitSoftmax
import HiddenMonotonicity.ClosedFormMonotoneDC

/-! Explicit scalar syntax for finite Transformer computations and their DC evaluator. -/
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity.TransformerDC
open Set
open scoped BigOperators
universe u v

/-- The constructors contain actual analytic operations; none stores a DC certificate. -/
inductive Expr (ι : Type u) where
  | input (i : ι)
  | const (c : ℝ)
  | add (a b : Expr ι)
  | scale (c : ℝ) (a : Expr ι)
  | mul (a b : Expr ι)
  | sum (d : ℕ) (xs : Fin d → Expr ι)
  | activation (φ : SmoothDC.ClosedFormActivation) (a : Expr ι)
  | softmax (d : ℕ) (xs : Fin d → Expr ι) (i : Fin d)
  | layerNorm (d : ℕ) (ε : ℝ) (hε : 0 < ε)
      (γ β : Fin d → ℝ) (xs : Fin d → Expr ι) (i : Fin d)

/-- Ordinary real-valued evaluation. -/
def Expr.eval {ι : Type u} : Expr ι → (ι → ℝ) → ℝ
  | .input i, x => x i
  | .const c, _ => c
  | .add a b, x => a.eval x + b.eval x
  | .scale c a, x => c * a.eval x
  | .mul a b, x => a.eval x * b.eval x
  | .sum _ xs, x => ∑ j, (xs j).eval x
  | .activation φ a, x => φ.eval (a.eval x)
  | .softmax _ xs i, x => SoftmaxDC.softmax (fun j => (xs j).eval x) i
  | .layerNorm _ ε _ γ β xs i, x => HiddenMonotonicity.TransformerDC.layerNorm ε γ β (fun j => (xs j).eval x) i

/-- The recursive two-stream algorithm uses the closed-form primitive splits. -/
def Expr.splitEval {ι : Type u} : Expr ι → (ι → ℝ × ℝ) → ℝ × ℝ
  | .input i, x => x i
  | .const c, _ => constPair c
  | .add a b, x => addPair (a.splitEval x) (b.splitEval x)
  | .scale c a, x => scalePair c (a.splitEval x)
  | .mul a b, x => mulPair (a.splitEval x) (b.splitEval x)
  | .sum _ xs, x => ∑ j, (xs j).splitEval x
  | .activation φ a, x => φ.pair (a.splitEval x)
  | .softmax _ xs i, x =>
      (SoftmaxDC.softmaxSplitFirst i
        ((fun j => ((xs j).splitEval x).1), fun j => ((xs j).splitEval x).2),
       SoftmaxDC.softmaxSplitSecond i
        ((fun j => ((xs j).splitEval x).1), fun j => ((xs j).splitEval x).2))
  | .layerNorm _ ε _ γ β xs i, x =>
      layerNormPair ε γ β (fun j => (xs j).splitEval x) i

@[simp] theorem Expr.eval_input {ι : Type u} (i : ι) (x : ι → ℝ) :
    (Expr.input i).eval x = x i := rfl
@[simp] theorem Expr.eval_const {ι : Type u} (c : ℝ) (x : ι → ℝ) :
    (Expr.const c).eval x = c := rfl
@[simp] theorem Expr.eval_add {ι : Type u} (a b : Expr ι) (x : ι → ℝ) :
    (Expr.add a b).eval x = a.eval x + b.eval x := rfl
@[simp] theorem Expr.eval_scale {ι : Type u} (c : ℝ) (a : Expr ι) (x : ι → ℝ) :
    (Expr.scale c a).eval x = c * a.eval x := rfl
@[simp] theorem Expr.eval_mul {ι : Type u} (a b : Expr ι) (x : ι → ℝ) :
    (Expr.mul a b).eval x = a.eval x * b.eval x := rfl
@[simp] theorem Expr.eval_sum {ι : Type u} (d : ℕ) (xs : Fin d → Expr ι) (x : ι → ℝ) :
    (Expr.sum d xs).eval x = ∑ j, (xs j).eval x := rfl
@[simp] theorem Expr.eval_activation {ι : Type u} (φ : SmoothDC.ClosedFormActivation)
    (a : Expr ι) (x : ι → ℝ) :
    (Expr.activation φ a).eval x = φ.eval (a.eval x) := rfl
@[simp] theorem Expr.eval_softmax {ι : Type u} (d : ℕ) (xs : Fin d → Expr ι)
    (i : Fin d) (x : ι → ℝ) :
    (Expr.softmax d xs i).eval x = SoftmaxDC.softmax (fun j => (xs j).eval x) i := rfl
@[simp] theorem Expr.eval_layerNorm {ι : Type u} (d : ℕ) (ε : ℝ) (hε : 0 < ε)
    (γ β : Fin d → ℝ) (xs : Fin d → Expr ι) (i : Fin d) (x : ι → ℝ) :
    (Expr.layerNorm d ε hε γ β xs i).eval x =
      HiddenMonotonicity.TransformerDC.layerNorm ε γ β (fun j => (xs j).eval x) i := rfl

/-- Exactness is independent of stream positivity. Positivity is needed below
for composition of the convex heads, not for their subtraction identity. -/
theorem Expr.splitEval_exact {ι : Type u} (e : Expr ι) (x : ι → ℝ × ℝ) :
    value (e.splitEval x) = e.eval (fun i => value (x i)) := by
  induction e with
  | input i => rfl
  | const c => exact value_constPair c
  | add a b ha hb => simpa only [Expr.splitEval, Expr.eval, value_addPair, ha, hb]
  | scale c a ha => simpa only [Expr.splitEval, Expr.eval, value_scalePair, ha]
  | mul a b ha hb => simpa only [Expr.splitEval, Expr.eval, value_mulPair, ha, hb]
  | sum d xs ih =>
      simp only [Expr.splitEval, Expr.eval, value_sum]
      exact Finset.sum_congr rfl (fun j _ => ih j)
  | activation φ a ha =>
      have hv := (SmoothDC.closed_form_activation_properties φ).2.2.1
      change value (φ.pair (a.splitEval x)) = φ.eval (a.eval (fun i => value (x i)))
      change (φ.pair (a.splitEval x)).1 - (φ.pair (a.splitEval x)).2 = _
      rw [hv, ← ha]
      rfl
  | softmax d xs i ih =>
      letI : Nonempty (Fin d) := ⟨i⟩
      change SoftmaxDC.softmaxSplitFirst i _ - SoftmaxDC.softmaxSplitSecond i _ = _
      rw [(SoftmaxDC.softmax_split_properties i).2.2.2.2.1]
      apply congrArg (fun z => SoftmaxDC.softmax z i)
      funext j
      exact ih j
  | layerNorm d ε hε γ β xs i ih =>
      change value (layerNormPair ε γ β (fun j => (xs j).splitEval x) i) = _
      rw [layerNormPair_exact ε hε γ β]
      apply congrArg (fun z => HiddenMonotonicity.TransformerDC.layerNorm ε γ β z i)
      funext j
      exact ih j

/-- Compositional structural invariant for the explicit recursive algorithm. -/
theorem Expr.splitEval_regular {ι : Type u} {E : Type v}
    [AddCommGroup E] [Module ℝ E] [Preorder E]
    (e : Expr ι) (s : Set E) (hs : Convex ℝ s) (f : ι → E → ℝ × ℝ)
    (hf : ∀ i, Regular s (f i)) :
    Regular s (fun x => e.splitEval (fun i => f i x)) := by
  induction e with
  | input i => exact hf i
  | const c => exact Regular.const hs c
  | add a b ha hb => exact ha.add hb
  | scale c a ha => exact ha.scale c
  | mul a b ha hb => exact ha.mul hb
  | sum d xs ih =>
      exact Regular.finset_sum Finset.univ
        (fun j x => (xs j).splitEval (fun i => f i x)) hs (fun j _ => ih j)
  | activation φ a ha =>
      obtain ⟨hc, hm, _, hn⟩ := SmoothDC.closed_form_activation_properties φ
      exact ha.scalar_comp φ.pair hc.1 hc.2 hm (fun z hz => hn z.1 z.2 hz.1 hz.2)
  | softmax d xs i ih =>
      letI : Nonempty (Fin d) := ⟨i⟩
      obtain ⟨hp, hq, hmp, hmq, _, hn⟩ := SoftmaxDC.softmax_split_properties i
      exact Regular.vector_comp
        (fun z => (SoftmaxDC.softmaxSplitFirst i z, SoftmaxDC.softmaxSplitSecond i z))
        hp hq (fun _ _ h => ⟨hmp h, hmq h⟩) hn hs
        (fun j x => (xs j).splitEval (fun i => f i x)) ih
  | layerNorm d ε hε γ β xs i ih =>
      exact layerNormPair_regular s hs ε hε γ β
        (fun j x => (xs j).splitEval (fun i => f i x)) ih i

end HiddenMonotonicity.TransformerDC
