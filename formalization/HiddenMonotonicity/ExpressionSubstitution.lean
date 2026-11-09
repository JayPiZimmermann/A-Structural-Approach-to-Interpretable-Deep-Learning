import HiddenMonotonicity.MultiplicativeSplit
import Mathlib.Algebra.BigOperators.Fin

namespace HiddenMonotonicity

noncomputable def PositiveExpr.substitute {ι κ} (σ : ι → PositiveExpr κ) :
    PositiveExpr ι → PositiveExpr κ
  | .input i => σ i
  | .constant c hc => .constant c hc
  | .add a b => .add (a.substitute σ) (b.substitute σ)
  | .scale c hc a => .scale c hc (a.substitute σ)
  | .mul a b => .mul (a.substitute σ) (b.substitute σ)
  | .maximum a b => .maximum (a.substitute σ) (b.substitute σ)

theorem PositiveExpr.substitute_eval {ι κ} (σ : ι → PositiveExpr κ)
    (e : PositiveExpr ι) (x : κ → ℝ) :
    (e.substitute σ).eval x=e.eval (fun i => (σ i).eval x) := by
  induction e <;> simp_all [substitute,eval]

theorem PositiveExpr.substitute_additive {ι κ} (σ : ι → PositiveExpr κ)
    (hσ : ∀ i, (σ i).Additive) (e : PositiveExpr ι) (he : e.Additive) :
    (e.substitute σ).Additive := by
  induction e with
  | input i => exact hσ i
  | constant c hc => trivial
  | add a b ha hb => exact ⟨ha he.1,hb he.2⟩
  | scale c hc a ha => exact ha he
  | mul a b ha hb => exact False.elim he
  | maximum a b ha hb => exact ⟨ha he.1,hb he.2⟩

def SignedExpr.Additive {ι} : SignedExpr ι → Prop
  | .input _ | .constant _ => True
  | .add a b | .maximum a b => a.Additive ∧ b.Additive
  | .scale _ a => a.Additive
  | .mul _ _ => False

theorem SignedExpr.split_additive {ι} (e : SignedExpr ι) (he : e.Additive) :
    e.split.1.Additive ∧ e.split.2.Additive := by
  induction e with
  | input i => exact ⟨trivial,trivial⟩
  | constant c => exact ⟨trivial,trivial⟩
  | add a b ha hb => exact ⟨⟨(ha he.1).1,(hb he.2).1⟩,⟨(ha he.1).2,(hb he.2).2⟩⟩
  | scale c a ha => exact ⟨⟨(ha he).1,(ha he).2⟩,⟨(ha he).2,(ha he).1⟩⟩
  | mul a b ha hb => exact False.elim he
  | maximum a b ha hb => exact ⟨⟨⟨(ha he.1).1,(hb he.2).2⟩,
      ⟨(hb he.2).1,(ha he.1).2⟩⟩,⟨(ha he.1).2,(hb he.2).2⟩⟩

noncomputable def SignedExpr.sum {ι} : List (SignedExpr ι) → SignedExpr ι
  | [] => .constant 0
  | e::es => .add e (sum es)

theorem SignedExpr.sum_eval {ι} (es : List (SignedExpr ι)) (x : ι → ℝ) :
    (SignedExpr.sum es).eval x=(es.map (fun e => e.eval x)).sum := by
  induction es <;> simp_all [SignedExpr.sum,SignedExpr.eval]

noncomputable def SignedExpr.affine {n} (w : Vec n) (b : ℝ) : SignedExpr (Fin n) :=
  .add (.constant b) (SignedExpr.sum (List.ofFn (fun i => .scale (w i) (.input i))))

theorem SignedExpr.affine_eval {n} (w : Vec n) (b : ℝ) (x : Vec n) :
    (SignedExpr.affine w b).eval x=b+∑ i,w i*x i := by
  simp [SignedExpr.affine,SignedExpr.eval,SignedExpr.sum_eval,List.map_ofFn,List.sum_ofFn,Function.comp_def]

theorem SignedExpr.affine_additive {n} (w : Vec n) (b : ℝ) :
    (SignedExpr.affine w b).Additive := by
  constructor
  · trivial
  · suffices ∀ es : List (SignedExpr (Fin n)), (∀ e∈es, e.Additive) → (SignedExpr.sum es).Additive by
      apply this
      intro e he
      simp only [List.mem_ofFn] at he
      rcases he with ⟨i,rfl⟩
      trivial
    intro es
    induction es with
    | nil => intro _; trivial
    | cons e es ih =>
        intro h
        exact ⟨h e (by simp),ih (fun a ha => h a (by simp [ha]))⟩

end HiddenMonotonicity
