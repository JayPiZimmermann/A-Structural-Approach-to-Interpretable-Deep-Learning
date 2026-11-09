import Thesis.StoppingDAGIntermediate

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit Matrix
open scoped BigOperators

/-- The source's earliest maximizing operand. The strict comparison deliberately
keeps operand zero when the maximum is tied. -/
def earliestWinner : {k : ℕ} → (Fin (k+1) → ℝ) → Fin (k+1)
  | 0, _ => 0
  | k+1, v =>
      let t := earliestWinner (fun i : Fin (k+1) => v i.succ)
      if v 0<v t.succ then t.succ else 0

/-- Ordered nonempty finite pool, compiled into the existing binary expression.
Earlier source operands occupy RIGHT branches, matching the generic right-tie
rule while implementing the source's smallest-index maximizing rule. -/
def orderedPool {n} : {k : ℕ} → (Fin (k+1) → SignedExpr (Fin n)) → SignedExpr (Fin n)
  | 0, es => es 0
  | k+1, es => .maximum (orderedPool (fun i : Fin (k+1) => es i.succ)) (es 0)

theorem earliestWinner_maximal {k} (v : Fin (k+1) → ℝ) (i : Fin (k+1)) :
    v i ≤ v (earliestWinner v) := by
  induction k with
  | zero => have hi : i=0 := Fin.eq_zero i; subst i; exact le_rfl
  | succ k ih =>
      simp only [earliestWinner]
      split_ifs with h
      · refine Fin.cases ?_ (fun j => ?_) i
        · exact h.le
        · exact ih (fun j : Fin (k+1) => v j.succ) j
      · refine Fin.cases ?_ (fun j => ?_) i
        · exact le_rfl
        · exact (ih (fun j : Fin (k+1) => v j.succ) j).trans (le_of_not_gt h)

/-- The winner is the least original operand index among all maximizers. -/
theorem earliestWinner_le_of_eq {k} (v : Fin (k+1) → ℝ) (i : Fin (k+1))
    (hi : v i=v (earliestWinner v)) : earliestWinner v ≤ i := by
  induction k with
  | zero => exact Fin.zero_le _
  | succ k ih =>
      simp only [earliestWinner] at hi ⊢
      split_ifs at hi ⊢ with h
      · refine Fin.cases ?_ (fun j => ?_) i hi
        · intro he; exact False.elim ((ne_of_lt h) he)
        · intro he
          exact Fin.succ_le_succ_iff.mpr (ih (fun j : Fin (k+1) => v j.succ) j he)
      · exact Fin.zero_le _

theorem earliestWinner_spec {k} (v : Fin (k+1) → ℝ) :
    (∀ i,v i ≤ v (earliestWinner v)) ∧
    (∀ i,v i=v (earliestWinner v) → earliestWinner v ≤ i) :=
  ⟨earliestWinner_maximal v,earliestWinner_le_of_eq v⟩

theorem earliestWinner_eq_of_strict {k} (v : Fin (k+1) → ℝ) (winner : Fin (k+1))
    (hw : ∀ i,i≠winner → v i<v winner) : earliestWinner v=winner := by
  by_contra hne
  have h := hw (earliestWinner v) hne
  have hm := earliestWinner_maximal v winner
  linarith

theorem orderedPool_eval {n k} (es : Fin (k+1) → SignedExpr (Fin n)) (x : Vec n) :
    (orderedPool es).eval x=(es (earliestWinner (fun i => (es i).eval x))).eval x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [orderedPool,SignedExpr.eval,earliestWinner]
      rw [ih]
      split_ifs with h
      · exact max_eq_left h.le
      · exact max_eq_right (le_of_not_gt h)

theorem orderedPool_score {n k} (es : Fin (k+1) → SignedExpr (Fin n)) (x : PairVec n) :
    score (orderedPool es) x=score (es (earliestWinner (fun i => score (es i) x))) x :=
  orderedPool_eval es (x.1-x.2)

theorem orderedPool_stopping {n k} (es : Fin (k+1) → SignedExpr (Fin n)) (x : PairVec n) :
    stoppingExpr (orderedPool es) x=
      stoppingExpr (es (earliestWinner (fun i => score (es i) x))) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [orderedPool,stoppingExpr_maximum,orderedPool_score,earliestWinner]
      split_ifs with h
      · exact ih (fun i : Fin (k+1) => es i.succ)
      · rfl

theorem orderedPool_kernel {n k} (es : Fin (k+1) → SignedExpr (Fin n)) (x : PairVec n) :
    expressionKernel (orderedPool es) x=
      expressionKernel (es (earliestWinner (fun i => score (es i) x))) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [orderedPool,expressionKernel,orderedPool_score,earliestWinner]
      split_ifs with h
      · exact ih (fun i : Fin (k+1) => es i.succ)
      · rfl

theorem orderedPool_additive {n k} (es : Fin (k+1) → SignedExpr (Fin n))
    (he : ∀ i,(es i).Additive) : (orderedPool es).Additive := by
  induction k with
  | zero => exact he 0
  | succ k ih => exact ⟨ih (fun i => es i.succ) (fun i => he i.succ),he 0⟩

/-- A unique pool maximum requires regularity only of the winning operand;
maxima tied strictly below it impose no extra nested-tail condition. -/
theorem orderedPool_regular {n k} (es : Fin (k+1) → SignedExpr (Fin n))
    (x : PairVec n) (winner : Fin (k+1))
    (hw : ∀ i,i≠winner → score (es i) x<score (es winner) x)
    (hr : ExpressionRegular (es winner) x) : ExpressionRegular (orderedPool es) x := by
  induction k with
  | zero => have he : winner=0 := Fin.eq_zero winner; subst winner; exact hr
  | succ k ih =>
      refine Fin.cases ?_ (fun w => ?_) winner hw hr
      · intro hwin hreg
        have hlt := hwin (earliestWinner (fun i : Fin (k+1) => score (es i.succ) x)).succ
          (Fin.succ_ne_zero _)
        simp only [orderedPool,ExpressionRegular,orderedPool_score]
        refine ⟨ne_of_lt hlt,?_⟩
        rw [if_neg (not_lt_of_ge hlt.le)]
        exact hreg
      · intro hwin hreg
        have ht : ∀ i : Fin (k+1),i≠w → score (es i.succ) x<score (es w.succ) x := by
          intro i hi
          exact hwin i.succ (by simpa using hi)
        have he := earliestWinner_eq_of_strict (fun i : Fin (k+1) => score (es i.succ) x) w ht
        have hlt := hwin 0 (Ne.symm (Fin.succ_ne_zero w))
        simp only [orderedPool,ExpressionRegular,orderedPool_score,he]
        refine ⟨ne_of_gt hlt,?_⟩
        rw [if_pos hlt]
        exact ih (fun i : Fin (k+1) => es i.succ) w ht hreg

def orderedInputPool {n k} (inputs : Fin (k+1) → Fin n) : SignedExpr (Fin n) :=
  orderedPool (fun i => .input (inputs i))

theorem orderedInputPool_regular {n k} (inputs : Fin (k+1) → Fin n)
    (x : PairVec n) (winner : Fin (k+1))
    (hw : ∀ i,i≠winner → x.1 (inputs i)-x.2 (inputs i)<x.1 (inputs winner)-x.2 (inputs winner)) :
    ExpressionRegular (orderedInputPool inputs) x := by
  apply orderedPool_regular (fun i => .input (inputs i)) x winner hw
  trivial

/-- Source finite maxpool at ties: exact propagated pair, exact selected kernel,
and proof that the selected operand is the smallest original maximizing index. -/
theorem orderedInputPool_source {n k} (inputs : Fin (k+1) → Fin n) (x : PairVec n) :
    let values := fun i => x.1 (inputs i)-x.2 (inputs i)
    let winner := earliestWinner values
    (∀ i,values i ≤ values winner) ∧
    (∀ i,values i=values winner → winner ≤ i) ∧
    stoppingExpr (orderedInputPool inputs) x=(x.1 (inputs winner),x.2 (inputs winner)) ∧
    expressionKernel (orderedInputPool inputs) x=(Pi.single (inputs winner) 1,0) := by
  dsimp only
  refine ⟨(earliestWinner_spec _).1,(earliestWinner_spec _).2,?_,?_⟩
  · rw [orderedInputPool,orderedPool_stopping]
    rfl
  · rw [orderedInputPool,orderedPool_kernel]
    rfl

/-- For the source's sorted predecessor enumeration, the winner is also the
smallest graph-node index among all maximizing predecessors. -/
theorem orderedInputPool_minimum_graph_index {n k} (inputs : Fin (k+1) → Fin n)
    (horder : Monotone inputs) (x : PairVec n) :
    let values := fun i => x.1 (inputs i)-x.2 (inputs i)
    let winner := earliestWinner values
    ∀ i,values i=values winner → inputs winner ≤ inputs i := by
  intro values winner i hi
  exact horder (earliestWinner_le_of_eq values i hi)

/-- The source-ordered pool's global selected Jacobian forwards exactly the
smallest maximizing predecessor row of the actual shared graph. -/
theorem orderedInputPool_dag_row {d n k} (prior : Circuit d n)
    (inputs : Fin (k+1) → Fin n) (x : PairVec d) :
    let s := stoppingCircuit prior x
    let winner := earliestWinner (fun i => s.1 (inputs i)-s.2 (inputs i))
    (dagKernel (.node prior (orderedInputPool inputs)) x).1 (Fin.last n)=
      (dagKernel prior x).1 (inputs winner) ∧
    (dagKernel (.node prior (orderedInputPool inputs)) x).2 (Fin.last n)=
      (dagKernel prior x).2 (inputs winner) := by
  dsimp only
  have hk := (orderedInputPool_source inputs (stoppingCircuit prior x)).2.2.2
  simp [dagKernel,hk,combineKernel,Fin.snoc,Matrix.single_one_vecMul,Matrix.row]

end Thesis.StoppingDAG
