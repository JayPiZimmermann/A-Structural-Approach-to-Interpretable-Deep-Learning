import Thesis.StoppingOrderedPool
set_option pp.universes true
set_option pp.explicit true
set_option autoImplicit false
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
example : (∀ {k : ℕ} (v : Fin (k+1) → ℝ), (∀ i,v i ≤ v (earliestWinner v)) ∧ (∀ i,v i=v (earliestWinner v) → earliestWinner v ≤ i)) := @Thesis.StoppingDAG.earliestWinner_spec
#check @Thesis.StoppingDAG.earliestWinner_spec
#print axioms Thesis.StoppingDAG.earliestWinner_spec
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
example : (∀ {n k : ℕ} (inputs : Fin (k+1) → Fin n) (x : PairVec n), let values := fun i => x.1 (inputs i)-x.2 (inputs i); let winner := earliestWinner values; (∀ i,values i ≤ values winner) ∧ (∀ i,values i=values winner → winner ≤ i) ∧ stoppingExpr (orderedInputPool inputs) x=(x.1 (inputs winner),x.2 (inputs winner)) ∧ expressionKernel (orderedInputPool inputs) x=(Pi.single (inputs winner) 1,0)) := @Thesis.StoppingDAG.orderedInputPool_source
#check @Thesis.StoppingDAG.orderedInputPool_source
#print axioms Thesis.StoppingDAG.orderedInputPool_source
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
example : (∀ {n k : ℕ} (inputs : Fin (k+1) → Fin n) (horder : Monotone inputs) (x : PairVec n), let values := fun i => x.1 (inputs i)-x.2 (inputs i); let winner := earliestWinner values; ∀ i,values i=values winner → inputs winner ≤ inputs i) := @Thesis.StoppingDAG.orderedInputPool_minimum_graph_index
#check @Thesis.StoppingDAG.orderedInputPool_minimum_graph_index
#print axioms Thesis.StoppingDAG.orderedInputPool_minimum_graph_index
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
example : (∀ {d n k : ℕ} (prior : Circuit d n) (inputs : Fin (k+1) → Fin n) (x : PairVec d), let s := stoppingCircuit prior x; let winner := earliestWinner (fun i => s.1 (inputs i)-s.2 (inputs i)); (dagKernel (.node prior (orderedInputPool inputs)) x).1 (Fin.last n)=(dagKernel prior x).1 (inputs winner) ∧ (dagKernel (.node prior (orderedInputPool inputs)) x).2 (Fin.last n)=(dagKernel prior x).2 (inputs winner)) := @Thesis.StoppingDAG.orderedInputPool_dag_row
#check @Thesis.StoppingDAG.orderedInputPool_dag_row
#print axioms Thesis.StoppingDAG.orderedInputPool_dag_row
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
example : (∀ {n k : ℕ} (es : Fin (k+1) → SignedExpr (Fin n)) (x : PairVec n) (winner : Fin (k+1)) (hw : ∀ i,i≠winner → score (es i) x<score (es winner) x) (hr : ExpressionRegular (es winner) x), ExpressionRegular (orderedPool es) x) := @Thesis.StoppingDAG.orderedPool_regular
#check @Thesis.StoppingDAG.orderedPool_regular
#print axioms Thesis.StoppingDAG.orderedPool_regular
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators
example : (∀ {n k : ℕ} (inputs : Fin (k+1) → Fin n) (x : PairVec n) (winner : Fin (k+1)) (hw : ∀ i,i≠winner → x.1 (inputs i)-x.2 (inputs i)<x.1 (inputs winner)-x.2 (inputs winner)), ExpressionRegular (orderedInputPool inputs) x) := @Thesis.StoppingDAG.orderedInputPool_regular
#check @Thesis.StoppingDAG.orderedInputPool_regular
#print axioms Thesis.StoppingDAG.orderedInputPool_regular
end
