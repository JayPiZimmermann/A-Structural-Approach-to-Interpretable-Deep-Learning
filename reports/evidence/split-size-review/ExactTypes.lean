import HiddenMonotonicity.SplitDAGSize
import HiddenMonotonicity.MaxoutProductSize
set_option pp.universes true
set_option pp.explicit true
set_option autoImplicit false
section
open HiddenMonotonicity Finset Matrix
example : (∀ {d n : ℕ} (c : Circuit d n) (x : Fin d × Bool → ℝ), c.compileSplitDAG.eval x=c.split false x) := @HiddenMonotonicity.Circuit.compileSplitDAG_eval
#check @HiddenMonotonicity.Circuit.compileSplitDAG_eval
#print axioms HiddenMonotonicity.Circuit.compileSplitDAG_eval
end
section
open HiddenMonotonicity Finset Matrix
example : (∀ {d n : ℕ} (c : Circuit d n) (D : ℕ) (hc : c.BoundedDuplication D), c.compileSplitDAG.graphSize≤24*2^D*c.syntaxSize ∧ (∀ x : Fin d × Bool → ℝ,   (c.compileSplitDAG.eval x).1-(c.compileSplitDAG.eval x).2=     c.eval (fun i => x (i,false)-x (i,true))) ∧ (∀ x : Fin d × Bool → ℝ, 0≤x → 0≤c.compileSplitDAG.eval x) ∧ (∀ x y : Fin d × Bool → ℝ, 0≤x → 0≤y → x≤y →   c.compileSplitDAG.eval x≤c.compileSplitDAG.eval y)) := @HiddenMonotonicity.Circuit.split_DAG_with_size
#check @HiddenMonotonicity.Circuit.split_DAG_with_size
#print axioms HiddenMonotonicity.Circuit.split_DAG_with_size
end
section
open HiddenMonotonicity Finset Matrix
example : (∀ {n : ℕ} (g : MaxoutProductGate n) (x : Vec n), g.toExpr.eval x=g.eval x) := @HiddenMonotonicity.MaxoutProductGate.toExpr_eval
#check @HiddenMonotonicity.MaxoutProductGate.toExpr_eval
#print axioms HiddenMonotonicity.MaxoutProductGate.toExpr_eval
end
section
open HiddenMonotonicity Finset Matrix
example : (∀ {d n : ℕ} (c : MaxoutProductDAG d n) (x : Vec d), c.toCircuit.eval x=c.eval x) := @HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval
#check @HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval
#print axioms HiddenMonotonicity.MaxoutProductDAG.toCircuit_eval
end
section
open HiddenMonotonicity Finset Matrix
example : (∀ {d n : ℕ} (c : MaxoutProductDAG d n) (x : Vec d), c.eval x=(c.compile.eval (canonicalSplitInput x)).1- (c.compile.eval (canonicalSplitInput x)).2) := @HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery
#check @HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery
#print axioms HiddenMonotonicity.MaxoutProductDAG.compile_canonical_recovery
end
section
open HiddenMonotonicity Finset Matrix
example : (∀ {d n : ℕ} (c : MaxoutProductDAG d n) (K D : ℕ) (hc : c.BoundedRankDegree K D), ∃ g : SplitDAG d n, g.maxoutRank≤2 ∧ g.graphSize≤(24*2^(max K D)*(4*K+2*D+1))*c.graphSize ∧ (∀ x : Fin d × Bool → ℝ, (g.eval x).1-(g.eval x).2=   c.eval (fun i => x (i,false)-x (i,true))) ∧ (∀ x : Fin d × Bool → ℝ, 0≤x → 0≤g.eval x) ∧ (∀ x y : Fin d × Bool → ℝ, 0≤x → 0≤y → x≤y → g.eval x≤g.eval y) ∧ (∀ i : Fin n, ∃ P Q : MaxPolynomial (Fin d × Bool),   ∀ x : Fin d × Bool → ℝ, 0≤x → (g.eval x).1 i=P.eval x ∧ (g.eval x).2 i=Q.eval x)) := @HiddenMonotonicity.MaxoutProductDAG.split_linear_size
#check @HiddenMonotonicity.MaxoutProductDAG.split_linear_size
#print axioms HiddenMonotonicity.MaxoutProductDAG.split_linear_size
end
section
open HiddenMonotonicity Finset Matrix
example : (∀ {n : ℕ} (g : MaxoutProductGate n), g.totalDegree≤g.expandedTerms) := @HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms
#check @HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms
#print axioms HiddenMonotonicity.MaxoutProductGate.degree_le_expandedTerms
end
section
open HiddenMonotonicity Finset Matrix
example : (∀ {d n : ℕ} (c : MaxoutProductDAG d n) (K B : ℕ) (hc : c.BoundedRankExpansion K B), ∃ g : SplitDAG d n, g.maxoutRank≤2 ∧ g.graphSize≤(24*2^(max K B)*(4*K+2*B+1))*c.graphSize ∧ (∀ x : Fin d × Bool → ℝ, (g.eval x).1-(g.eval x).2=   c.eval (fun i => x (i,false)-x (i,true))) ∧ (∀ x : Fin d × Bool → ℝ, 0≤x → 0≤g.eval x) ∧ (∀ x y : Fin d × Bool → ℝ, 0≤x → 0≤y → x≤y → g.eval x≤g.eval y) ∧ (∀ i : Fin n, ∃ P Q : MaxPolynomial (Fin d × Bool),   ∀ x : Fin d × Bool → ℝ, 0≤x → (g.eval x).1 i=P.eval x ∧ (g.eval x).2 i=Q.eval x)) := @HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion
#check @HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion
#print axioms HiddenMonotonicity.MaxoutProductDAG.split_linear_size_expansion
end
