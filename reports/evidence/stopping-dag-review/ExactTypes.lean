import Thesis.StoppingExpressionKernel
import Thesis.StoppingDAGDerivative
import Thesis.StoppingDAGPaths
import Thesis.StoppingDAGOccupation
import Thesis.StoppingDAGBackward
import Thesis.StoppingDAGPayoff
import Thesis.StoppingDAGPrimitives
import Thesis.StoppingDAGCuts
import Thesis.StoppingDAGVisits
import Thesis.StoppingDAGIntermediate
set_option pp.universes true
set_option pp.explicit true
set_option autoImplicit false
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (e : SignedExpr (Fin n)) (he : e.Additive) (x : PairVec n) (hx : ExpressionRegular e x), HasFDerivAt (stoppingExpr e) (kernelMap (expressionKernel e x)) x) := @Thesis.StoppingDAG.stoppingExpr_hasFDerivAt
#check @Thesis.StoppingDAG.stoppingExpr_hasFDerivAt
#print axioms Thesis.StoppingDAG.stoppingExpr_hasFDerivAt
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (hx : CircuitRegular c x), HasFDerivAt (stoppingCircuit c) (pairMap (dagKernel c x).1 (dagKernel c x).2) x) := @Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt
#check @Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt
#print axioms Thesis.StoppingDAG.stoppingCircuit_hasFDerivAt
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (path : DAGPaths c), 0≤pathProbability c x j path) := @Thesis.StoppingDAG.pathProbability_nonnegative
#check @Thesis.StoppingDAG.pathProbability_nonnegative
#print axioms Thesis.StoppingDAG.pathProbability_nonnegative
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (x : PairVec d) (j : Fin n), (∑ path : DAGPaths c,pathProbability c x j path)=1) := @Thesis.StoppingDAG.pathProbability_normalized
#check @Thesis.StoppingDAG.pathProbability_normalized
#print axioms Thesis.StoppingDAG.pathProbability_normalized
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (path : DAGPaths c), 0≤pathDiscount c x j path) := @Thesis.StoppingDAG.pathDiscount_nonnegative
#check @Thesis.StoppingDAG.pathDiscount_nonnegative
#print axioms Thesis.StoppingDAG.pathDiscount_nonnegative
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool), occupation c x j turn i channel = if Bool.xor channel turn then (dagKernel c x).2 j i else (dagKernel c x).1 j i) := @Thesis.StoppingDAG.occupation_eq_kernel
#check @Thesis.StoppingDAG.occupation_eq_kernel
#print axioms Thesis.StoppingDAG.occupation_eq_kernel
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool), (if turn then (pairMap (dagKernel c x).1 (dagKernel c x).2 (splitBasis i channel)).2 j else (pairMap (dagKernel c x).1 (dagKernel c x).2 (splitBasis i channel)).1 j) = occupation c x j turn i channel) := @Thesis.StoppingDAG.selected_operator_occupation
#check @Thesis.StoppingDAG.selected_operator_occupation
#print axioms Thesis.StoppingDAG.selected_operator_occupation
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (hx : CircuitRegular c x) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool), (if turn then (fderiv ℝ (stoppingCircuit c) x (splitBasis i channel)).2 j else (fderiv ℝ (stoppingCircuit c) x (splitBasis i channel)).1 j) = occupation c x j turn i channel) := @Thesis.StoppingDAG.stopping_derivative_occupation
#check @Thesis.StoppingDAG.stopping_derivative_occupation
#print axioms Thesis.StoppingDAG.stopping_derivative_occupation
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : Vec d) (hx : CircuitRegular c (x,0)), HasFDerivAt c.eval (matrixCLM ((dagKernel c (x,0)).1-(dagKernel c (x,0)).2)) x) := @Thesis.StoppingDAG.circuit_hasFDerivAt
#check @Thesis.StoppingDAG.circuit_hasFDerivAt
#print axioms Thesis.StoppingDAG.circuit_hasFDerivAt
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (e : SignedExpr (Fin n)) (he : e.Additive) (x : PairVec n), stoppingExpr e x=kernelMap (expressionKernel e x) x+expressionOffset e x) := @Thesis.StoppingDAG.stoppingExpr_affine
#check @Thesis.StoppingDAG.stoppingExpr_affine
#print axioms Thesis.StoppingDAG.stoppingExpr_affine
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (turn : Bool), expectedPayoff c x j turn=streamValue (stoppingCircuit c x) j turn) := @Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit
#check @Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit
#print axioms Thesis.StoppingDAG.expectedPayoff_eq_stoppingCircuit
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (w : Vec n) (b : ℝ) (x : PairVec n), expressionKernel (SignedExpr.affine w b) x=(fun i => max (w i) 0,fun i => max (-w i) 0)) := @Thesis.StoppingDAG.expressionKernel_affine
#check @Thesis.StoppingDAG.expressionKernel_affine
#print axioms Thesis.StoppingDAG.expressionKernel_affine
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (w : Vec n) (b : ℝ) (x : PairVec n), expressionOffset (SignedExpr.affine w b) x=(max b 0,max (-b) 0)) := @Thesis.StoppingDAG.expressionOffset_affine
#check @Thesis.StoppingDAG.expressionOffset_affine
#print axioms Thesis.StoppingDAG.expressionOffset_affine
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (w : Vec n) (b : ℝ) (x : PairVec n), localDiscount (expressionKernel (SignedExpr.affine w b) x)=∑ i,|w i|) := @Thesis.StoppingDAG.affine_discount
#check @Thesis.StoppingDAG.affine_discount
#print axioms Thesis.StoppingDAG.affine_discount
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (b : ℝ) (x : PairVec n), localDiscount (expressionKernel (.constant b) x)=0 ∧ localProbability (expressionKernel (.constant b) x) none=1 ∧ expressionOffset (.constant b) x=(max b 0,max (-b) 0)) := @Thesis.StoppingDAG.constant_cemetery
#check @Thesis.StoppingDAG.constant_cemetery
#print axioms Thesis.StoppingDAG.constant_cemetery
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (i j : Fin n) (x : PairVec n), localDiscount (expressionKernel (.add (.input i) (.input j)) x)=2) := @Thesis.StoppingDAG.addition_discount
#check @Thesis.StoppingDAG.addition_discount
#print axioms Thesis.StoppingDAG.addition_discount
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (i j k : Fin n) (x : PairVec n), localProbability (expressionKernel (.add (.input i) (.input j)) x) (some (k,false)) = additionProbability false*(if k=i then 1 else 0)+additionProbability true*(if k=j then 1 else 0)) := @Thesis.StoppingDAG.addition_probability
#check @Thesis.StoppingDAG.addition_probability
#print axioms Thesis.StoppingDAG.addition_probability
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (i j : Fin n) (x : PairVec n), expressionKernel (.maximum (.input i) (.input j)) x = (Pi.single (if x.1 j-x.2 j<x.1 i-x.2 i then i else j) 1,0)) := @Thesis.StoppingDAG.pool_kernel
#check @Thesis.StoppingDAG.pool_kernel
#print axioms Thesis.StoppingDAG.pool_kernel
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (i j : Fin n) (x : PairVec n), localDiscount (expressionKernel (.maximum (.input i) (.input j)) x)=1) := @Thesis.StoppingDAG.pool_discount
#check @Thesis.StoppingDAG.pool_discount
#print axioms Thesis.StoppingDAG.pool_discount
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {n : ℕ} (i : Fin n) (x : PairVec n), expressionKernel (.maximum (.input i) (.constant 0)) x = if x.2 i<x.1 i then (Pi.single i 1,0) else (0,0)) := @Thesis.StoppingDAG.relu_kernel
#check @Thesis.StoppingDAG.relu_kernel
#print axioms Thesis.StoppingDAG.relu_kernel
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d m n : ℕ} (pre : Circuit d m) (suffix : Circuit m n) (x : PairVec d), stoppingCircuit (graft pre suffix) x=stoppingCircuit suffix (stoppingCircuit pre x)) := @Thesis.StoppingDAG.graft_stopping
#check @Thesis.StoppingDAG.graft_stopping
#print axioms Thesis.StoppingDAG.graft_stopping
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n) (hc : (graft pre suffix).Additive) (x : PairVec d) (j : Fin n) (turn channel : Bool), fullOccupation (graft pre suffix) x j turn m channel = occupation suffix (stoppingCircuit pre x) j turn (Fin.last m) channel) := @Thesis.StoppingDAG.fullOccupation_graft_last
#check @Thesis.StoppingDAG.fullOccupation_graft_last
#print axioms Thesis.StoppingDAG.fullOccupation_graft_last
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (s : PairVec d) (hs : CircuitRegular c s), HasFDerivAt c.eval (matrixCLM ((dagKernel c s).1-(dagKernel c s).2)) (s.1-s.2)) := @Thesis.StoppingDAG.circuit_hasFDerivAt_split
#check @Thesis.StoppingDAG.circuit_hasFDerivAt_split
#print axioms Thesis.StoppingDAG.circuit_hasFDerivAt_split
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (target : ℕ) (hd : d≤target) (hn : target<n), ∃ pre : Circuit d (target+1),∃ suffix : Circuit (target+1) n,c=graft pre suffix) := @Thesis.StoppingDAG.exists_graph_cut
#check @Thesis.StoppingDAG.exists_graph_cut
#print axioms Thesis.StoppingDAG.exists_graph_cut
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d n : ℕ} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool), fullOccupation c x j turn i.val channel=occupation c x j turn i channel) := @Thesis.StoppingDAG.fullOccupation_input
#check @Thesis.StoppingDAG.fullOccupation_input
#print axioms Thesis.StoppingDAG.fullOccupation_input
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n) (hc : (graft pre suffix).Additive) (x : PairVec d) (hx : CircuitRegular (graft pre suffix) x) (j : Fin n) (p q k : Bool), (if Bool.xor p q then (fderiv ℝ (stoppingCircuit suffix) (stoppingCircuit pre x) (splitBasis (Fin.last m) k)).2 j else (fderiv ℝ (stoppingCircuit suffix) (stoppingCircuit pre x) (splitBasis (Fin.last m) k)).1 j) = fullOccupation (graft pre suffix) x j q m (Bool.xor p k)) := @Thesis.StoppingDAG.intermediate_stopping_derivative_occupation
#check @Thesis.StoppingDAG.intermediate_stopping_derivative_occupation
#print axioms Thesis.StoppingDAG.intermediate_stopping_derivative_occupation
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n) (hc : (graft pre suffix).Additive) (x : PairVec d) (hx : CircuitRegular (graft pre suffix) x) (j : Fin n) (q : Bool), (fderiv ℝ suffix.eval (pre.eval (x.1-x.2)) (Pi.single (Fin.last m) 1)) j = (if q then (-1 : ℝ) else 1)*(fullOccupation (graft pre suffix) x j q m false-fullOccupation (graft pre suffix) x j q m true)) := @Thesis.StoppingDAG.intermediate_circuit_derivative_occupation
#check @Thesis.StoppingDAG.intermediate_circuit_derivative_occupation
#print axioms Thesis.StoppingDAG.intermediate_circuit_derivative_occupation
end
section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG Matrix
open scoped BigOperators
example : (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n) (hc : (graft pre suffix).Additive) (x : PairVec d) (j : Fin n) (p q k : Bool), (if Bool.xor p q then (pairMap (dagKernel suffix (stoppingCircuit pre x)).1 (dagKernel suffix (stoppingCircuit pre x)).2 (splitBasis (Fin.last m) k)).2 j else (pairMap (dagKernel suffix (stoppingCircuit pre x)).1 (dagKernel suffix (stoppingCircuit pre x)).2 (splitBasis (Fin.last m) k)).1 j) = fullOccupation (graft pre suffix) x j q m (Bool.xor p k)) := @Thesis.StoppingDAG.intermediate_selected_occupation
#check @Thesis.StoppingDAG.intermediate_selected_occupation
#print axioms Thesis.StoppingDAG.intermediate_selected_occupation
end
