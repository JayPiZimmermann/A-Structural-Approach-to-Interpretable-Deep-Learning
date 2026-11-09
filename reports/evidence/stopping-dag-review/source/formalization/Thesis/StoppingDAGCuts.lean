import Thesis.StoppingDAGPrimitives

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Matrix
open scoped BigOperators

/-- Reattach an existing shared pre to a downstream circuit. Downstream
expressions keep their original node indices; shared predecessors are neither
copied nor replaced by independent networks. -/
def graft {d m n} (pre : Circuit d m) : Circuit m n → Circuit d n
  | .inputs => pre
  | .node prior op => .node (graft pre prior) op

theorem graft_eval {d m n} (pre : Circuit d m) (suffix : Circuit m n) (x : Vec d) :
    (graft pre suffix).eval x=suffix.eval (pre.eval x) := by
  induction suffix with
  | inputs => rfl
  | node prior op ih => simp only [graft,Circuit.eval,ih]

theorem graft_stopping {d m n} (pre : Circuit d m) (suffix : Circuit m n) (x : PairVec d) :
    stoppingCircuit (graft pre suffix) x=stoppingCircuit suffix (stoppingCircuit pre x) := by
  induction suffix with
  | inputs => rfl
  | node prior op ih => simp only [graft,stoppingCircuit,ih]

theorem graft_additive {d m n} (pre : Circuit d m) (suffix : Circuit m n) :
    (graft pre suffix).Additive ↔ pre.Additive ∧ suffix.Additive := by
  induction suffix with
  | inputs => simp [graft,Circuit.Additive]
  | node prior op ih => simp [graft,Circuit.Additive,ih,and_assoc]

theorem graft_regular {d m n} (pre : Circuit d m) (suffix : Circuit m n) (x : PairVec d) :
    CircuitRegular (graft pre suffix) x ↔
      CircuitRegular pre x ∧ CircuitRegular suffix (stoppingCircuit pre x) := by
  induction suffix with
  | inputs => simp [graft,CircuitRegular]
  | node prior op ih => simp [graft,CircuitRegular,ih,graft_stopping,and_assoc]

/-- Source p/q/k identity at an actual graph cut. The downstream state is the
shared pre's actual forward state. A chosen intermediate node can be made
the last pre node; terminating at this cut then records precisely its visit. -/
theorem cut_stopping_derivative_occupation {d m n}
    (pre : Circuit d m) (suffix : Circuit m n) (hc : (graft pre suffix).Additive)
    (x : PairVec d) (hx : CircuitRegular (graft pre suffix) x)
    (j : Fin n) (p q : Bool) (i : Fin m) (k : Bool) :
    (if Bool.xor p q then
        (fderiv ℝ (stoppingCircuit suffix) (stoppingCircuit pre x) (splitBasis i k)).2 j
      else (fderiv ℝ (stoppingCircuit suffix) (stoppingCircuit pre x) (splitBasis i k)).1 j) =
      occupation suffix (stoppingCircuit pre x) j q i (Bool.xor p k) := by
  rw [stopping_derivative_occupation suffix ((graft_additive pre suffix).mp hc).2
    _ ((graft_regular pre suffix x).mp hx).2]
  rw [occupation_eq_kernel suffix ((graft_additive pre suffix).mp hc).2,
      occupation_eq_kernel suffix ((graft_additive pre suffix).mp hc).2]
  cases p <;> cases q <;> cases k <;> rfl

/-- Arbitrary starting sign form of the source's ordinary activation identity. -/
theorem circuit_derivative_occupation_signed {d n} (c : Circuit d n) (hc : c.Additive)
    (x : Vec d) (hx : CircuitRegular c (x,0)) (j : Fin n) (i : Fin d) (q : Bool) :
    (fderiv ℝ c.eval x (Pi.single i 1)) j =
      (if q then (-1 : ℝ) else 1)*
        (occupation c (x,0) j q i false-occupation c (x,0) j q i true) := by
  rw [circuit_derivative_occupation c hc x hx]
  simp only [occupation_eq_kernel c hc]
  cases q <;> simp <;> ring

end Thesis.StoppingDAG
