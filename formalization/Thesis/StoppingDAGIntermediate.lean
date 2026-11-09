import Thesis.StoppingDAGVisits

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Matrix
open scoped BigOperators

/-- A split state need not be the canonical (a,0) lift. Keeping its negative
stream fixed gives a local affine lift of its represented ordinary activation. -/
theorem circuit_hasFDerivAt_split {d n} (c : Circuit d n) (hc : c.Additive)
    (s : PairVec d) (hs : CircuitRegular c s) :
    HasFDerivAt c.eval (matrixCLM ((dagKernel c s).1-(dagKernel c s).2)) (s.1-s.2) := by
  have hl : HasFDerivAt (fun y : Vec d => (y+s.2,s.2)) (liftCLM d) (s.1-s.2) :=
    ((hasFDerivAt_id (s.1-s.2)).add_const s.2).prodMk (hasFDerivAt_const s.2 (s.1-s.2))
  have hd : HasFDerivAt (stoppingCircuit c) (pairMap (dagKernel c s).1 (dagKernel c s).2)
      ((s.1-s.2)+s.2,s.2) := by
    simpa only [sub_add_cancel,Prod.mk.eta] using stoppingCircuit_hasFDerivAt c hc s hs
  have hr := (differenceCLM n).hasFDerivAt.comp (s.1-s.2) (hd.comp (s.1-s.2) hl)
  have he : (differenceCLM n) ∘ (stoppingCircuit c ∘ (fun y : Vec d => (y+s.2,s.2)))=c.eval := by
    funext y
    change (stoppingCircuit c (y+s.2,s.2)).1-(stoppingCircuit c (y+s.2,s.2)).2=c.eval y
    simpa only [add_sub_cancel_right] using stoppingCircuit_recovery c (y+s.2,s.2)
  rw [he] at hr
  rw [← ContinuousLinearMap.comp_assoc,difference_pairMap,ContinuousLinearMap.comp_assoc,
    difference_lift,ContinuousLinearMap.comp_id] at hr
  exact hr

theorem circuit_derivative_occupation_split {d n} (c : Circuit d n) (hc : c.Additive)
    (s : PairVec d) (hs : CircuitRegular c s) (j : Fin n) (i : Fin d) (q : Bool) :
    (fderiv ℝ c.eval (s.1-s.2) (Pi.single i 1)) j =
      (if q then (-1 : ℝ) else 1)*
        (occupation c s j q i false-occupation c s j q i true) := by
  rw [(circuit_hasFDerivAt_split c hc s hs).fderiv]
  change (((dagKernel c s).1-(dagKernel c s).2) *ᵥ (Pi.single i 1)) j=_
  cases q <;> simp [occupation_eq_kernel c hc]

/-- Every recorded internal node has an actual shared prefix/suffix cut. -/
theorem exists_graph_cut {d n} (c : Circuit d n) (target : ℕ)
    (hd : d≤target) (hn : target<n) :
    ∃ pre : Circuit d (target+1),∃ suffix : Circuit (target+1) n,c=graft pre suffix := by
  induction c with
  | inputs => omega
  | @node n prior op ih =>
      by_cases he : target=n
      · subst target
        exact ⟨.node prior op,.inputs,rfl⟩
      · obtain ⟨pre,suffix,hs⟩ := ih (by omega)
        refine ⟨pre,.node suffix op,?_⟩
        change Circuit.node prior op=Circuit.node (graft pre suffix) op
        rw [hs]

theorem fullOccupation_input {d n} (c : Circuit d n) (hc : c.Additive)
    (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool) :
    fullOccupation c x j turn i.val channel=occupation c x j turn i channel := by
  induction c generalizing turn with
  | inputs =>
      cases turn <;> cases channel <;>
        simp [fullOccupation,DAGPaths,pathProbability,visitWeight,visitIndicator,
          occupation_eq_kernel Circuit.inputs hc,dagKernel,Matrix.one_apply,Fin.ext_iff]
  | @node n prior op ih =>
      refine Fin.lastCases ?_ (fun h => ?_) j
      · rw [fullOccupation_node,occupation_node prior op hc]
        have hn : n≠i.val := by have h := circuit_width_le prior; omega
        simp only [visitIndicator,hn,false_and,ite_false,zero_add]
        simp_rw [ih hc.1]
      · rw [fullOccupation_old,occupation_old prior op hc]
        exact ih hc.1 h turn

/-- At ties the source formula still describes the selected operator and full
trajectory occupation, without asserting classical stream differentiability. -/
theorem intermediate_selected_occupation {d m n}
    (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n)
    (hc : (graft pre suffix).Additive) (x : PairVec d)
    (j : Fin n) (p q k : Bool) :
    (if Bool.xor p q then
        (pairMap (dagKernel suffix (stoppingCircuit pre x)).1
          (dagKernel suffix (stoppingCircuit pre x)).2 (splitBasis (Fin.last m) k)).2 j
      else (pairMap (dagKernel suffix (stoppingCircuit pre x)).1
          (dagKernel suffix (stoppingCircuit pre x)).2 (splitBasis (Fin.last m) k)).1 j) =
      fullOccupation (graft pre suffix) x j q m (Bool.xor p k) := by
  have hs := ((graft_additive pre suffix).mp hc).2
  rw [selected_operator_occupation suffix hs,fullOccupation_graft_last pre suffix hc]
  rw [occupation_eq_kernel suffix hs,occupation_eq_kernel suffix hs]
  cases p <;> cases q <;> cases k <;> rfl

/-- Source p/q/k stopping derivative identity for every intermediate node,
using the original full graph's discounted visits (not a terminal-only law).
The actual shared prefix ends at the target; suffix evaluation is precisely the
original graph after an independent perturbation of this node's activation. -/
theorem intermediate_stopping_derivative_occupation {d m n}
    (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n)
    (hc : (graft pre suffix).Additive) (x : PairVec d)
    (hx : CircuitRegular (graft pre suffix) x) (j : Fin n) (p q k : Bool) :
    (if Bool.xor p q then
        (fderiv ℝ (stoppingCircuit suffix) (stoppingCircuit pre x) (splitBasis (Fin.last m) k)).2 j
      else (fderiv ℝ (stoppingCircuit suffix) (stoppingCircuit pre x) (splitBasis (Fin.last m) k)).1 j) =
      fullOccupation (graft pre suffix) x j q m (Bool.xor p k) := by
  rw [cut_stopping_derivative_occupation pre suffix hc x hx,
    fullOccupation_graft_last pre suffix hc]

/-- Source ordinary-activation identity at every intermediate shared-DAG node.
The scalar derivative is evaluated at the prefix's original activation vector,
and the right side is the original graph's full discounted visit occupation. -/
theorem intermediate_circuit_derivative_occupation {d m n}
    (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n)
    (hc : (graft pre suffix).Additive) (x : PairVec d)
    (hx : CircuitRegular (graft pre suffix) x) (j : Fin n) (q : Bool) :
    (fderiv ℝ suffix.eval (pre.eval (x.1-x.2)) (Pi.single (Fin.last m) 1)) j =
      (if q then (-1 : ℝ) else 1)*
        (fullOccupation (graft pre suffix) x j q m false-
          fullOccupation (graft pre suffix) x j q m true) := by
  rw [fullOccupation_graft_last pre suffix hc,fullOccupation_graft_last pre suffix hc]
  rw [← stoppingCircuit_recovery pre x]
  exact circuit_derivative_occupation_split suffix ((graft_additive pre suffix).mp hc).2
    _ ((graft_regular pre suffix x).mp hx).2 j (Fin.last m) q

end Thesis.StoppingDAG
