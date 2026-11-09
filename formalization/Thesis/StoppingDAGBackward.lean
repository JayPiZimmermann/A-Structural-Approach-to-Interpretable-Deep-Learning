import Thesis.StoppingDAGOccupation

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Matrix
open scoped BigOperators

def splitBasis {d} (i : Fin d) (channel : Bool) : PairVec d :=
  if channel then (0,Pi.single i 1) else (Pi.single i 1,0)

theorem pairMap_apply {d n} (P N : Matrix (Fin n) (Fin d) ℝ) (x : PairVec d) :
    pairMap P N x=(P *ᵥ x.1+N *ᵥ x.2,N *ᵥ x.1+P *ᵥ x.2) := rfl

theorem pairMap_basis {d n} (P N : Matrix (Fin n) (Fin d) ℝ)
    (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool) :
    (if turn then (pairMap P N (splitBasis i channel)).2 j
      else (pairMap P N (splitBasis i channel)).1 j) =
      if Bool.xor channel turn then N j i else P j i := by
  cases turn <;> cases channel <;> simp [splitBasis,pairMap_apply,Matrix.mulVec_single_one]

/-- The selected linear operator equals discounted occupation at every point,
including the deterministic right-winner convention at tied pools. -/
theorem selected_operator_occupation {d n} (c : Circuit d n) (hc : c.Additive)
    (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool) :
    (if turn then
        (pairMap (dagKernel c x).1 (dagKernel c x).2 (splitBasis i channel)).2 j
      else (pairMap (dagKernel c x).1 (dagKernel c x).2 (splitBasis i channel)).1 j) =
      occupation c x j turn i channel := by
  rw [pairMap_basis,occupation_eq_kernel c hc]

/-- Actual end-to-end stopping-stream Jacobian equals the normalized path law's
full discounted terminal occupation. Regularity is checked on original forward
node values; it is not an assumed derivative or occupation invariant. -/
theorem stopping_derivative_occupation {d n} (c : Circuit d n) (hc : c.Additive)
    (x : PairVec d) (hx : CircuitRegular c x)
    (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool) :
    (if turn then (fderiv ℝ (stoppingCircuit c) x (splitBasis i channel)).2 j
      else (fderiv ℝ (stoppingCircuit c) x (splitBasis i channel)).1 j) =
      occupation c x j turn i channel := by
  rw [(stoppingCircuit_hasFDerivAt c hc x hx).fderiv]
  exact selected_operator_occupation c hc x j turn i channel

theorem difference_pairMap {d n} (P N : Matrix (Fin n) (Fin d) ℝ) :
    (differenceCLM n).comp (pairMap P N) =
      (matrixCLM (P-N)).comp (differenceCLM d) := by
  apply ContinuousLinearMap.ext
  intro v
  change (P *ᵥ v.1+N *ᵥ v.2)-(N *ᵥ v.1+P *ᵥ v.2) = (P-N) *ᵥ (v.1-v.2)
  simp only [Matrix.sub_mulVec,Matrix.mulVec_sub]
  abel

theorem difference_lift {d} :
    (differenceCLM d).comp (liftCLM d)=ContinuousLinearMap.id ℝ (Vec d) := by
  apply ContinuousLinearMap.ext
  intro v
  change v-0=v
  exact sub_zero v

/-- The original shared circuit's actual derivative is the difference of the
same two nonnegative graph kernels, after the canonical input lift. -/
theorem circuit_hasFDerivAt {d n} (c : Circuit d n) (hc : c.Additive)
    (x : Vec d) (hx : CircuitRegular c (x,0)) :
    HasFDerivAt c.eval (matrixCLM ((dagKernel c (x,0)).1-(dagKernel c (x,0)).2)) x := by
  have hs := (stoppingCircuit_hasFDerivAt c hc (x,0) hx).comp x (liftCLM d).hasFDerivAt
  have hr := (differenceCLM n).hasFDerivAt.comp x hs
  have he : (differenceCLM n) ∘ (stoppingCircuit c ∘ liftCLM d) = c.eval := by
    funext y
    change (stoppingCircuit c (y,0)).1-(stoppingCircuit c (y,0)).2=c.eval y
    simpa only [sub_zero] using stoppingCircuit_recovery c (y,0)
  rw [he] at hr
  rw [← ContinuousLinearMap.comp_assoc,difference_pairMap,ContinuousLinearMap.comp_assoc,
    difference_lift,ContinuousLinearMap.comp_id] at hr
  exact hr

/-- Ordinary-input backward identity for affine/addition/ReLU/selected-pool
DAGs, including residual edges and fanout in the shared graph. -/
theorem circuit_derivative_occupation {d n} (c : Circuit d n) (hc : c.Additive)
    (x : Vec d) (hx : CircuitRegular c (x,0)) (j : Fin n) (i : Fin d) :
    (fderiv ℝ c.eval x (Pi.single i 1)) j =
      occupation c (x,0) j false i false-occupation c (x,0) j false i true := by
  rw [(circuit_hasFDerivAt c hc x hx).fderiv]
  change (((dagKernel c (x,0)).1-(dagKernel c (x,0)).2) *ᵥ (Pi.single i 1)) j=_
  simp [Matrix.mulVec_single_one,occupation_eq_kernel c hc]

end Thesis.StoppingDAG
