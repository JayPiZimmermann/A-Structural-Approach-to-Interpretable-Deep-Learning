import Thesis.SoftplusCircuitPaths

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.StoppingDAG Matrix
open scoped BigOperators

/-- Full discounted terminal occupation under the normalized finite trajectory
law. The two channels retain the parity of sign changes along the path. -/
def occupation {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) (j : Fin n)
    (turn : Bool) (i : Fin d) (channel : Bool) : ℝ :=
  ∑ path : DAGPaths c, pathDiscount θ c plan x j path * pathProbability θ c plan x j path *
    (if pathOutcome c j turn path=some (i,channel) then 1 else 0)

theorem path_weight_recovery {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ)
    (x : Vec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool) (path : DAGPaths c) :
    pathDiscount θ c plan x j path * pathProbability θ c plan x j path *
      (if pathOutcome c j turn path=some (i,channel) then 1 else 0) =
      pathRaw θ c plan x j i (Bool.xor channel turn) path := by
  induction c generalizing turn channel with
  | inputs =>
      cases turn <;> cases channel <;> simp [pathDiscount,pathProbability,pathOutcome,pathRaw,eq_comm]
  | node prior op ih =>
      refine Fin.lastCases ?_ (fun h => ?_) j
      · cases path with
        | inl rest => simp [pathDiscount,pathProbability,pathOutcome,pathRaw]
        | inr path =>
            cases path with
            | inr u => simp [pathDiscount,pathProbability,pathOutcome,pathRaw]
            | inl t =>
                rcases t with ⟨⟨h,b⟩,rest⟩
                simp only [pathDiscount,pathProbability,pathOutcome,pathRaw,Fin.lastCases_last]
                rw [show ∀ a b c d e : ℝ, a*b*(c*d)*e=(a*c)*(b*d*e) by intros; ring]
                rw [node_discount_recovery,ih plan.1]
                congr 2
                cases channel <;> cases turn <;> cases b <;> rfl
      · cases path with
        | inl rest => simpa only [pathDiscount,pathProbability,pathOutcome,pathRaw,
            Fin.lastCases_castSucc] using ih plan.1 h turn channel rest
        | inr t => simp [pathDiscount,pathProbability,pathOutcome,pathRaw]

theorem pathRaw_sum {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) (j : Fin n) (i : Fin d) (p : Bool) :
    (∑ path : DAGPaths c,pathRaw θ c plan x j i p path) =
      if p then (graphKernel θ c plan x).2 j i else (graphKernel θ c plan x).1 j i := by
  induction c generalizing p with
  | inputs => cases p <;> simp [DAGPaths,pathRaw,graphKernel,appendMatrix,Matrix.one_apply,eq_comm]
  | @node n prior op ih =>
      rw [sum_paths_node]
      refine Fin.lastCases ?_ (fun h => ?_) j
      · simp only [pathRaw,Fin.lastCases_last,Finset.sum_const_zero,zero_add,add_zero,
          ← Finset.mul_sum]
        simp_rw [ih]
        cases p <;> simp [Fintype.sum_bool,graphKernel,appendMatrix,combineKernel,Fin.snoc,Matrix.vecMul,dotProduct,
          Finset.sum_add_distrib,add_comm]
      · simpa [pathRaw,Fin.lastCases_castSucc,graphKernel,appendMatrix,Fin.snoc] using ih plan.1 h p

/-- Global two-channel occupation identity. This algebraic selected-operator
statement includes deterministic ties and does not claim differentiability there. -/
theorem occupation_eq_kernel {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ)
    (x : Vec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool) :
    occupation c plan θ x j turn i channel =
      if Bool.xor channel turn then (graphKernel θ c plan x).2 j i else (graphKernel θ c plan x).1 j i := by
  simp only [occupation,path_weight_recovery c plan θ]
  exact pathRaw_sum c plan θ x j i (Bool.xor channel turn)

theorem occupation_nonnegative {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ)
    (x : Vec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool) :
    0≤occupation c plan θ x j turn i channel := by
  apply Finset.sum_nonneg
  intro path _
  exact mul_nonneg (mul_nonneg (pathDiscount_nonnegative c plan θ x j path)
    (pathProbability_nonnegative c plan θ x j path)) (by split_ifs <;> norm_num)

/-- Source ordinary-input softplus backward identity for the actual shared DAG.
Only hard pools require unique winners; all affine fan-ins, including zero,
and all soft activation preactivations are covered. -/
theorem graph_derivative_occupation {d n} (c : Circuit d n) (plan : Plan c)
    (θ : ℝ) (hθ : 0<θ) (x : Vec d) (hx : Regular θ c plan x) (j : Fin n) (i : Fin d) :
    (fderiv ℝ (graphSoft θ c plan) x (Pi.single i 1)) j =
      occupation c plan θ x j false i false-occupation c plan θ x j false i true := by
  rw [(graphSoft_hasFDerivAt c plan θ hθ x hx).fderiv]
  change (((graphKernel θ c plan x).1-(graphKernel θ c plan x).2) *ᵥ (Pi.single i 1)) j=_
  simp [Matrix.mulVec_single_one,occupation_eq_kernel c plan θ]

end Thesis.SoftplusCircuit
