import Thesis.StoppingDAGPaths

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Matrix
open scoped BigOperators

/-- Full discounted terminal occupation under the normalized finite trajectory
law. The two channels retain the parity of sign changes along the path. -/
def occupation {d n} (c : Circuit d n) (x : PairVec d) (j : Fin n)
    (turn : Bool) (i : Fin d) (channel : Bool) : ℝ :=
  ∑ path : DAGPaths c, pathDiscount c x j path * pathProbability c x j path *
    (if pathOutcome c j turn path=some (i,channel) then 1 else 0)

theorem path_weight_recovery {d n} (c : Circuit d n) (hc : c.Additive)
    (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool) (path : DAGPaths c) :
    pathDiscount c x j path * pathProbability c x j path *
      (if pathOutcome c j turn path=some (i,channel) then 1 else 0) =
      pathRaw c x j i (Bool.xor channel turn) path := by
  induction c generalizing turn channel with
  | inputs =>
      cases turn <;> cases channel <;> simp [pathDiscount,pathProbability,pathOutcome,pathRaw,eq_comm]
  | node prior op ih =>
      have hk := expressionKernel_nonnegative op hc.2 (stoppingCircuit prior x)
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
                rw [local_discount_recovery _ hk,ih hc.1]
                congr 2
                cases channel <;> cases turn <;> cases b <;> rfl
      · cases path with
        | inl rest => simpa only [pathDiscount,pathProbability,pathOutcome,pathRaw,
            Fin.lastCases_castSucc] using ih hc.1 h turn channel rest
        | inr t => simp [pathDiscount,pathProbability,pathOutcome,pathRaw]

theorem pathRaw_sum {d n} (c : Circuit d n) (x : PairVec d) (j : Fin n) (i : Fin d) (p : Bool) :
    (∑ path : DAGPaths c,pathRaw c x j i p path) =
      if p then (dagKernel c x).2 j i else (dagKernel c x).1 j i := by
  induction c generalizing p with
  | inputs => cases p <;> simp [DAGPaths,pathRaw,dagKernel,Matrix.one_apply,eq_comm]
  | @node n prior op ih =>
      rw [sum_paths_node]
      refine Fin.lastCases ?_ (fun h => ?_) j
      · simp only [pathRaw,Fin.lastCases_last,Finset.sum_const_zero,zero_add,add_zero,
          ← Finset.mul_sum]
        simp_rw [ih]
        cases p <;> simp [Fintype.sum_bool,dagKernel,combineKernel,Fin.snoc,Matrix.vecMul,dotProduct,
          Finset.sum_add_distrib,add_comm]
      · simpa [pathRaw,Fin.lastCases_castSucc,dagKernel,Fin.snoc] using ih h p

/-- Global two-channel occupation identity. This algebraic selected-operator
statement includes deterministic ties and does not claim differentiability there. -/
theorem occupation_eq_kernel {d n} (c : Circuit d n) (hc : c.Additive)
    (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool) :
    occupation c x j turn i channel =
      if Bool.xor channel turn then (dagKernel c x).2 j i else (dagKernel c x).1 j i := by
  simp only [occupation,path_weight_recovery c hc]
  exact pathRaw_sum c x j i (Bool.xor channel turn)

theorem occupation_nonnegative {d n} (c : Circuit d n) (hc : c.Additive)
    (x : PairVec d) (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool) :
    0≤occupation c x j turn i channel := by
  apply Finset.sum_nonneg
  intro path _
  exact mul_nonneg (mul_nonneg (pathDiscount_nonnegative c hc x j path)
    (pathProbability_nonnegative c hc x j path)) (by split_ifs <;> norm_num)

end Thesis.StoppingDAG
