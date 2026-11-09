import Thesis.SoftplusCircuitDerivative

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.StoppingDAG
open scoped BigOperators

def pathProbability {d n} (θ : ℝ) : (c : Circuit d n) → Plan c → Vec d → Fin n → DAGPaths c → ℝ
  | .inputs, _, _, _, _ => 1
  | .node prior op, plan, x, j, path =>
      Fin.lastCases
        (match path with
        | .inl _ => 0
        | .inr (.inl ((i,b),rest)) => nodeProbability θ plan.2 (graphSoft θ prior plan.1 x)
            (some (i,b)) * pathProbability θ prior plan.1 x i rest
        | .inr (.inr _) => nodeProbability θ plan.2 (graphSoft θ prior plan.1 x) none)
        (fun i => match path with
        | .inl rest => pathProbability θ prior plan.1 x i rest
        | _ => 0) j

def pathDiscount {d n} (θ : ℝ) : (c : Circuit d n) → Plan c → Vec d → Fin n → DAGPaths c → ℝ
  | .inputs, _, _, _, _ => 1
  | .node prior op, plan, x, j, path =>
      Fin.lastCases
        (match path with
        | .inr (.inl ((i,_),rest)) => nodeDiscount plan.2 (graphSoft θ prior plan.1 x) *
            pathDiscount θ prior plan.1 x i rest
        | _ => 1)
        (fun i => match path with
        | .inl rest => pathDiscount θ prior plan.1 x i rest
        | _ => 1) j

/-- The raw signed-path weight is used only as a proof bridge, not as the
probability or occupation definition. -/
def pathRaw {d n} (θ : ℝ) : (c : Circuit d n) → Plan c → Vec d → Fin n → Fin d → Bool → DAGPaths c → ℝ
  | .inputs, _, _, j, i, p, _ => if j=i ∧ p=false then 1 else 0
  | .node prior op, plan, x, j, i, p, path =>
      Fin.lastCases
        (match path with
        | .inr (.inl ((h,b),rest)) =>
            (if b then (selectedWeights θ plan.2 (graphSoft θ prior plan.1 x)).2 h
              else (selectedWeights θ plan.2 (graphSoft θ prior plan.1 x)).1 h) *
              pathRaw θ prior plan.1 x h i (Bool.xor p b) rest
        | _ => 0)
        (fun h => match path with
        | .inl rest => pathRaw θ prior plan.1 x h i p rest
        | _ => 0) j

theorem pathProbability_nonnegative {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ)
    (x : Vec d) (j : Fin n) (path : DAGPaths c) : 0≤pathProbability θ c plan x j path := by
  induction c with
  | inputs => exact zero_le_one
  | node prior op ih =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [pathProbability,Fin.lastCases_last]
        cases path with
        | inl rest => exact le_rfl
        | inr path =>
            cases path with
            | inl t => exact mul_nonneg (nodeProbability_nonnegative θ plan.2 _ _) (ih plan.1 t.1.1 t.2)
            | inr u => exact nodeProbability_nonnegative θ plan.2 _ none
      · simp only [pathProbability,Fin.lastCases_castSucc]
        cases path with
        | inl rest => exact ih plan.1 i rest
        | inr path => exact le_rfl

theorem pathDiscount_nonnegative {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ)
    (x : Vec d) (j : Fin n) (path : DAGPaths c) : 0≤pathDiscount θ c plan x j path := by
  induction c with
  | inputs => exact zero_le_one
  | node prior op ih =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [pathDiscount,Fin.lastCases_last]
        cases path with
        | inl rest => exact zero_le_one
        | inr path =>
            cases path with
            | inl t => exact mul_nonneg (nodeDiscount_nonnegative plan.2 _) (ih plan.1 t.1.1 t.2)
            | inr u => exact zero_le_one
      · simp only [pathDiscount,Fin.lastCases_castSucc]
        cases path with
        | inl rest => exact ih plan.1 i rest
        | inr path => exact zero_le_one

/-- Every starting graph state defines a genuinely normalized full trajectory
law, including constant nodes and zero-fan-in cemetery termination. -/
theorem pathProbability_normalized {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) (j : Fin n) :
    (∑ path : DAGPaths c,pathProbability θ c plan x j path)=1 := by
  induction c with
  | inputs => change (∑ _ : Unit,(1 : ℝ))=1; simp
  | @node n prior op ih =>
      rw [sum_paths_node]
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [pathProbability,Fin.lastCases_last,Finset.sum_const_zero,zero_add,
          ← Finset.mul_sum,ih,mul_one]
        have h := nodeProbability_normalized θ plan.2 (graphSoft θ prior plan.1 x)
        simpa only [Fintype.sum_option,Fintype.sum_prod_type,add_comm] using h
      · simpa only [pathProbability,Fin.lastCases_castSucc,Finset.sum_const_zero,add_zero] using ih plan.1 i


end Thesis.SoftplusCircuit
