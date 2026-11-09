import Thesis.StoppingDAGDerivative
import Mathlib.Data.Fintype.Sum

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit Matrix
open scoped BigOperators

/-- Structural discount of the selected two-channel predecessor row. -/
def localDiscount {n} (k : PairVec n) : ℝ := ∑ i, (k.1 i+k.2 i)

def localProbability {n} (k : PairVec n) : Option (Fin n × Bool) → ℝ
  | none => if localDiscount k=0 then 1 else 0
  | some (i,b) => (if b then k.2 i else k.1 i)/localDiscount k

theorem localDiscount_nonnegative {n} (k : PairVec n) (hk : 0≤k) : 0≤localDiscount k :=
  Finset.sum_nonneg (fun i _ => add_nonneg (hk.1 i) (hk.2 i))

theorem localProbability_nonnegative {n} (k : PairVec n) (hk : 0≤k) (t : Option (Fin n × Bool)) :
    0≤localProbability k t := by
  cases t with
  | none => simp only [localProbability]; split_ifs <;> norm_num
  | some t =>
      rcases t with ⟨i,b⟩
      cases b <;> exact div_nonneg (by first | exact hk.1 i | exact hk.2 i) (localDiscount_nonnegative k hk)

theorem localProbability_normalized {n} (k : PairVec n) : (∑ t,localProbability k t)=1 := by
  by_cases hz : localDiscount k=0
  · simp [localProbability,hz,Fintype.sum_option]
  · simp only [Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool,localProbability,
      hz,ite_false,ite_true,Bool.false_eq_true]
    simp_rw [← add_div]
    rw [← Finset.sum_div]
    simpa [localDiscount,add_comm] using div_self hz

theorem local_zero_weights {n} (k : PairVec n) (hk : 0≤k) (hz : localDiscount k=0) (i : Fin n) :
    k.1 i=0 ∧ k.2 i=0 := by
  have h := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => add_nonneg (hk.1 j) (hk.2 j))).mp hz i (Finset.mem_univ i)
  have hp : (0 : ℝ)≤k.1 i := hk.1 i
  have hn : (0 : ℝ)≤k.2 i := hk.2 i
  exact ⟨by linarith,by linarith⟩

theorem local_discount_recovery {n} (k : PairVec n) (hk : 0≤k) (i : Fin n) (b : Bool) :
    localDiscount k*localProbability k (some (i,b)) = if b then k.2 i else k.1 i := by
  by_cases hz : localDiscount k=0
  · have h := local_zero_weights k hk hz i
    simp [localProbability,hz,h.1,h.2]
  · simp only [localProbability]
    field_simp

/-- A complete finite trajectory either bypasses the newly appended state,
chooses a signed predecessor and continues in the prior DAG, or terminates in
its cemetery. The sum type keeps cemetery paths normalized without fake tails. -/
@[reducible] def DAGPaths {d n} : Circuit d n → Type
  | .inputs => Unit
  | @Circuit.node _ n prior _ => DAGPaths prior ⊕ (((Fin n × Bool) × DAGPaths prior) ⊕ Unit)

instance dagPathsFintype {d n} : (c : Circuit d n) → Fintype (DAGPaths c)
  | .inputs => inferInstanceAs (Fintype Unit)
  | @Circuit.node _ n prior op => by
      letI := dagPathsFintype prior
      exact inferInstanceAs (Fintype (DAGPaths prior ⊕ (((Fin n × Bool) × DAGPaths prior) ⊕ Unit)))

def pathProbability {d n} : (c : Circuit d n) → PairVec d → Fin n → DAGPaths c → ℝ
  | .inputs, _, _, _ => 1
  | .node prior op, x, j, path =>
      Fin.lastCases
        (match path with
        | .inl _ => 0
        | .inr (.inl ((i,b),rest)) => localProbability (expressionKernel op (stoppingCircuit prior x))
            (some (i,b)) * pathProbability prior x i rest
        | .inr (.inr _) => localProbability (expressionKernel op (stoppingCircuit prior x)) none)
        (fun i => match path with
        | .inl rest => pathProbability prior x i rest
        | _ => 0) j

def pathDiscount {d n} : (c : Circuit d n) → PairVec d → Fin n → DAGPaths c → ℝ
  | .inputs, _, _, _ => 1
  | .node prior op, x, j, path =>
      Fin.lastCases
        (match path with
        | .inr (.inl ((i,_),rest)) => localDiscount (expressionKernel op (stoppingCircuit prior x)) *
            pathDiscount prior x i rest
        | _ => 1)
        (fun i => match path with
        | .inl rest => pathDiscount prior x i rest
        | _ => 1) j

def pathOutcome {d n} : (c : Circuit d n) → Fin n → Bool → DAGPaths c → Option (Fin d × Bool)
  | .inputs, j, turn, _ => some (j,turn)
  | .node prior _, j, turn, path =>
      Fin.lastCases
        (match path with
        | .inr (.inl ((i,b),rest)) => pathOutcome prior i (Bool.xor turn b) rest
        | _ => none)
        (fun i => match path with
        | .inl rest => pathOutcome prior i turn rest
        | _ => none) j

/-- The raw signed-path weight is used only as a proof bridge, not as the
probability or occupation definition. -/
def pathRaw {d n} : (c : Circuit d n) → PairVec d → Fin n → Fin d → Bool → DAGPaths c → ℝ
  | .inputs, _, j, i, p, _ => if j=i ∧ p=false then 1 else 0
  | .node prior op, x, j, i, p, path =>
      Fin.lastCases
        (match path with
        | .inr (.inl ((h,b),rest)) =>
            (if b then (expressionKernel op (stoppingCircuit prior x)).2 h
              else (expressionKernel op (stoppingCircuit prior x)).1 h) *
              pathRaw prior x h i (Bool.xor p b) rest
        | _ => 0)
        (fun h => match path with
        | .inl rest => pathRaw prior x h i p rest
        | _ => 0) j

theorem pathProbability_nonnegative {d n} (c : Circuit d n) (hc : c.Additive)
    (x : PairVec d) (j : Fin n) (path : DAGPaths c) : 0≤pathProbability c x j path := by
  induction c with
  | inputs => exact zero_le_one
  | node prior op ih =>
      have hk := expressionKernel_nonnegative op hc.2 (stoppingCircuit prior x)
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [pathProbability,Fin.lastCases_last]
        cases path with
        | inl rest => exact le_rfl
        | inr path =>
            cases path with
            | inl t => exact mul_nonneg (localProbability_nonnegative _ hk _) (ih hc.1 t.1.1 t.2)
            | inr u => exact localProbability_nonnegative _ hk none
      · simp only [pathProbability,Fin.lastCases_castSucc]
        cases path with
        | inl rest => exact ih hc.1 i rest
        | inr path => exact le_rfl

theorem pathDiscount_nonnegative {d n} (c : Circuit d n) (hc : c.Additive)
    (x : PairVec d) (j : Fin n) (path : DAGPaths c) : 0≤pathDiscount c x j path := by
  induction c with
  | inputs => exact zero_le_one
  | node prior op ih =>
      have hk := expressionKernel_nonnegative op hc.2 (stoppingCircuit prior x)
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [pathDiscount,Fin.lastCases_last]
        cases path with
        | inl rest => exact zero_le_one
        | inr path =>
            cases path with
            | inl t => exact mul_nonneg (localDiscount_nonnegative _ hk) (ih hc.1 t.1.1 t.2)
            | inr u => exact zero_le_one
      · simp only [pathDiscount,Fin.lastCases_castSucc]
        cases path with
        | inl rest => exact ih hc.1 i rest
        | inr path => exact zero_le_one

theorem sum_paths_node {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (f : DAGPaths (.node prior op) → ℝ) :
    (∑ path : DAGPaths (.node prior op),f path) =
      (∑ rest : DAGPaths prior,f (.inl rest)) +
      ((∑ i : Fin n,∑ b : Bool,∑ rest : DAGPaths prior,f (.inr (.inl ((i,b),rest))))) +
      f (.inr (.inr ())) := by
  change (∑ path : DAGPaths prior ⊕ (((Fin n × Bool) × DAGPaths prior) ⊕ Unit),f path)=_
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type,Fintype.sum_unique,add_assoc]

/-- Every starting graph state defines a genuinely normalized full trajectory
law, including constant nodes and zero-fan-in cemetery termination. -/
theorem pathProbability_normalized {d n} (c : Circuit d n) (x : PairVec d) (j : Fin n) :
    (∑ path : DAGPaths c,pathProbability c x j path)=1 := by
  induction c with
  | inputs => change (∑ _ : Unit,(1 : ℝ))=1; simp
  | @node n prior op ih =>
      rw [sum_paths_node]
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [pathProbability,Fin.lastCases_last,Finset.sum_const_zero,zero_add,
          ← Finset.mul_sum,ih,mul_one]
        have h := localProbability_normalized (expressionKernel op (stoppingCircuit prior x))
        simpa only [Fintype.sum_option,Fintype.sum_prod_type,add_comm] using h
      · simpa only [pathProbability,Fin.lastCases_castSucc,Finset.sum_const_zero,add_zero] using ih i

end Thesis.StoppingDAG
