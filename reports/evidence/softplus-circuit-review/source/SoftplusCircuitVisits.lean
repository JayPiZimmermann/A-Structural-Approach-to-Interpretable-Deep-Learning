import Thesis.SoftplusCircuitCuts

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.StoppingDAG Matrix
open scoped BigOperators

/-- Sum of cumulative-discount-weighted visits to an arbitrary graph state.
Bypass constructors do not introduce graph visits; each actual predecessor move
multiplies every later visit by the local discount. -/
def visitWeight {d n} (θ : ℝ) : (c : Circuit d n) → Plan c → Vec d → Fin n → Bool → ℕ → Bool → DAGPaths c → ℝ
  | .inputs, _, _, j, turn, target, channel, _ => visitIndicator j.val turn target channel
  | @Circuit.node _ n prior op, plan, x, j, turn, target, channel, path =>
      Fin.lastCases
        (let r := visitIndicator n turn target channel
         match path with
         | .inr (.inl ((i,p),rest)) => r+
             nodeDiscount plan.2 (graphSoft θ prior plan.1 x)*
               visitWeight θ prior plan.1 x i (Bool.xor turn p) target channel rest
         | _ => r)
        (fun i => match path with
         | .inl rest => visitWeight θ prior plan.1 x i turn target channel rest
         | _ => 0) j

def fullOccupation {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) (j : Fin n)
    (turn : Bool) (target : ℕ) (channel : Bool) : ℝ :=
  ∑ path : DAGPaths c,pathProbability θ c plan x j path*visitWeight θ c plan x j turn target channel path

theorem fullOccupation_node {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (plan : Plan (.node prior op)) (θ : ℝ) (x : Vec d) (turn : Bool) (target : ℕ) (channel : Bool) :
    fullOccupation (.node prior op) plan θ x (Fin.last n) turn target channel =
      visitIndicator n turn target channel+
      ∑ i : Fin n,∑ b : Bool,
        nodeDiscount plan.2 (graphSoft θ prior plan.1 x)*
          nodeProbability θ plan.2 (graphSoft θ prior plan.1 x) (some (i,b))*
          fullOccupation prior plan.1 θ x i (Bool.xor turn b) target channel := by
  let z := visitIndicator n turn target channel
  unfold fullOccupation
  rw [sum_paths_node]
  simp only [pathProbability,visitWeight,Fin.lastCases_last,zero_mul,Finset.sum_const_zero,zero_add]
  change (∑ i : Fin n,∑ b : Bool,∑ rest : DAGPaths prior,
      (nodeProbability θ plan.2 (graphSoft θ prior plan.1 x) (some (i,b))*pathProbability θ prior plan.1 x i rest)*
        (z+nodeDiscount plan.2 (graphSoft θ prior plan.1 x)*visitWeight θ prior plan.1 x i (Bool.xor turn b) target channel rest))+
      nodeProbability θ plan.2 (graphSoft θ prior plan.1 x) none*z = _
  simp_rw [show ∀ a b c d e : ℝ,(a*b)*(c+d*e)=a*c*b+(d*a)*(b*e) by intros; ring]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,pathProbability_normalized,mul_one]
  have h := nodeProbability_normalized θ plan.2 (graphSoft θ prior plan.1 x)
  simp only [Fintype.sum_option,Fintype.sum_prod_type] at h
  simp_rw [← Finset.sum_mul]
  dsimp only [z] at h ⊢
  linear_combination visitIndicator n turn target channel * h

theorem fullOccupation_old {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (plan : Plan (.node prior op)) (θ : ℝ) (x : Vec d) (j : Fin n) (turn : Bool) (target : ℕ) (channel : Bool) :
    fullOccupation (.node prior op) plan θ x j.castSucc turn target channel =
      fullOccupation prior plan.1 θ x j turn target channel := by
  unfold fullOccupation
  rw [sum_paths_node]
  simp only [pathProbability,visitWeight,Fin.lastCases_castSucc,zero_mul,
    Finset.sum_const_zero,add_zero]

theorem visitWeight_above {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) (j : Fin n)
    (turn : Bool) (target : ℕ) (channel : Bool) (hj : j.val<target) (path : DAGPaths c) :
    visitWeight θ c plan x j turn target channel path=0 := by
  induction c generalizing turn with
  | inputs => simp [visitWeight,visitIndicator,ne_of_lt hj]
  | @node n prior op ih =>
      refine Fin.lastCases ?_ (fun i => ?_) j hj
      · intro h
        simp only [Fin.val_last] at h
        simp only [visitWeight,Fin.lastCases_last]
        cases path with
        | inl rest => simp [visitIndicator,ne_of_lt h]
        | inr t =>
            cases t with
            | inr u => simp [visitIndicator,ne_of_lt h]
            | inl t =>
                rcases t with ⟨⟨i,b⟩,rest⟩
                dsimp only
                rw [ih plan.1 i (Bool.xor turn b) (lt_trans i.isLt h) rest]
                simp [visitIndicator,ne_of_lt h]
      · intro h
        simp only [visitWeight,Fin.lastCases_castSucc]
        cases path with
        | inl rest => exact ih plan.1 i turn h rest
        | inr t => rfl

theorem fullOccupation_above {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) (j : Fin n)
    (turn : Bool) (target : ℕ) (channel : Bool) (hj : j.val<target) :
    fullOccupation c plan θ x j turn target channel=0 := by
  simp [fullOccupation,visitWeight_above c plan θ x j turn target channel hj]

theorem fullOccupation_self {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) (j : Fin n)
    (turn channel : Bool) :
    fullOccupation c plan θ x j turn j.val channel=if turn=channel then 1 else 0 := by
  induction c generalizing turn with
  | inputs => simp [fullOccupation,DAGPaths,pathProbability,visitWeight,visitIndicator]
  | @node n prior op ih =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [fullOccupation_node]
        have hz : ∀ i : Fin n,∀ b : Bool,fullOccupation prior plan.1 θ x i b n channel=0 :=
          fun i b => fullOccupation_above prior plan.1 θ x i b n channel i.isLt
        simp [hz,visitIndicator]
      · simpa only [fullOccupation_old,Fin.val_castSucc] using ih plan.1 i turn

theorem occupation_node {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (plan : Plan (.node prior op)) (θ : ℝ) (x : Vec d) (turn : Bool) (i : Fin d) (channel : Bool) :
    occupation (.node prior op) plan θ x (Fin.last n) turn i channel =
      ∑ h : Fin n,∑ b : Bool,
        nodeDiscount plan.2 (graphSoft θ prior plan.1 x)*
          nodeProbability θ plan.2 (graphSoft θ prior plan.1 x) (some (h,b))*
          occupation prior plan.1 θ x h (Bool.xor turn b) i channel := by
  simp_rw [node_discount_recovery,
    occupation_eq_kernel (.node prior op) plan θ,occupation_eq_kernel prior plan.1 θ]
  cases turn <;> cases channel <;>
    simp [graphKernel,appendMatrix,combineKernel,Fin.snoc,Matrix.vecMul,dotProduct,Finset.sum_add_distrib,add_comm]

theorem occupation_old {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (plan : Plan (.node prior op)) (θ : ℝ) (x : Vec d) (j : Fin n)
    (turn : Bool) (i : Fin d) (channel : Bool) :
    occupation (.node prior op) plan θ x j.castSucc turn i channel=occupation prior plan.1 θ x j turn i channel := by
  simp [occupation_eq_kernel (.node prior op) plan θ,occupation_eq_kernel prior plan.1 θ,graphKernel,appendMatrix,Fin.snoc]

/-- Cut/full-trajectory bridge for every intermediate graph node: choose the
shared prefix ending at that node. The original full trajectory may continue
below the cut; its total discounted visits to the chosen node equal the suffix
law's terminal occupation, since graph edges strictly decrease node indices. -/
theorem fullOccupation_graft_last {d m n} (pre : Circuit d (m+1)) (prePlan : Plan pre)
    (suffix : Circuit (m+1) n) (suffixPlan : Plan suffix) (θ : ℝ) (x : Vec d)
    (j : Fin n) (turn channel : Bool) :
    fullOccupation (graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) θ x j turn m channel =
      occupation suffix suffixPlan θ (graphSoft θ pre prePlan x) j turn (Fin.last m) channel := by
  induction suffix generalizing turn with
  | inputs =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · change fullOccupation pre prePlan θ x (Fin.last m) turn m channel=_
        have ht := fullOccupation_self pre prePlan θ x (Fin.last m) turn channel
        simp only [Fin.val_last] at ht
        rw [ht]
        cases turn <;> cases channel <;>
          simp [occupation_eq_kernel,graphKernel,Matrix.one_apply]
      · change fullOccupation pre prePlan θ x i.castSucc turn m channel=_
        rw [fullOccupation_above pre prePlan θ x i.castSucc turn m channel i.isLt]
        cases turn <;> cases channel <;>
          simp [occupation_eq_kernel,graphKernel,Matrix.one_apply]
  | @node n prior op ih =>
      rcases suffixPlan with ⟨priorPlan,spec⟩
      refine Fin.lastCases ?_ (fun i => ?_) j
      · change fullOccupation (.node (graft pre prior) op)
          (graftPlan pre prePlan prior priorPlan,spec) θ x (Fin.last n) turn m channel=_
        erw [fullOccupation_node,occupation_node]
        have hn : n≠m := by have h := circuit_width_le prior; omega
        simp only [visitIndicator,hn,false_and,ite_false,zero_add,graft_soft]
        simp_rw [ih]
      · change fullOccupation (.node (graft pre prior) op)
          (graftPlan pre prePlan prior priorPlan,spec) θ x i.castSucc turn m channel=_
        erw [fullOccupation_old,occupation_old]
        exact ih priorPlan i turn

/-- Full-trajectory occupation version of the actual intermediate-node gradient:
the law belongs to the original grafted DAG, rather than to an unrelated suffix. -/
theorem intermediate_derivative_fullOccupation {d m n} (pre : Circuit d (m+1))
    (prePlan : Plan pre) (suffix : Circuit (m+1) n) (suffixPlan : Plan suffix)
    (θ : ℝ) (hθ : 0<θ) (x : Vec d)
    (hx : Regular θ (graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) x)
    (j : Fin n) (q : Bool) :
    (fderiv ℝ (graphSoft θ suffix suffixPlan) (graphSoft θ pre prePlan x)
      (Pi.single (Fin.last m) 1)) j =
      (if q then (-1 : ℝ) else 1)*
        (fullOccupation (graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) θ x j q m false-
         fullOccupation (graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) θ x j q m true) := by
  rw [fullOccupation_graft_last,fullOccupation_graft_last]
  exact cut_derivative_occupation pre prePlan suffix suffixPlan θ hθ x hx j (Fin.last m) q

end Thesis.SoftplusCircuit
