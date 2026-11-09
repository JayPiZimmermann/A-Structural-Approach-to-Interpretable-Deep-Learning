import Thesis.StoppingDAGCuts

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Matrix
open scoped BigOperators

def visitIndicator (state : ℕ) (turn : Bool) (target : ℕ) (channel : Bool) : ℝ :=
  if state=target ∧ turn=channel then 1 else 0

/-- Sum of cumulative-discount-weighted visits to an arbitrary graph state.
Bypass constructors do not introduce graph visits; each actual predecessor move
multiplies every later visit by the local discount. -/
def visitWeight {d n} : (c : Circuit d n) → PairVec d → Fin n → Bool → ℕ → Bool → DAGPaths c → ℝ
  | .inputs, _, j, turn, target, channel, _ => visitIndicator j.val turn target channel
  | @Circuit.node _ n prior op, x, j, turn, target, channel, path =>
      Fin.lastCases
        (let r := visitIndicator n turn target channel
         match path with
         | .inr (.inl ((i,p),rest)) => r+
             localDiscount (expressionKernel op (stoppingCircuit prior x))*
               visitWeight prior x i (Bool.xor turn p) target channel rest
         | _ => r)
        (fun i => match path with
         | .inl rest => visitWeight prior x i turn target channel rest
         | _ => 0) j

def fullOccupation {d n} (c : Circuit d n) (x : PairVec d) (j : Fin n)
    (turn : Bool) (target : ℕ) (channel : Bool) : ℝ :=
  ∑ path : DAGPaths c,pathProbability c x j path*visitWeight c x j turn target channel path

theorem fullOccupation_node {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (x : PairVec d) (turn : Bool) (target : ℕ) (channel : Bool) :
    fullOccupation (.node prior op) x (Fin.last n) turn target channel =
      visitIndicator n turn target channel+
      ∑ i : Fin n,∑ b : Bool,
        localDiscount (expressionKernel op (stoppingCircuit prior x))*
          localProbability (expressionKernel op (stoppingCircuit prior x)) (some (i,b))*
          fullOccupation prior x i (Bool.xor turn b) target channel := by
  let k := expressionKernel op (stoppingCircuit prior x)
  let z := visitIndicator n turn target channel
  unfold fullOccupation
  rw [sum_paths_node]
  simp only [pathProbability,visitWeight,Fin.lastCases_last,zero_mul,Finset.sum_const_zero,zero_add]
  change (∑ i : Fin n,∑ b : Bool,∑ rest : DAGPaths prior,
      (localProbability k (some (i,b))*pathProbability prior x i rest)*
        (z+localDiscount k*visitWeight prior x i (Bool.xor turn b) target channel rest))+
      localProbability k none*z = _
  simp_rw [show ∀ a b c d e : ℝ,(a*b)*(c+d*e)=a*c*b+(d*a)*(b*e) by intros; ring]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,pathProbability_normalized,mul_one]
  have h := localProbability_normalized k
  simp only [Fintype.sum_option,Fintype.sum_prod_type] at h
  simp_rw [← Finset.sum_mul]
  dsimp only [k,z] at h ⊢
  linear_combination visitIndicator n turn target channel * h

theorem fullOccupation_old {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (x : PairVec d) (j : Fin n) (turn : Bool) (target : ℕ) (channel : Bool) :
    fullOccupation (.node prior op) x j.castSucc turn target channel =
      fullOccupation prior x j turn target channel := by
  unfold fullOccupation
  rw [sum_paths_node]
  simp only [pathProbability,visitWeight,Fin.lastCases_castSucc,zero_mul,
    Finset.sum_const_zero,add_zero]

theorem visitWeight_above {d n} (c : Circuit d n) (x : PairVec d) (j : Fin n)
    (turn : Bool) (target : ℕ) (channel : Bool) (hj : j.val<target) (path : DAGPaths c) :
    visitWeight c x j turn target channel path=0 := by
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
                rw [ih i (Bool.xor turn b) (lt_trans i.isLt h) rest]
                simp [visitIndicator,ne_of_lt h]
      · intro h
        simp only [visitWeight,Fin.lastCases_castSucc]
        cases path with
        | inl rest => exact ih i turn h rest
        | inr t => rfl

theorem fullOccupation_above {d n} (c : Circuit d n) (x : PairVec d) (j : Fin n)
    (turn : Bool) (target : ℕ) (channel : Bool) (hj : j.val<target) :
    fullOccupation c x j turn target channel=0 := by
  simp [fullOccupation,visitWeight_above c x j turn target channel hj]

theorem fullOccupation_self {d n} (c : Circuit d n) (x : PairVec d) (j : Fin n)
    (turn channel : Bool) :
    fullOccupation c x j turn j.val channel=if turn=channel then 1 else 0 := by
  induction c generalizing turn with
  | inputs => simp [fullOccupation,DAGPaths,pathProbability,visitWeight,visitIndicator]
  | @node n prior op ih =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [fullOccupation_node]
        have hz : ∀ i : Fin n,∀ b : Bool,fullOccupation prior x i b n channel=0 :=
          fun i b => fullOccupation_above prior x i b n channel i.isLt
        simp [hz,visitIndicator]
      · simpa only [fullOccupation_old,Fin.val_castSucc] using ih i turn

theorem circuit_width_le {d n} (c : Circuit d n) : d≤n := by
  induction c with
  | inputs => exact le_rfl
  | node prior op ih => omega

theorem occupation_node {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (hc : (Circuit.node prior op).Additive) (x : PairVec d) (turn : Bool) (i : Fin d) (channel : Bool) :
    occupation (.node prior op) x (Fin.last n) turn i channel =
      ∑ h : Fin n,∑ b : Bool,
        localDiscount (expressionKernel op (stoppingCircuit prior x))*
          localProbability (expressionKernel op (stoppingCircuit prior x)) (some (h,b))*
          occupation prior x h (Bool.xor turn b) i channel := by
  simp_rw [local_discount_recovery _ (expressionKernel_nonnegative op hc.2 _),
    occupation_eq_kernel (.node prior op) hc,occupation_eq_kernel prior hc.1]
  cases turn <;> cases channel <;>
    simp [dagKernel,combineKernel,Fin.snoc,Matrix.vecMul,dotProduct,Finset.sum_add_distrib,add_comm]

theorem occupation_old {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (hc : (Circuit.node prior op).Additive) (x : PairVec d) (j : Fin n)
    (turn : Bool) (i : Fin d) (channel : Bool) :
    occupation (.node prior op) x j.castSucc turn i channel=occupation prior x j turn i channel := by
  simp [occupation_eq_kernel (.node prior op) hc,occupation_eq_kernel prior hc.1,dagKernel,Fin.snoc]

/-- Cut/full-trajectory bridge for every intermediate graph node: choose the
shared prefix ending at that node. The original full trajectory may continue
below the cut; its total discounted visits to the chosen node equal the suffix
law's terminal occupation, since graph edges strictly decrease node indices. -/
theorem fullOccupation_graft_last {d m n} (pre : Circuit d (m+1)) (suffix : Circuit (m+1) n)
    (hc : (graft pre suffix).Additive) (x : PairVec d) (j : Fin n) (turn channel : Bool) :
    fullOccupation (graft pre suffix) x j turn m channel =
      occupation suffix (stoppingCircuit pre x) j turn (Fin.last m) channel := by
  have hs := ((graft_additive pre suffix).mp hc).2
  induction suffix generalizing turn with
  | inputs =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [show graft pre Circuit.inputs=pre from rfl]
        have ht := fullOccupation_self pre x (Fin.last m) turn channel
        simp only [Fin.val_last] at ht
        rw [ht]
        cases turn <;> cases channel <;>
          simp [occupation_eq_kernel (Circuit.inputs : Circuit (m+1) (m+1)) (by trivial),dagKernel,Matrix.one_apply]
      · rw [show graft pre Circuit.inputs=pre from rfl,
          fullOccupation_above pre x i.castSucc turn m channel i.isLt]
        cases turn <;> cases channel <;>
          simp [occupation_eq_kernel (Circuit.inputs : Circuit (m+1) (m+1)) (by trivial),dagKernel,Matrix.one_apply]
  | @node n prior op ih =>
      have hp : (graft pre prior).Additive := hc.1
      refine Fin.lastCases ?_ (fun i => ?_) j
      · change fullOccupation (.node (graft pre prior) op) x (Fin.last n) turn m channel=_
        rw [fullOccupation_node,occupation_node prior op hs]
        have hn : n≠m := by have h := circuit_width_le prior; omega
        simp only [visitIndicator,hn,false_and,ite_false,zero_add,graft_stopping]
        simp_rw [ih hp _ _ hs.1]
      · change fullOccupation (.node (graft pre prior) op) x i.castSucc turn m channel=_
        rw [fullOccupation_old,occupation_old prior op hs]
        exact ih hp i turn hs.1

end Thesis.StoppingDAG
