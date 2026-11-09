import Thesis.StoppingDAGBackward

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Matrix
open scoped BigOperators

/-- The selected affine bias is computed from the actual expression syntax.
It is an immediate stopping-game reward; it is not defined by subtracting a
claimed derivative from the forward value. -/
def expressionOffset {n} : SignedExpr (Fin n) → PairVec n → ℝ × ℝ
  | .input _, _ => (0,0)
  | .constant c, _ => (max c 0,max (-c) 0)
  | .add a b, x => expressionOffset a x+expressionOffset b x
  | .scale c a, x => scalarSplitMap c (expressionOffset a x)
  | .mul _ _, _ => (0,0)
  | .maximum a b, x => if score b x<score a x then expressionOffset a x else expressionOffset b x

theorem stoppingExpr_affine {n} (e : SignedExpr (Fin n)) (he : e.Additive) (x : PairVec n) :
    stoppingExpr e x=kernelMap (expressionKernel e x) x+expressionOffset e x := by
  induction e with
  | input i =>
      simp [stoppingExpr,expressionKernel,expressionOffset,kernelMap_apply,
        coefficientRow_single,coefficientRow_zero]
  | constant c => simp [stoppingExpr,expressionKernel,expressionOffset,kernelMap_apply,coefficientRow_zero]
  | add a b ha hb =>
      rw [stoppingExpr,ha he.1,hb he.2]
      simp only [expressionKernel,expressionOffset,kernelMap_add,ContinuousLinearMap.add_apply]
      abel
  | scale c a ha =>
      change scalarSplitMap c (stoppingExpr a x)=_
      rw [ha he]
      simp only [expressionKernel,kernelMap_scale,ContinuousLinearMap.comp_apply,map_add,expressionOffset]
  | mul a b ha hb => exact False.elim he
  | maximum a b ha hb =>
      rw [stoppingExpr_maximum]
      simp only [expressionKernel,expressionOffset]
      split_ifs <;> first | exact ha he.1 | exact hb he.2

def channelValue (v : ℝ × ℝ) (b : Bool) : ℝ := if b then v.2 else v.1

def streamValue {n} (x : PairVec n) (j : Fin n) (b : Bool) : ℝ :=
  if b then x.2 j else x.1 j

theorem channelValue_add (v w : ℝ × ℝ) (b : Bool) :
    channelValue (v+w) b=channelValue v b+channelValue w b := by cases b <;> rfl

theorem local_value_recovery {n} (k x : PairVec n) (hk : 0≤k) (turn : Bool) :
    (∑ i : Fin n,∑ b : Bool,
      localDiscount k*localProbability k (some (i,b))*streamValue x i (Bool.xor turn b)) =
      channelValue (kernelMap k x) turn := by
  simp_rw [local_discount_recovery k hk]
  cases turn <;> simp [Fintype.sum_bool,streamValue,channelValue,kernelMap_apply,
    coefficientRow_apply,Finset.sum_add_distrib,add_comm]

/-- Realized discounted payoff along a complete trajectory. Every selected
constant contributes its actual signed bias pair before cemetery termination.
Input leaves pay the corresponding input stream. -/
def pathPayoff {d n} : (c : Circuit d n) → PairVec d → Fin n → Bool → DAGPaths c → ℝ
  | .inputs, x, j, turn, _ => streamValue x j turn
  | .node prior op, x, j, turn, path =>
      Fin.lastCases
        (let b := channelValue (expressionOffset op (stoppingCircuit prior x)) turn
         match path with
         | .inr (.inl ((i,p),rest)) => b+
             localDiscount (expressionKernel op (stoppingCircuit prior x))*
               pathPayoff prior x i (Bool.xor turn p) rest
         | _ => b)
        (fun i => match path with
         | .inl rest => pathPayoff prior x i turn rest
         | _ => 0) j

def expectedPayoff {d n} (c : Circuit d n) (x : PairVec d) (j : Fin n) (turn : Bool) : ℝ :=
  ∑ path : DAGPaths c,pathProbability c x j path*pathPayoff c x j turn path

theorem expectedPayoff_node {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (x : PairVec d) (turn : Bool) :
    expectedPayoff (.node prior op) x (Fin.last n) turn =
      channelValue (expressionOffset op (stoppingCircuit prior x)) turn+
      ∑ i : Fin n,∑ b : Bool,
        localDiscount (expressionKernel op (stoppingCircuit prior x))*
          localProbability (expressionKernel op (stoppingCircuit prior x)) (some (i,b))*
          expectedPayoff prior x i (Bool.xor turn b) := by
  let k := expressionKernel op (stoppingCircuit prior x)
  let z := channelValue (expressionOffset op (stoppingCircuit prior x)) turn
  unfold expectedPayoff
  rw [sum_paths_node]
  simp only [pathProbability,pathPayoff,Fin.lastCases_last,zero_mul,Finset.sum_const_zero,zero_add]
  change (∑ i : Fin n,∑ b : Bool,∑ rest : DAGPaths prior,
      (localProbability k (some (i,b))*pathProbability prior x i rest)*
        (z+localDiscount k*pathPayoff prior x i (Bool.xor turn b) rest))+
      localProbability k none*z = _
  simp_rw [show ∀ a b c d e : ℝ,(a*b)*(c+d*e)=a*c*b+(d*a)*(b*e) by intros; ring]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,pathProbability_normalized,mul_one]
  have h := localProbability_normalized k
  simp only [Fintype.sum_option,Fintype.sum_prod_type] at h
  simp_rw [← Finset.sum_mul]
  dsimp only [k,z] at h ⊢
  linear_combination channelValue (expressionOffset op (stoppingCircuit prior x)) turn * h

/-- The full normalized finite stopping-game interpreter recovers the actual
shared-circuit forward streams, including biases and zero-fan-in termination. -/
theorem expectedPayoff_eq_stoppingCircuit {d n} (c : Circuit d n) (hc : c.Additive)
    (x : PairVec d) (j : Fin n) (turn : Bool) :
    expectedPayoff c x j turn=streamValue (stoppingCircuit c x) j turn := by
  induction c generalizing turn with
  | inputs => simp [expectedPayoff,DAGPaths,pathProbability,pathPayoff,stoppingCircuit]
  | @node n prior op ih =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [expectedPayoff_node]
        simp_rw [ih hc.1]
        rw [local_value_recovery _ _ (expressionKernel_nonnegative op hc.2 _)]
        have hf := congrArg (fun v => channelValue v turn)
          (stoppingExpr_affine op hc.2 (stoppingCircuit prior x))
        rw [channelValue_add] at hf
        simpa [streamValue,channelValue,stoppingCircuit,Fin.snoc,add_comm] using hf.symm
      · unfold expectedPayoff
        rw [sum_paths_node]
        simp only [pathProbability,pathPayoff,Fin.lastCases_castSucc,zero_mul,
          Finset.sum_const_zero,add_zero]
        simpa [expectedPayoff,streamValue,stoppingCircuit,Fin.snoc] using ih hc.1 i turn

end Thesis.StoppingDAG
