import Thesis.SoftplusCircuitTransition
import Thesis.SoftplusCircuitPaths

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.StoppingDAG
open Thesis.SoftplusGame (PlayerValues)
open scoped BigOperators

/-- Complete-trajectory payoff with predictable immediate rewards. Each reward
is the conditional expectation of the source split bias and entropy payment;
this also covers the lumped stop/zero-fan-in cemetery transition. -/
def pathPayoff {d n} (θ : ℝ) : (c : Circuit d n) → Plan c → Vec d → PlayerValues d → Bool → Fin n → Bool → DAGPaths c → ℝ
  | .inputs, _, _, v, player, j, turn, _ => v player turn j
  | .node prior op, plan, x, v, player, j, turn, path =>
      Fin.lastCases
        (let b := nodeReward θ plan.2 (graphSoft θ prior plan.1 x) player turn
         match path with
         | .inr (.inl ((i,p),rest)) => b+
             nodeDiscount plan.2 (graphSoft θ prior plan.1 x)*
               pathPayoff θ prior plan.1 x v player i (Bool.xor turn p) rest
         | _ => b)
        (fun i => match path with
         | .inl rest => pathPayoff θ prior plan.1 x v player i turn rest
         | _ => 0) j

def expectedPayoff {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) (v : PlayerValues d) (player : Bool) (j : Fin n) (turn : Bool) : ℝ :=
  ∑ path : DAGPaths c,pathProbability θ c plan x j path*pathPayoff θ c plan x v player j turn path

theorem expectedPayoff_node {d n} (prior : Circuit d n) (op : SignedExpr (Fin n))
    (plan : Plan (.node prior op)) (θ : ℝ) (x : Vec d) (v : PlayerValues d) (player : Bool) (turn : Bool) :
    expectedPayoff (.node prior op) plan θ x v player (Fin.last n) turn =
      nodeReward θ plan.2 (graphSoft θ prior plan.1 x) player turn+
      ∑ i : Fin n,∑ b : Bool,
        nodeDiscount plan.2 (graphSoft θ prior plan.1 x)*
          nodeProbability θ plan.2 (graphSoft θ prior plan.1 x) (some (i,b))*
          expectedPayoff prior plan.1 θ x v player i (Bool.xor turn b) := by
  let z := nodeReward θ plan.2 (graphSoft θ prior plan.1 x) player turn
  unfold expectedPayoff
  rw [sum_paths_node]
  simp only [pathProbability,pathPayoff,Fin.lastCases_last,zero_mul,Finset.sum_const_zero,zero_add]
  change (∑ i : Fin n,∑ b : Bool,∑ rest : DAGPaths prior,
      (nodeProbability θ plan.2 (graphSoft θ prior plan.1 x) (some (i,b))*pathProbability θ prior plan.1 x i rest)*
        (z+nodeDiscount plan.2 (graphSoft θ prior plan.1 x)*pathPayoff θ prior plan.1 x v player i (Bool.xor turn b) rest))+
      nodeProbability θ plan.2 (graphSoft θ prior plan.1 x) none*z = _
  simp_rw [show ∀ a b c d e : ℝ,(a*b)*(c+d*e)=a*c*b+(d*a)*(b*e) by intros; ring]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,pathProbability_normalized,mul_one]
  have h := nodeProbability_normalized θ plan.2 (graphSoft θ prior plan.1 x)
  simp only [Fintype.sum_option,Fintype.sum_prod_type] at h
  simp_rw [← Finset.sum_mul]
  dsimp only [z] at h ⊢
  linear_combination nodeReward θ plan.2 (graphSoft θ prior plan.1 x) player turn * h

/-- The full normalized finite trajectory interpreter equals the actual
canonical source player's recursive expected payoff, for all four coordinates. -/
theorem expectedPayoff_eq_playerValue {d n} (c : Circuit d n) (plan : Plan c)
    (θ : ℝ) (x : Vec d) (v : PlayerValues d) (player : Bool) (j : Fin n) (turn : Bool) :
    expectedPayoff c plan θ x v player j turn=
      playerValue θ c plan (canonicalStrategy θ c plan x)
        (canonicalStrategy θ c plan x) v player turn j := by
  induction c generalizing turn with
  | inputs => simp [expectedPayoff,DAGPaths,pathProbability,pathPayoff,playerValue]
  | @node n prior op ih =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [expectedPayoff_node]
        simp_rw [ih]
        simp only [playerValue,canonicalStrategy,Fin.snoc_last]
        exact (nodePlayer_transition θ plan.2 _ _ player turn).symm
      · unfold expectedPayoff
        rw [sum_paths_node]
        simp only [pathProbability,pathPayoff,Fin.lastCases_castSucc,zero_mul,
          Finset.sum_const_zero,add_zero]
        simpa [expectedPayoff,playerValue,canonicalStrategy,Fin.snoc] using ih plan.1 i turn

theorem expectedPayoff_eq_split {d n} (c : Circuit d n) (plan : Plan c)
    (θ : ℝ) (hθ : 0<θ) (x : PairVec d) (player turn : Bool) (j : Fin n) :
    expectedPayoff c plan θ (x.1-x.2) (Thesis.SoftplusGame.pairValues x) player j turn =
      if player=turn then (graphSplit θ c plan x).1 j else (graphSplit θ c plan x).2 j := by
  rw [expectedPayoff_eq_playerValue,playerValue_canonical c plan θ hθ x]
  cases player <;> cases turn <;> rfl

end Thesis.SoftplusCircuit
