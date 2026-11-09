import Thesis.SoftplusCircuitPlayers
import Thesis.SoftplusCircuitRows

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.Regularization Thesis.StoppingDAG
open Thesis.SoftplusGame (PlayerValues)
open scoped BigOperators

def nodeReward {n e} (θ : ℝ) (spec : NodeSpec (n := n) e) (x : Vec n)
    (player turn : Bool) : ℝ :=
  match spec with
  | .affine _ b => if player=turn then max b 0 else max (-b) 0
  | .activation w b =>
      let r := gate θ ((SignedExpr.affine w b).eval x)
      r*(if player=turn then max b 0 else max (-b) 0)+
        if player=turn then θ*Real.binEntropy r else 0
  | .addition _ _ => 0
  | .pool _ => 0

theorem node_expected_value {n e} (θ : ℝ) (spec : NodeSpec (n := n) e) (x : Vec n)
    (v : Bool → Vec n) (turn : Bool) :
    (∑ i : Fin n,∑ b : Bool,nodeDiscount spec x*nodeProbability θ spec x (some (i,b))*
      v (Bool.xor turn b) i)=
      ∑ i,((selectedWeights θ spec x).1 i*v turn i+
        (selectedWeights θ spec x).2 i*v (!turn) i) := by
  simp_rw [node_discount_recovery]
  cases turn <;> simp [Fintype.sum_bool,Finset.sum_add_distrib,add_comm]

/-- Source stochastic Bellman equation for every player and owner at the
canonical profile: structural discount, continuation-scaled split bias, and
controller-only entropy. Affine outputs remain ungated. -/
theorem nodePlayer_transition {n e} (θ : ℝ) (spec : NodeSpec (n := n) e) (x : Vec n)
    (v : PlayerValues n) (player turn : Bool) :
    nodePlayer θ spec (canonicalNode θ spec x) (canonicalNode θ spec x) v player turn=
      nodeReward θ spec x player turn+
      ∑ i : Fin n,∑ b : Bool,nodeDiscount spec x*nodeProbability θ spec x (some (i,b))*
        v player (Bool.xor turn b) i := by
  rw [node_expected_value]
  cases spec with
  | affine w b =>
      simp [nodePlayer,nodeReward,affinePlayer,selectedWeights,continuationProbability,
        nodeWeights,baseExpr,expressionKernel_affine]
  | activation w b =>
      simp only [nodePlayer,nodeReward,canonicalNode,Thesis.SoftplusGame.gibbsProbability,
        selectedWeights,continuationProbability,nodeWeights,baseExpr,expressionKernel_affine]
      cases turn <;> simp [affinePlayer,Finset.mul_sum,mul_add,Finset.sum_add_distrib,mul_assoc] <;> ring
  | addition i j =>
      simp [nodePlayer,nodeReward,selectedWeights,continuationProbability,nodeWeights,
        baseExpr,expressionKernel,Pi.single_apply,Finset.sum_add_distrib,add_mul]
  | pool inputs =>
      have hk := (orderedInputPool_source inputs (x,0)).2.2.2
      simp only [Pi.zero_apply,sub_zero] at hk
      cases turn <;> simp [nodePlayer,nodeReward,canonicalNode,selectedWeights,continuationProbability,
        nodeWeights,baseExpr,hk,Thesis.RoutingExtended.pure,Pi.single_apply]

end Thesis.SoftplusCircuit
