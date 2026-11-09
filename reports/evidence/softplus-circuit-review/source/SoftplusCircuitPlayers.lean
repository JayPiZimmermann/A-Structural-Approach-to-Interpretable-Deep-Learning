import Thesis.SoftplusCircuitEquilibrium

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.Regularization Thesis.StoppingCircuit Thesis.StoppingDAG
open Thesis.SoftplusGame (PlayerValues pairValues advantage)
open scoped BigOperators

def affinePlayer {n} (w : Vec n) (b : ℝ) (v : PlayerValues n) (player turn : Bool) : ℝ :=
  (if player=turn then max b 0 else max (-b) 0)+
    ∑ i,(max (w i) 0*v player turn i+max (-w i) 0*v player (!turn) i)

def nodePlayer {n e} (θ : ℝ) (spec : NodeSpec (n := n) e)
    (plus minus : NodePolicy spec) (v : PlayerValues n) (player turn : Bool) : ℝ :=
  match spec with
  | .affine w b => affinePlayer w b v player turn
  | .activation w b =>
      let r := if turn then minus.val else plus.val
      r*affinePlayer w b v player turn+(if player=turn then θ*Real.binEntropy r else 0)
  | .addition i j => v player turn i+v player turn j
  | .pool inputs =>
      let r := if turn then minus else plus
      ∑ i,r.prob i*v player turn (inputs i)

def playerValue {d n} (θ : ℝ) : (c : Circuit d n) → (plan : Plan c) →
    Strategy c plan → Strategy c plan → PlayerValues d → PlayerValues n
  | .inputs, _, _, _, x => x
  | .node prior _, plan, plus, minus, x =>
      let v := playerValue θ prior plan.1 plus.1 minus.1 x
      fun player turn => Fin.snoc (v player turn) (nodePlayer θ plan.2 plus.2 minus.2 v player turn)

theorem affinePlayer_advantage {n} (w : Vec n) (b : ℝ) (v : PlayerValues n) :
    (affinePlayer w b v false false-affinePlayer w b v true false,
     affinePlayer w b v false true-affinePlayer w b v true true)=affineSigned w b (advantage v) := by
  have hb := (canonical_weight_split b).1
  simp only [affinePlayer,affineSigned,kernelMap_apply,coefficientRow_apply,advantage]
  apply Prod.ext <;>
    simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_sub] <;> linarith

theorem nodePlayer_advantage {n e} (θ : ℝ) (spec : NodeSpec (n := n) e)
    (plus minus : NodePolicy spec) (v : PlayerValues n) :
    (nodePlayer θ spec plus minus v false false-nodePlayer θ spec plus minus v true false,
     nodePlayer θ spec plus minus v false true-nodePlayer θ spec plus minus v true true)=
      nodeSigned θ spec plus minus (advantage v) := by
  cases spec with
  | affine w b => exact affinePlayer_advantage w b v
  | activation w b =>
      have hp := congrArg Prod.fst (affinePlayer_advantage w b v)
      have hn := congrArg Prod.snd (affinePlayer_advantage w b v)
      apply Prod.ext <;> simp [nodePlayer,nodeSigned]
      · linear_combination plus.val*hp
      · linear_combination minus.val*hn
  | addition i j => apply Prod.ext <;> simp [nodePlayer,nodeSigned,advantage] <;> ring
  | pool inputs =>
      apply Prod.ext <;> simp [nodePlayer,nodeSigned,advantage,mul_sub,Finset.sum_sub_distrib]

/-- Off-equilibrium bridge for the full shared graph: the signed saddle model
is exactly the difference of the actual source player-specific payoffs. -/
theorem playerValue_advantage {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ)
    (plus minus : Strategy c plan) (v : PlayerValues d) :
    advantage (playerValue θ c plan plus minus v)=signedValue θ c plan plus minus (advantage v) := by
  induction c with
  | inputs => rfl
  | @node n prior op ih =>
      have hp := ih plan.1 plus.1 minus.1
      have hn := nodePlayer_advantage θ plan.2 plus.2 minus.2
        (playerValue θ prior plan.1 plus.1 minus.1 v)
      rw [hp] at hn
      apply Prod.ext <;> funext j <;> refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [advantage,playerValue,signedValue,Fin.snoc_last,Pi.sub_apply]
        exact congrArg Prod.fst hn
      · simpa only [advantage,playerValue,signedValue,Fin.snoc_castSucc,Pi.sub_apply]
          using congrFun (congrArg Prod.fst hp) i
      · simp only [advantage,playerValue,signedValue,Fin.snoc_last,Pi.sub_apply]
        exact congrArg Prod.snd hn
      · simpa only [advantage,playerValue,signedValue,Fin.snoc_castSucc,Pi.sub_apply]
          using congrFun (congrArg Prod.snd hp) i

theorem affinePlayer_pair {n} (w : Vec n) (b : ℝ) (x : PairVec n) (player turn : Bool) :
    affinePlayer w b (pairValues x) player turn =
      if player=turn then (stoppingExpr (SignedExpr.affine w b) x).1
      else (stoppingExpr (SignedExpr.affine w b) x).2 := by
  rw [stoppingExpr_affine _ (SignedExpr.affine_additive w b),expressionKernel_affine,expressionOffset_affine]
  cases player <;> cases turn <;>
    simp [affinePlayer,pairValues,kernelMap_apply,coefficientRow_apply,Finset.sum_add_distrib,add_comm]

theorem nodePlayer_canonical {n e} (θ : ℝ) (spec : NodeSpec (n := n) e) (x : PairVec n)
    (player turn : Bool) :
    nodePlayer θ spec (canonicalNode θ spec (x.1-x.2)) (canonicalNode θ spec (x.1-x.2))
      (pairValues x) player turn =
      if player=turn then (nodeSplit θ spec x).1 else (nodeSplit θ spec x).2 := by
  cases spec with
  | affine w b => exact affinePlayer_pair w b x player turn
  | activation w b =>
      have hz := stoppingExpr_recovery (SignedExpr.affine w b) x
      cases player <;> cases turn <;>
        simp [nodePlayer,canonicalNode,nodeSplit,affinePlayer_pair,softSplit,
          Thesis.SoftplusGame.gibbsProbability,hz]
  | addition i j => cases player <;> cases turn <;> simp [nodePlayer,nodeSplit,stoppingExpr,pairValues]
  | pool inputs =>
      have hk := (orderedInputPool_source inputs x).2.2.1
      cases player <;> cases turn <;>
        simp [nodePlayer,canonicalNode,nodeSplit,pairValues,Thesis.RoutingExtended.pure,hk]

/-- Actual source forward values on residual/maxpool Softplus DAGs, with every
player and owner coordinate retained and entropy credited only to its controller. -/
theorem playerValue_canonical {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0<θ)
    (x : PairVec d) :
    playerValue θ c plan (canonicalStrategy θ c plan (x.1-x.2))
      (canonicalStrategy θ c plan (x.1-x.2)) (pairValues x)=pairValues (graphSplit θ c plan x) := by
  induction c with
  | inputs => rfl
  | @node n prior op ih =>
      have hp := ih plan.1
      funext player turn j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [playerValue,canonicalStrategy,graphSplit,Fin.snoc_last,hp]
        rw [← graphSplit_recovery prior plan.1 θ hθ x,nodePlayer_canonical]
        cases player <;> cases turn <;> simp [pairValues]
      · have hh := congrFun (congrFun (congrFun hp player) turn) i
        cases player <;> cases turn <;>
          simpa [playerValue,canonicalStrategy,graphSplit,Fin.snoc,pairValues] using hh

end Thesis.SoftplusCircuit
