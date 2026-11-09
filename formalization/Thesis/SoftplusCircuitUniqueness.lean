import Thesis.SoftplusCircuitPlayers

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.Regularization Thesis.StoppingDAG
open scoped BigOperators

def HasNoPool {n e} : NodeSpec (n := n) e → Prop
  | .pool _ => False
  | _ => True

def NoPools {d n} : (c : Circuit d n) → Plan c → Prop
  | .inputs, _ => True
  | .node prior _, plan => NoPools prior plan.1 ∧ HasNoPool plan.2

theorem node_nash_unique {n e} (θ : ℝ) (hθ : 0<θ) (spec : NodeSpec (n := n) e)
    (hs : HasNoPool spec) (x : Vec n) (plus minus : NodePolicy spec)
    (hn : NodeNash θ spec plus minus (x,-x)) :
    plus=canonicalNode θ spec x ∧ minus=canonicalNode θ spec x := by
  cases spec with
  | affine w b => cases plus; cases minus; exact ⟨rfl,rfl⟩
  | addition i j => cases plus; cases minus; exact ⟨rfl,rfl⟩
  | pool inputs => exact False.elim hs
  | activation w b =>
      constructor
      · apply (Thesis.SoftplusGame.maximizesEntropy_iff θ _ hθ plus).mp
        intro a
        have h := hn.1 a
        simpa only [nodeSigned,affineSigned_original] using h
      · apply (Thesis.SoftplusGame.minimizesEntropy_neg_iff θ _ hθ minus).mp
        intro a
        have h := hn.2 a
        simpa only [nodeSigned,affineSigned_original] using h

/-- Source uniqueness on graphs without hard pools, including residual/addition
and ungated signed affine readouts. Every zero-fan-in activation still has the
unique positive-temperature entropy optimizer. -/
theorem subgamePerfect_iff {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0<θ)
    (hc : NoPools c plan) (x : Vec d) (plus minus : Strategy c plan) :
    SubgamePerfect θ c plan plus minus (x,-x) ↔
      plus=canonicalStrategy θ c plan x ∧ minus=canonicalStrategy θ c plan x := by
  constructor
  · intro hn
    induction c with
    | inputs => cases plus; cases minus; exact ⟨rfl,rfl⟩
    | node prior op ih =>
        have hp := ih plan.1 hc.1 plus.1 minus.1 hn.1
        have hh := hn.2
        rw [hp.1,hp.2,canonical_value prior plan.1 θ hθ x] at hh
        have hq := node_nash_unique θ hθ plan.2 hc.2 _ plus.2 minus.2 hh
        exact ⟨Prod.ext hp.1 hq.1,Prod.ext hp.2 hq.2⟩
  · rintro ⟨rfl,rfl⟩
    exact canonical_spne c plan θ hθ x

/-- Joint forward statement for the original shared Circuit, its actual
arbitrary-profile game, and both player-specific decomposition streams. -/
theorem softplus_forward_spne {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ)
    (hθ : 0<θ) (x : PairVec d) :
    SubgamePerfect θ c plan (canonicalStrategy θ c plan (x.1-x.2))
      (canonicalStrategy θ c plan (x.1-x.2)) (x.1-x.2,-(x.1-x.2)) ∧
    playerValue θ c plan (canonicalStrategy θ c plan (x.1-x.2))
      (canonicalStrategy θ c plan (x.1-x.2)) (Thesis.SoftplusGame.pairValues x)=
        Thesis.SoftplusGame.pairValues (graphSplit θ c plan x) ∧
    (graphSplit θ c plan x).1-(graphSplit θ c plan x).2=graphSoft θ c plan (x.1-x.2) :=
  ⟨canonical_spne c plan θ hθ _,playerValue_canonical c plan θ hθ x,
    graphSplit_recovery c plan θ hθ x⟩

end Thesis.SoftplusCircuit
