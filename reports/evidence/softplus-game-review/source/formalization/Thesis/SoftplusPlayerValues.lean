import Thesis.SoftplusEquilibrium

noncomputable section
namespace Thesis.SoftplusGame
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward
open Thesis.ReLUNetGame Thesis.RoutingBackward Matrix
open scoped BigOperators

abbrev PlayerValues (n : ℕ) := Bool → Bool → Vec n

def pairValues {n} (x : PairVec n) : PlayerValues n :=
  fun player turn => if player=turn then x.1 else x.2

def advantage {n} (v : PlayerValues n) : PairVec n :=
  (v false false-v true false,v false true-v true true)

def playerContinuation {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (v : PlayerValues n) (player turn : Bool) (j : Fin k) : ℝ :=
  continuation wp wn (if player=turn then bp else bn) (v player turn) (v player (!turn)) j

/-- The entropy bonus is credited only to the active player. Both players receive
their own bias/routed continuation reward under the controller's mixed action. -/
def playerStep {n k} (θ : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (plus minus : Fin k → Set.Icc (0 : ℝ) 1) (v : PlayerValues n) : PlayerValues k :=
  fun player turn j =>
    let r := if turn then (minus j).val else (plus j).val
    r*playerContinuation wp wn bp bn v player turn j+
      if player=turn then θ*Real.binEntropy r else 0

def playerValue {n m} (θ : ℝ) : (net : Network n m) → Strategy net → Strategy net →
    PlayerValues n → PlayerValues m
  | .output _, _, _, v => v
  | .layer wp wn bp bn tail, plus, minus, v =>
      playerValue θ tail plus.2 minus.2 (playerStep θ wp wn bp bn plus.1 minus.1 v)

theorem playerContinuation_advantage {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (bp bn : Vec k) (v : PlayerValues n)
    (turn : Bool) (j : Fin k) :
    playerContinuation wp wn bp bn v false turn j-playerContinuation wp wn bp bn v true turn j =
      if turn then continuation wn wp (bn-bp) (advantage v).1 (advantage v).2 j
      else continuation wp wn (bp-bn) (advantage v).1 (advantage v).2 j := by
  have hswap : ∀ j i,0≤wn j i ∧ 0≤wp j i := fun j i => ⟨(hw j i).2,(hw j i).1⟩
  cases turn <;>
    simp [playerContinuation,continuation_recovery_total wp wn hw,
      continuation_recovery_total wn wp hswap,advantage,Matrix.mulVec_sub] <;> ring

theorem playerStep_advantage {n k} (θ : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (bp bn : Vec k)
    (plus minus : Fin k → Set.Icc (0 : ℝ) 1) (v : PlayerValues n) :
    advantage (playerStep θ wp wn bp bn plus minus v) =
      (fun j => (plus j).val*continuation wp wn (bp-bn) (advantage v).1 (advantage v).2 j+
          θ*Real.binEntropy (plus j).val,
       fun j => (minus j).val*continuation wn wp (bn-bp) (advantage v).1 (advantage v).2 j-
          θ*Real.binEntropy (minus j).val) := by
  apply Prod.ext <;> funext j
  · have h := playerContinuation_advantage wp wn hw bp bn v false j
    simp only [Bool.false_eq_true,ite_false,advantage] at h
    simp [advantage,playerStep]
    linear_combination (plus j).val*h
  · have h := playerContinuation_advantage wp wn hw bp bn v true j
    simp only [ite_true,advantage] at h
    simp [advantage,playerStep]
    linear_combination (minus j).val*h

/-- All-profile bridge: the signed game really is the difference of the two
source player payoffs, including off-equilibrium entropy credits. -/
theorem playerValue_advantage {n m} (net : Network n m) (θ : ℝ) (hw : net.Nonnegative)
    (plus minus : Strategy net) (v : PlayerValues n) :
    advantage (playerValue θ net plus minus v)=
      policyValue θ net plus minus (advantage v).1 (advantage v).2 := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [playerValue]
      rw [ih hw.2.2,playerStep_advantage θ wp wn (fun j i => ⟨hw.1 j i,hw.2.1 j i⟩)]
      rfl

theorem advantage_pairValues {n} (x : PairVec n) : advantage (pairValues x)=(x.1-x.2,-(x.1-x.2)) := by
  simp [advantage,pairValues,neg_sub]

theorem playerContinuation_pair {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (bp bn : Vec k) (x : PairVec n)
    (player turn : Bool) (j : Fin k) :
    playerContinuation wp wn bp bn (pairValues x) player turn j =
      if player=turn then (preP wp wn x+bp) j else (preN wp wn x+bn) j := by
  cases player <;> cases turn <;>
    simp [playerContinuation,pairValues,continuation_recovery_total wp wn hw,preP_apply,preN,add_comm]

def softPairLayer {n k} (θ : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) : PairVec k :=
  (fun j => (softSplit θ ((preP wp wn x+bp) j) ((preN wp wn x+bn) j)).1,
   fun j => (softSplit θ ((preP wp wn x+bp) j) ((preN wp wn x+bn) j)).2)

theorem softPairLayer_recovery {n k} (θ : ℝ) (hθ : 0<θ)
    (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n) :
    (softPairLayer θ wp wn bp bn x).1-(softPairLayer θ wp wn bp bn x).2=
      softLayer θ wp wn bp bn (x.1-x.2) := by
  funext j
  rw [Pi.sub_apply,softPairLayer,softSplit_recovery θ _ _ hθ]
  congr 1
  exact congrFun (preactivation_difference wp wn bp bn x) j

theorem playerStep_gibbs {n k} (θ : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (bp bn : Vec k) (x : PairVec n) :
    playerStep θ wp wn bp bn
      (fun j => gibbsProbability θ (preactivation wp wn bp bn (x.1-x.2) j))
      (fun j => gibbsProbability θ (preactivation wp wn bp bn (x.1-x.2) j)) (pairValues x) =
      pairValues (softPairLayer θ wp wn bp bn x) := by
  funext player turn j
  have he := congrFun (preactivation_difference wp wn bp bn x) j
  change (preP wp wn x+bp) j-(preN wp wn x+bn) j=preactivation wp wn bp bn (x.1-x.2) j at he
  cases player <;> cases turn <;>
    simp [playerStep,playerContinuation_pair wp wn hw,pairValues,softPairLayer,softSplit,
      gibbsProbability,← he]

/-- Exact source player coordinates under the Gibbs equilibrium, for the actual
full varying-width MLP and its actual canonical Softplus pair decomposition. -/
theorem playerValue_gibbs {n m} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x : PairVec n) :
    playerValue θ net (gibbsStrategy θ net (x.1-x.2)) (gibbsStrategy θ net (x.1-x.2)) (pairValues x)=
      pairValues (net.decomposeWith (fun z => softSplit θ z.1 z.2) x) := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [playerValue,gibbsStrategy]
      rw [playerStep_gibbs θ wp wn (fun j i => ⟨hw.1 j i,hw.2.1 j i⟩)]
      rw [← softPairLayer_recovery θ hθ wp wn bp bn x]
      exact ih hw.2.2 (softPairLayer θ wp wn bp bn x)

end Thesis.SoftplusGame
