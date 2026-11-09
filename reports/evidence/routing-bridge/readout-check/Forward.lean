import Thesis.RoutingPolicyBridge
import Thesis.AffineOutputBackward

/-! A forced fair sign oracle for an ungated affine output. This interpreter
has no activation choice: both complete routing histories are retained, with
their separate outside/bias actions and the source entered-state discounts. -/
noncomputable section
namespace Thesis.RoutingReadoutHistory
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork
open Thesis.RoutingHistory Thesis.RoutingPolicyBridge
open Thesis.RoutingBackward Thesis.AffineOutputBackward
open scoped BigOperators

abbrev ForcedHistories (positive negative : Tree) := Histories positive ⊕ Histories negative

def forcedProbability (θ : ℝ) (positive negative : Tree) :
    ForcedHistories positive negative → ℝ
  | .inl h => (1/2)*probability positive (canonical θ positive) (canonical θ positive) h
  | .inr h => (1/2)*probability negative (canonical θ negative) (canonical θ negative) h

theorem forcedProbability_nonnegative (θ : ℝ) (positive negative : Tree)
    (h : ForcedHistories positive negative) :
    0≤forcedProbability θ positive negative h := by
  cases h with
  | inl h => exact mul_nonneg (by norm_num) (probability_nonnegative _ _ _ h)
  | inr h => exact mul_nonneg (by norm_num) (probability_nonnegative _ _ _ h)

theorem forcedProbability_normalized (θ : ℝ) (positive negative : Tree) :
    (∑ h : ForcedHistories positive negative,forcedProbability θ positive negative h)=1 := by
  rw [Fintype.sum_sum_type]
  simp only [forcedProbability, ← Finset.mul_sum, probability_normalized]
  norm_num

def forcedReturn (α β : ℝ) (positive negative : Tree)
    (positiveObs : Observation positive) (negativeObs : Observation negative) :
    ForcedHistories positive negative → ℝ
  | .inl h => (2*α)*pathReturn α β positive positiveObs h
  | .inr h => (2*β)*pathReturn α β negative negativeObs h

def forcedIntegral (θ α β : ℝ) (positive negative : Tree)
    (positiveObs : Observation positive) (negativeObs : Observation negative) : ℝ :=
  ∑ h : ForcedHistories positive negative,
    forcedProbability θ positive negative h * forcedReturn α β positive negative positiveObs negativeObs h

theorem forcedIntegral_decomposition (θ α β : ℝ) (positive negative : Tree)
    (positiveObs : Observation positive) (negativeObs : Observation negative) :
    forcedIntegral θ α β positive negative positiveObs negativeObs =
      α*canonicalIntegral θ α β positive positiveObs +
      β*canonicalIntegral θ α β negative negativeObs := by
  unfold forcedIntegral
  rw [Fintype.sum_sum_type]
  simp only [forcedProbability, forcedReturn, canonicalIntegral, integral, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

def positiveReadout {n m r : ℕ} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (ε : ℝ) (hε : 0≤ε) (x : Vec n) (u : Fin r) (q : Bool) : Tree :=
  route q ε (max (b u-(0 : Vec r) u) 0)
    (fun j => max (C u j-(0 : Matrix (Fin r) (Fin m) ℝ) u j) 0)
    (fun j => networkGame net ε hε x j q) hε (le_max_right _ _) (fun _ => le_max_right _ _)

def negativeReadout {n m r : ℕ} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (ε : ℝ) (hε : 0≤ε) (x : Vec n) (u : Fin r) (q : Bool) : Tree :=
  route (!q) ε (max (-(b u-(0 : Vec r) u)) 0)
    (fun j => max (-(C u j-(0 : Matrix (Fin r) (Fin m) ℝ) u j)) 0)
    (fun j => networkGame net ε hε x j (!q)) hε (le_max_right _ _) (fun _ => le_max_right _ _)

/-- The two ungated route subgames recover the signed affine logit, including
its bias. Equal stabilizers in the two streams cancel in the forward value. -/
theorem readout_forward {n m r : ℕ} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (ε : ℝ) (hε : 0≤ε)
    (x : Vec n) (hx : ∀ j,0≤net.eval x j) (u : Fin r) (q : Bool) :
    value 1 (positiveReadout net C b ε hε x u q) +
      value 1 (negativeReadout net C b ε hε x u q) =
      signed q (affineOutput net C b x u) := by
  have h := layerGames_continuation C 0 b 0 ε hε (networkGame net ε hε x)
    (net.eval x) hx (networkGame_value net ε hε x) u q
  change signed q (value 1 (positiveReadout net C b ε hε x u q) +
    value 1 (negativeReadout net C b ε hε x u q)) = _ at h
  have hs := congrArg (signed q) h
  simpa [signed_involutive, preactivation, affineOutput] using hs

end Thesis.RoutingReadoutHistory
