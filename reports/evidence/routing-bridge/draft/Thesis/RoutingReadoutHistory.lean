import Thesis.RoutingObservations
import Thesis.AffineOutputBackward

/-! A forced fair sign oracle for an ungated affine output. This interpreter
has no activation choice: both complete routing histories are retained, with
their separate outside/bias actions and the source entered-state discounts. -/
noncomputable section
namespace Thesis.RoutingReadoutHistory
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork
open Thesis.RoutingHistory Thesis.RoutingPolicyBridge Thesis.RoutingObservations
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

def positiveReadoutObservation {n m r : ℕ} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (ε : ℝ) (hε : 0≤ε) (x : Vec n)
    (mark : Fin n → Bool → ℝ) (u : Fin r) (q : Bool) :
    Observation (positiveReadout net C b ε hε x u q) :=
  routeObservation q ε (max (b u-(0 : Vec r) u) 0)
    (fun j => max (C u j-(0 : Matrix (Fin r) (Fin m) ℝ) u j) 0)
    (fun j => networkGame net ε hε x j q) hε (le_max_right _ _) (fun _ => le_max_right _ _)
    (fun j => networkObservation net ε hε x mark j q)

def negativeReadoutObservation {n m r : ℕ} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (ε : ℝ) (hε : 0≤ε) (x : Vec n)
    (mark : Fin n → Bool → ℝ) (u : Fin r) (q : Bool) :
    Observation (negativeReadout net C b ε hε x u q) :=
  routeObservation (!q) ε (max (-(b u-(0 : Vec r) u)) 0)
    (fun j => max (-(C u j-(0 : Matrix (Fin r) (Fin m) ℝ) u j)) 0)
    (fun j => networkGame net ε hε x j (!q)) hε (le_max_right _ _) (fun _ => le_max_right _ _)
    (fun j => networkObservation net ε hε x mark j (!q))

/-- The actual expectation over complete forced-oracle and backbone histories.
The endpoint mark records the actual input index and owner. -/
def readoutHistoryOccupation {n m r : ℕ} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hε : 0≤ε)
    (x : Vec n) (u : Fin r) (q : Bool) (i : Fin n) (owner : Bool) : ℝ :=
  forcedIntegral 1 α β (positiveReadout net C b ε hε x u q) (negativeReadout net C b ε hε x u q)
    (positiveReadoutObservation net C b ε hε x (fun a s => if a=i ∧ s=owner then 1 else 0) u q)
    (negativeReadoutObservation net C b ε hε x (fun a s => if a=i ∧ s=owner then 1 else 0) u q)

theorem readoutHistoryOccupation_eq_readoutOccupation {n m r : ℕ} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hε : 0≤ε)
    (x : Vec n) (hx : ∀ j,0≤net.eval x j) (u : Fin r) (q : Bool) (i : Fin n) (owner : Bool) :
    readoutHistoryOccupation net C b α β ε hε x u q i owner =
      readoutOccupation net C b α β ε x u i (Bool.xor q owner) := by
  unfold readoutHistoryOccupation
  rw [forcedIntegral_decomposition]
  unfold positiveReadout negativeReadout positiveReadoutObservation negativeReadoutObservation
  rw [canonicalIntegral_route, canonicalIntegral_route]
  change α*(∑ j, (layerPositive C 0 b 0 ε hε (networkGame net ε hε x) u q).prob j.succ.succ *
      networkOccupation net α β ε hε x j q i owner) +
    β*(∑ j, (layerNegative C 0 b 0 ε hε (networkGame net ε hε x) u q).prob j.succ.succ *
      networkOccupation net α β ε hε x j (!q) i owner) = _
  simp_rw [(layer_policy_probabilities C 0 b 0 ε hε (networkGame net ε hε x)
      (net.eval x) hx (networkGame_value net ε hε x) u q _).1,
    (layer_policy_probabilities C 0 b 0 ε hε (networkGame net ε hε x)
      (net.eval x) hx (networkGame_value net ε hε x) u q _).2,
    networkOccupation_eq_rgOccupation]
  simp only [readoutOccupation, readoutPos, readoutNeg, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases q <;> cases owner <;> simp <;> ring

/-- Complete alpha-beta recovery with the final affine operation ungated. -/
theorem affine_output_history_lrp {n m r : ℕ} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hε : 0≤ε)
    (x : Vec n) (hx : ∀ j,0≤net.eval x j) (R : Vec r) (i : Fin n) :
    affineOutputLRP net C b α β ε x R i = ∑ u, R u *
      (readoutHistoryOccupation net C b α β ε hε x u true i true -
       readoutHistoryOccupation net C b α β ε hε x u true i false) := by
  simp only [readoutHistoryOccupation_eq_readoutOccupation net C b α β ε hε x hx,
    Bool.true_xor, Bool.not_true, Bool.not_false]
  exact thesis_affine_output_lrp net C b α β ε x R i

/-- Any nonempty activated backbone permits signed raw input without an extra
output-positivity hypothesis. The final signed affine operation remains ungated. -/
theorem affine_output_layer_history_lrp {n k m r : ℕ}
    (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (tail : Network k m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hε : 0≤ε)
    (x : Vec n) (R : Vec r) (i : Fin n) :
    affineOutputLRP (Network.layer wp wn bp bn tail) C b α β ε x R i =
      ∑ u, R u *
        (readoutHistoryOccupation (Network.layer wp wn bp bn tail) C b α β ε hε x u true i true -
         readoutHistoryOccupation (Network.layer wp wn bp bn tail) C b α β ε hε x u true i false) := by
  apply affine_output_history_lrp
  exact eval_nonnegative tail _ (fun _ => le_max_right _ _)

/-- Nonnegative source discounts give a nonnegative occupation even at epsilon
zero, where empty streams are handled by the canonical outside action. -/
theorem readoutHistoryOccupation_nonnegative {n m r : ℕ} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ)
    (hα : 0≤α) (hβ : 0≤β) (hε : 0≤ε)
    (x : Vec n) (hx : ∀ j,0≤net.eval x j) (u : Fin r) (q : Bool) (i : Fin n) (owner : Bool) :
    0≤readoutHistoryOccupation net C b α β ε hε x u q i owner := by
  rw [readoutHistoryOccupation_eq_readoutOccupation net C b α β ε hε x hx]
  unfold readoutOccupation
  apply Finset.sum_nonneg
  intro j _
  apply add_nonneg
  · apply mul_nonneg
    · exact div_nonneg (mul_nonneg hα (le_max_right _ _))
        (Thesis.RoutingTransitions.posDenominator_nonnegative C 0 b 0 ε hε (net.eval x) u)
    · exact Thesis.RoutingTransitions.occupation_nonnegative net α β ε hα hβ hε x j i _
  · apply mul_nonneg
    · exact div_nonneg (mul_nonneg hβ (le_max_right _ _))
        (Thesis.RoutingTransitions.negDenominator_nonnegative C 0 b 0 ε hε (net.eval x) u)
    · exact Thesis.RoutingTransitions.occupation_nonnegative net α β ε hα hβ hε x j i _

end Thesis.RoutingReadoutHistory
