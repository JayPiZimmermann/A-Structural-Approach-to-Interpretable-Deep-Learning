import Thesis.RoutingProfiles
import Thesis.RoutingBackward

/-! The finite source game instantiated from the shared varying-width network.
Every routing node includes separate outside and bias actions. The first layer
splits the actual products x_i W_ij, so signed raw inputs are allowed. Later
layers route nonnegative activation values through signed weight streams. -/
noncomputable section
namespace Thesis.RoutingNetwork
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward
open Thesis.RoutingProfiles Thesis.RoutingExtended

def continuationMass (θ : ℝ) : Tree → ℝ
  | .activation q p n => signed q (value θ p + value θ n)
  | _ => 0

def extend {n : ℕ} {X : Type*} (outside bias : X) (ordinary : Fin n → X) : Fin (n+2) → X :=
  Fin.cases outside (Fin.cases bias ordinary)

theorem sum_extend {n} (outside bias : ℝ) (ordinary : Fin n → ℝ) :
    (∑ i, extend outside bias ordinary i) = outside + (bias + ∑ i, ordinary i) := by
  simp [extend, Fin.sum_univ_succ]

theorem extend_nonnegative {n} (outside bias : ℝ) (ordinary : Fin n → ℝ)
    (ho : 0 ≤ outside) (hb : 0 ≤ bias) (hw : ∀ i, 0 ≤ ordinary i) :
    ∀ i, 0 ≤ extend outside bias ordinary i := Fin.cases ho (Fin.cases hb hw)

def route {n} (q : Bool) (ε b : ℝ) (w : Fin n → ℝ) (child : Fin n → Tree)
    (hε : 0 ≤ ε) (hb : 0 ≤ b) (hw : ∀ i, 0 ≤ w i) : Tree :=
  .routing (n+2) q 0 (extend ε b w) (extend_nonnegative ε b w hε hb hw)
    (extend (.terminal (signed q 1)) (.terminal (signed q 1)) child)

theorem route_action_masses {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (ha : ∀ i, 0 ≤ a i)
    (hv : ∀ i, value 1 (child i) = signed q (a i)) :
    actionMass q (extend ε b w)
      (fun i => value 1 (extend (.terminal (signed q 1)) (.terminal (signed q 1)) child i)) =
      extend ε b (fun i => w i * a i) := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ ?_) i
  · simp [actionMass, extend, value, signed_involutive]
  · change b * max (signed q (value 1 (.terminal (signed q 1)))) 0 = b
    simp [value, signed_involutive]
  · intro j
    simp [actionMass, extend, hv, signed_involutive, max_eq_left (ha j)]

theorem route_anchor_value {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, value 1 (child i) = signed q (a i)) :
    value 1 (route q ε b w child hε hb hw) = signed q (ε + (b + ∑ i, w i * a i)) := by
  simp only [route, value, routingOperator, routingChoice]
  rw [gibbs_anchor_mass _ (actionMass_nonnegative q _ _ (extend_nonnegative ε b w hε hb hw)),
    route_action_masses q ε b w a child ha hv, sum_extend]

theorem route_anchor_ordinary_probability {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, value 1 (child i) = signed q (a i)) (i : Fin n) :
    (canonical 1 (route q ε b w child hε hb hw)).1.prob i.succ.succ =
      w i * a i / (ε + (b + ∑ j, w j * a j)) := by
  simp only [route, canonical, routingChoice]
  rw [gibbs_anchor_nonoutside _
    (actionMass_nonnegative q _ _ (extend_nonnegative ε b w hε hb hw)) 0 i.succ.succ
      (Fin.succ_ne_zero _), route_action_masses q ε b w a child ha hv, sum_extend]
  rfl

theorem signed_opponent (q : Bool) (z : ℝ) : signed (!q) z = -signed q z := by
  cases q <;> simp [signed]

theorem signed_difference (q : Bool) (p n : ℝ) :
    signed q p + signed (!q) n = signed q (p-n) := by
  cases q <;> simp [signed] <;> ring

theorem gateValue_signed (q : Bool) (z : ℝ) : gateValue q (signed q z) = signed q (relu z) := by
  simp only [gateValue, signed_involutive]
  have h := Thesis.RoutingGate.chosenLogAction_mass z
  cases q
  · by_cases hg : Thesis.RoutingGate.chosenLogAction z = true
    · simpa [signed, hg, relu] using congrArg Neg.neg h
    · simpa [signed, hg, relu] using congrArg Neg.neg h
  · exact h

theorem activation_anchor_value (q : Bool) (positive negative : Tree) (P N : ℝ)
    (hp : value 1 positive = signed q P) (hn : value 1 negative = signed (!q) N) :
    value 1 (.activation q positive negative) = signed q (relu (P-N)) := by
  simp only [value, hp, hn, signed_difference, gateValue_signed]

theorem denominator_difference {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (x : Vec n) (j : Fin k) :
    posDenominator wp wn bp bn ε x j - negDenominator wp wn bp bn ε x j =
      preactivation wp wn bp bn x j := by
  have hs : (∑ i, posContribution wp wn x j i) - (∑ i, negContribution wp wn x j i) =
      ∑ i, x i * (wp j i - wn j i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact positive_parts_difference _
  unfold posDenominator negDenominator
  have hb := positive_parts_difference (bp j - bn j)
  change _ = (∑ i, (wp j i - wn j i) * x i) + (bp j - bn j)
  have hcomm : (∑ i, x i * (wp j i - wn j i)) = ∑ i, (wp j i - wn j i) * x i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

def inputLayerGames {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool) : Tree :=
  .activation q
    (route q ε (max (bp j-bn j) 0) (posContribution wp wn x j)
      (fun _ => .terminal (signed q 1)) hε (le_max_right _ _) (fun _ => le_max_right _ _))
    (route (!q) ε (max (-(bp j-bn j)) 0) (negContribution wp wn x j)
      (fun _ => .terminal (signed (!q) 1)) hε (le_max_right _ _) (fun _ => le_max_right _ _))

theorem inputLayerGames_value {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool) :
    value 1 (inputLayerGames wp wn bp bn ε hε x j q) =
      signed q (relu (preactivation wp wn bp bn x j)) := by
  have hp := route_anchor_value q ε (max (bp j-bn j) 0) (posContribution wp wn x j)
    (fun _ => 1) (fun _ => .terminal (signed q 1)) hε (le_max_right _ _)
    (fun _ => le_max_right _ _) (fun _ => zero_le_one) (fun _ => rfl)
  have hn := route_anchor_value (!q) ε (max (-(bp j-bn j)) 0) (negContribution wp wn x j)
    (fun _ => 1) (fun _ => .terminal (signed (!q) 1)) hε (le_max_right _ _)
    (fun _ => le_max_right _ _) (fun _ => zero_le_one) (fun _ => rfl)
  simp only [mul_one] at hp hn
  have hpden : ε + (max (bp j-bn j) 0 + ∑ i, posContribution wp wn x j i) =
      posDenominator wp wn bp bn ε x j := by unfold posDenominator; ring
  have hnden : ε + (max (-(bp j-bn j)) 0 + ∑ i, negContribution wp wn x j i) =
      negDenominator wp wn bp bn ε x j := by unfold negDenominator; ring
  rw [hpden] at hp
  rw [hnden] at hn
  change value 1 (.activation q _ _) = _
  rw [activation_anchor_value q _ _ _ _ hp hn, denominator_difference]

def layerGames {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree) (j : Fin k) (q : Bool) : Tree :=
  .activation q
    (route q ε (max (bp j-bn j) 0) (fun i => max (wp j i-wn j i) 0)
      (fun i => input i q) hε (le_max_right _ _) (fun _ => le_max_right _ _))
    (route (!q) ε (max (-(bp j-bn j)) 0) (fun i => max (-(wp j i-wn j i)) 0)
      (fun i => input i (!q)) hε (le_max_right _ _) (fun _ => le_max_right _ _))

theorem layerGames_value {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree) (x : Vec n)
    (hx : ∀ i, 0 ≤ x i) (hv : ∀ i q, value 1 (input i q) = signed q (x i))
    (j : Fin k) (q : Bool) :
    value 1 (layerGames wp wn bp bn ε hε input j q) =
      signed q (relu (preactivation wp wn bp bn x j)) := by
  have hp := route_anchor_value q ε (max (bp j-bn j) 0) (fun i => max (wp j i-wn j i) 0)
    x (fun i => input i q) hε (le_max_right _ _) (fun _ => le_max_right _ _) hx (fun i => hv i q)
  have hn := route_anchor_value (!q) ε (max (-(bp j-bn j)) 0) (fun i => max (-(wp j i-wn j i)) 0)
    x (fun i => input i (!q)) hε (le_max_right _ _) (fun _ => le_max_right _ _) hx (fun i => hv i (!q))
  have hpos (i : Fin n) : max (wp j i-wn j i) 0 * x i = posContribution wp wn x j i := by
    rw [max_mul_of_nonneg _ _ (hx i)]
    simp [posContribution, mul_comm]
  have hneg (i : Fin n) : max (-(wp j i-wn j i)) 0 * x i = negContribution wp wn x j i := by
    rw [max_mul_of_nonneg _ _ (hx i)]
    unfold negContribution
    congr 1 <;> ring
  simp_rw [hpos] at hp
  simp_rw [hneg] at hn
  have hpden : ε + (max (bp j-bn j) 0 + ∑ i, posContribution wp wn x j i) =
      posDenominator wp wn bp bn ε x j := by unfold posDenominator; ring
  have hnden : ε + (max (-(bp j-bn j)) 0 + ∑ i, negContribution wp wn x j i) =
      negDenominator wp wn bp bn ε x j := by unfold negDenominator; ring
  rw [hpden] at hp
  rw [hnden] at hn
  change value 1 (.activation q _ _) = _
  rw [activation_anchor_value q _ _ _ _ hp hn, denominator_difference]

def propagate (ε : ℝ) (hε : 0 ≤ ε) : {n m : ℕ} → Network n m → (Fin n → Bool → Tree) →
    Fin m → Bool → Tree
  | _, _, .output _, input => input
  | _, _, .layer wp wn bp bn tail, input =>
      propagate ε hε tail (layerGames wp wn bp bn ε hε input)

theorem propagate_value {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (input : Fin n → Bool → Tree) (x : Vec n) (hx : ∀ i, 0 ≤ x i)
    (hv : ∀ i q, value 1 (input i q) = signed q (x i)) (j : Fin m) (q : Bool) :
    value 1 (propagate ε hε net input j q) = signed q (net.eval x j) := by
  induction net with
  | output n => exact hv j q
  | layer wp wn bp bn tail ih =>
      exact ih (layerGames wp wn bp bn ε hε input)
        (fun j => relu (preactivation wp wn bp bn x j))
        (fun _ => le_max_right _ _) (layerGames_value wp wn bp bn ε hε input x hx hv) j

def networkGame {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) : Fin m → Bool → Tree :=
  match net with
  | .output _ => fun j q => .terminal (signed q (x j))
  | .layer wp wn bp bn tail => propagate ε hε tail (inputLayerGames wp wn bp bn ε hε x)

/-- Forward equivalence from the actual signed weights, biases and raw inputs at tau=1. -/
theorem networkGame_value {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool) :
    value 1 (networkGame net ε hε x j q) = signed q (net.eval x j) := by
  cases net with
  | output n => rfl
  | layer wp wn bp bn tail =>
      exact propagate_value tail ε hε (inputLayerGames wp wn bp bn ε hε x)
        (fun j => relu (preactivation wp wn bp bn x j)) (fun _ => le_max_right _ _)
        (inputLayerGames_value wp wn bp bn ε hε x) j q

/-- Source-log SPNE for every actual network game, with pure activation choices and arbitrary routing policies. -/
theorem networkGame_subgame_perfect {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin m) (q : Bool) :
    IsSubgamePerfect θ (networkGame net ε hε x j q) (canonical θ (networkGame net ε hε x j q)) :=
  canonical_subgame_perfect θ hθ _

/-- Actual reported source coordinates at the anchor, derived from the all-profile model bridge. -/
theorem networkGame_reported {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool) :
    reported 1 (networkGame net ε hε x j q)
      (canonical 1 (networkGame net ε hε x j q)) (canonical 1 (networkGame net ε hε x j q)) =
      (Thesis.RoutingGate.logCoordinate (signed q (net.eval x j)),
       Thesis.RoutingGate.logCoordinate (-signed q (net.eval x j))) := by
  rw [reported_coordinates, canonical_value, networkGame_value]

/-- Nonnegative output activations have active-player log value and bottom opponent value. -/
theorem networkGame_nonnegative_reported {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool) (ha : 0 ≤ net.eval x j) :
    reported 1 (networkGame net ε hε x j q)
      (canonical 1 (networkGame net ε hε x j q)) (canonical 1 (networkGame net ε hε x j q)) =
      if q then (Thesis.RoutingGate.logCoordinate (net.eval x j), ⊥)
      else (⊥, Thesis.RoutingGate.logCoordinate (net.eval x j)) := by
  rw [networkGame_reported]
  cases q <;> simp [signed, Thesis.RoutingGate.logCoordinate_nonpositive _ (neg_nonpos.mpr ha)]

theorem eval_nonnegative {n m} (net : Network n m) (x : Vec n) (hx : ∀ i, 0 ≤ x i) :
    ∀ j, 0 ≤ net.eval x j := by
  induction net with
  | output n => exact hx
  | layer wp wn bp bn tail ih => exact ih _ (fun _ => le_max_right _ _)

/-- For every network with an activation layer, raw inputs may be signed. -/
theorem networkLayer_reported {n k m} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (tail : Network k m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool) :
    reported 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q)
      (canonical 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q))
      (canonical 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q)) =
      if q then (Thesis.RoutingGate.logCoordinate ((Network.layer wp wn bp bn tail).eval x j), ⊥)
      else (⊥, Thesis.RoutingGate.logCoordinate ((Network.layer wp wn bp bn tail).eval x j)) :=
  networkGame_nonnegative_reported _ ε hε x j q
    (eval_nonnegative tail _ (fun _ => le_max_right _ _) j)

theorem inputLayerGames_continuation {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool) :
    continuationMass 1 (inputLayerGames wp wn bp bn ε hε x j q) =
      preactivation wp wn bp bn x j := by
  have hp := route_anchor_value q ε (max (bp j-bn j) 0) (posContribution wp wn x j)
    (fun _ => 1) (fun _ => .terminal (signed q 1)) hε (le_max_right _ _)
    (fun _ => le_max_right _ _) (fun _ => zero_le_one) (fun _ => rfl)
  have hn := route_anchor_value (!q) ε (max (-(bp j-bn j)) 0) (negContribution wp wn x j)
    (fun _ => 1) (fun _ => .terminal (signed (!q) 1)) hε (le_max_right _ _)
    (fun _ => le_max_right _ _) (fun _ => zero_le_one) (fun _ => rfl)
  simp only [mul_one] at hp hn
  have hpden : ε + (max (bp j-bn j) 0 + ∑ i, posContribution wp wn x j i) =
      posDenominator wp wn bp bn ε x j := by unfold posDenominator; ring
  have hnden : ε + (max (-(bp j-bn j)) 0 + ∑ i, negContribution wp wn x j i) =
      negDenominator wp wn bp bn ε x j := by unfold negDenominator; ring
  rw [hpden] at hp
  rw [hnden] at hn
  change signed q (value 1 _ + value 1 _) = _
  rw [hp, hn, signed_difference, signed_involutive, denominator_difference]

theorem layerGames_continuation {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree) (x : Vec n)
    (hx : ∀ i, 0 ≤ x i) (hv : ∀ i q, value 1 (input i q) = signed q (x i))
    (j : Fin k) (q : Bool) :
    continuationMass 1 (layerGames wp wn bp bn ε hε input j q) =
      preactivation wp wn bp bn x j := by
  have hp := route_anchor_value q ε (max (bp j-bn j) 0) (fun i => max (wp j i-wn j i) 0)
    x (fun i => input i q) hε (le_max_right _ _) (fun _ => le_max_right _ _) hx (fun i => hv i q)
  have hn := route_anchor_value (!q) ε (max (-(bp j-bn j)) 0) (fun i => max (-(wp j i-wn j i)) 0)
    x (fun i => input i (!q)) hε (le_max_right _ _) (fun _ => le_max_right _ _) hx (fun i => hv i (!q))
  have hpos (i : Fin n) : max (wp j i-wn j i) 0 * x i = posContribution wp wn x j i := by
    rw [max_mul_of_nonneg _ _ (hx i)]
    simp [posContribution, mul_comm]
  have hneg (i : Fin n) : max (-(wp j i-wn j i)) 0 * x i = negContribution wp wn x j i := by
    rw [max_mul_of_nonneg _ _ (hx i)]
    unfold negContribution
    congr 1 <;> ring
  simp_rw [hpos] at hp
  simp_rw [hneg] at hn
  have hpden : ε + (max (bp j-bn j) 0 + ∑ i, posContribution wp wn x j i) =
      posDenominator wp wn bp bn ε x j := by unfold posDenominator; ring
  have hnden : ε + (max (-(bp j-bn j)) 0 + ∑ i, negContribution wp wn x j i) =
      negDenominator wp wn bp bn ε x j := by unfold negDenominator; ring
  rw [hpden] at hp
  rw [hnden] at hn
  change signed q (value 1 _ + value 1 _) = _
  rw [hp, hn, signed_difference, signed_involutive, denominator_difference]

theorem inputLayerGames_selected_gate {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool) :
    (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)).1 =
      decide (0 < preactivation wp wn bp bn x j) := by
  change Thesis.RoutingGate.chosenLogAction
    (continuationMass 1 (inputLayerGames wp wn bp bn ε hε x j q)) = _
  rw [inputLayerGames_continuation, Thesis.RoutingGate.chosenLogAction_eq_positive]

theorem layerGames_selected_gate {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree) (x : Vec n)
    (hx : ∀ i, 0 ≤ x i) (hv : ∀ i q, value 1 (input i q) = signed q (x i))
    (j : Fin k) (q : Bool) :
    (canonical 1 (layerGames wp wn bp bn ε hε input j q)).1 =
      decide (0 < preactivation wp wn bp bn x j) := by
  change Thesis.RoutingGate.chosenLogAction
    (continuationMass 1 (layerGames wp wn bp bn ε hε input j q)) = _
  rw [layerGames_continuation wp wn bp bn ε hε input x hx hv,
    Thesis.RoutingGate.chosenLogAction_eq_positive]

end Thesis.RoutingNetwork
