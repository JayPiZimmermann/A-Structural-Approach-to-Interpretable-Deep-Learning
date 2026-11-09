import Thesis.RoutingExtended

/-! Finite unfolded source routing games. Activation choices are pure stop or
continue; routing choices are arbitrary finite probability distributions. The
auxiliary signed recursion will be identified with the difference of exponentiated
reported source coordinates, rather than replacing either player's log utility. -/
noncomputable section
namespace Thesis.RoutingProfiles
open Thesis.RoutingExtended

def signed (plus : Bool) (z : ℝ) : ℝ := if plus then z else -z

theorem signed_involutive (q : Bool) (z : ℝ) : signed q (signed q z) = z := by
  cases q <;> simp [signed]

def gateValue (q : Bool) (z : ℝ) : ℝ :=
  if Thesis.RoutingGate.chosenLogAction (signed q z) then z else 0

theorem gateValue_plus (z : ℝ) : gateValue true z = max z 0 := by
  exact Thesis.RoutingGate.chosenLogAction_mass z

theorem gateValue_minus (z : ℝ) : gateValue false z = min z 0 := by
  by_cases hz : z < 0
  · simp [gateValue, signed, Thesis.RoutingGate.chosenLogAction_eq_positive,
      hz, min_eq_left hz.le]
  · have hn : 0 ≤ z := le_of_not_gt hz
    simp [gateValue, signed, Thesis.RoutingGate.chosenLogAction_eq_positive,
      not_lt_of_ge hn, min_eq_right hn]

theorem gate_action_monotone (a : Bool) : Monotone (fun z : ℝ => if a then z else 0) := by
  intro z w h
  cases a
  · exact le_rfl
  · exact h

theorem gate_action_bound (q : Bool) (z : ℝ) (a : Bool) :
    signed q (if a then z else 0) ≤ signed q (gateValue q z) := by
  cases q <;> cases a <;> simp [signed, gateValue_plus, gateValue_minus]

def actionMass {n} (q : Bool) (w v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w i * max (signed q (v i)) 0

theorem actionMass_nonnegative {n} (q : Bool) (w v : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∀ i, 0 ≤ actionMass q w v i := fun i => mul_nonneg (hw i) (le_max_right _ _)

def routingOperator {n} (θ : ℝ) (q : Bool) (w : Fin n → ℝ)
    (p : Policy (Fin n)) (v : Fin n → ℝ) : ℝ :=
  signed q (routedMass θ (actionMass q w v) p)

theorem routingOperator_monotone {n} (θ : ℝ) (q : Bool) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (p : Policy (Fin n)) : Monotone (routingOperator θ q w p) := by
  intro v u hvu
  cases q
  · apply neg_le_neg
    apply routedMass_monotone θ p
    intro i
    exact mul_le_mul_of_nonneg_left (max_le_max (neg_le_neg (hvu i)) le_rfl) (hw i)
  · apply routedMass_monotone θ p
    intro i
    exact mul_le_mul_of_nonneg_left (max_le_max (hvu i) le_rfl) (hw i)

def routingChoice {n} (θ : ℝ) (q : Bool) (w : Fin n → ℝ)
    (outside : Fin n) (v : Fin n → ℝ) : Policy (Fin n) :=
  gibbs θ (actionMass q w v) outside

theorem routing_choice_bound {n} (θ : ℝ) (hθ : 0 < θ) (q : Bool)
    (w : Fin n → ℝ) (outside : Fin n) (v : Fin n → ℝ) (p : Policy (Fin n)) :
    signed q (routingOperator θ q w p v) ≤
      signed q (routingOperator θ q w (routingChoice θ q w outside v) v) := by
  simp only [routingOperator, signed_involutive]
  exact gibbs_optimal θ hθ _ outside p

inductive Tree where
  | terminal (mass : ℝ) : Tree
  | activation (owner : Bool) (positive negative : Tree) : Tree
  | routing (n : ℕ) (owner : Bool) (outside : Fin n)
      (weight : Fin n → ℝ) (nonnegative : ∀ i, 0 ≤ weight i) (child : Fin n → Tree) : Tree

/-- Full contingent choices, including choices at every off-path subgame. -/
def Strategy : Tree → Type
  | .terminal _ => Unit
  | .activation _ p n => Bool × Strategy p × Strategy n
  | .routing n _ _ _ _ c => Policy (Fin n) × ((i : Fin n) → Strategy (c i))

/-- The signed auxiliary evaluation under arbitrary player strategy profiles. -/
def auxiliary (θ : ℝ) : (t : Tree) → Strategy t → Strategy t → ℝ
  | .terminal z, _, _ => z
  | .activation q p n, plus, minus =>
      if (if q then plus.1 else minus.1) then
        auxiliary θ p plus.2.1 minus.2.1 + auxiliary θ n plus.2.2 minus.2.2 else 0
  | .routing _ q _ w _ c, plus, minus =>
      routingOperator θ q w (if q then plus.1 else minus.1)
        (fun i => auxiliary θ (c i) (plus.2 i) (minus.2 i))

def value (θ : ℝ) : Tree → ℝ
  | .terminal z => z
  | .activation q p n => gateValue q (value θ p + value θ n)
  | .routing _ q outside w _ c =>
      routingOperator θ q w (routingChoice θ q w outside (fun i => value θ (c i)))
        (fun i => value θ (c i))

/-- Canonical source policy: stop at every activation log tie, Gibbs at routing. -/
def canonical (θ : ℝ) : (t : Tree) → Strategy t
  | .terminal _ => ()
  | .activation q p n =>
      (Thesis.RoutingGate.chosenLogAction (signed q (value θ p + value θ n)),
        canonical θ p, canonical θ n)
  | .routing _ q outside w _ c =>
      (routingChoice θ q w outside (fun i => value θ (c i)), fun i => canonical θ (c i))

theorem canonical_value (θ : ℝ) (t : Tree) :
    auxiliary θ t (canonical θ t) (canonical θ t) = value θ t := by
  induction t with
  | terminal z => rfl
  | activation q p n hp hn => simp only [auxiliary, canonical, hp, hn, ite_self, value, gateValue]
  | routing n q outside w hw c ih =>
      simp only [auxiliary, canonical, ite_self, ih, value]

/-- Stronger signed saddle, proved for every off-equilibrium profile by monotone induction. -/
theorem auxiliary_saddle (θ : ℝ) (hθ : 0 < θ) (t : Tree) (plus minus : Strategy t) :
    auxiliary θ t plus (canonical θ t) ≤ value θ t ∧
      value θ t ≤ auxiliary θ t (canonical θ t) minus := by
  induction t with
  | terminal z => exact ⟨le_rfl, le_rfl⟩
  | activation q p n hp hn =>
      have hpl := (hp plus.2.1 minus.2.1).1
      have hnl := (hn plus.2.2 minus.2.2).1
      have hpr := (hp plus.2.1 minus.2.1).2
      have hnr := (hn plus.2.2 minus.2.2).2
      cases q
      · constructor
        · exact gate_action_monotone _ (add_le_add hpl hnl)
        · have h := gate_action_bound false (value θ p + value θ n) minus.1
          have hs := gate_action_monotone minus.1 (add_le_add hpr hnr)
          exact (neg_le_neg_iff.mp h).trans hs
      · constructor
        · have h := gate_action_bound true (value θ p + value θ n) plus.1
          have hs := gate_action_monotone plus.1 (add_le_add hpl hnl)
          exact hs.trans h
        · exact gate_action_monotone _ (add_le_add hpr hnr)
  | routing n q outside w hw c ih =>
      have hl : (fun i => auxiliary θ (c i) (plus.2 i) (canonical θ (c i))) ≤
          (fun i => value θ (c i)) := fun i => (ih i (plus.2 i) (minus.2 i)).1
      have hr : (fun i => value θ (c i)) ≤
          (fun i => auxiliary θ (c i) (canonical θ (c i)) (minus.2 i)) :=
        fun i => (ih i (plus.2 i) (minus.2 i)).2
      cases q
      · constructor
        · exact routingOperator_monotone θ false w hw _ hl
        · have h := routing_choice_bound θ hθ false w outside (fun i => value θ (c i)) minus.1
          exact (neg_le_neg_iff.mp h).trans (routingOperator_monotone θ false w hw minus.1 hr)
      · constructor
        · have h := routing_choice_bound θ hθ true w outside (fun i => value θ (c i)) plus.1
          exact (routingOperator_monotone θ true w hw plus.1 hl).trans h
        · exact routingOperator_monotone θ true w hw _ hr

/-- Source-reported coordinates are defined independently from the auxiliary payoff. -/
def reported (θ : ℝ) : (t : Tree) → Strategy t → Strategy t → WithBot ℝ × WithBot ℝ
  | .terminal z, _, _ => (Thesis.RoutingGate.logCoordinate z, Thesis.RoutingGate.logCoordinate (-z))
  | .activation q p n, plus, minus =>
      if (if q then plus.1 else minus.1) then
        let vp := reported θ p plus.2.1 minus.2.1
        let vn := reported θ n plus.2.2 minus.2.2
        let d := (expZero vp.1 - expZero vp.2) + (expZero vn.1 - expZero vn.2)
        (Thesis.RoutingGate.logCoordinate d, Thesis.RoutingGate.logCoordinate (-d))
      else (⊥,⊥)
  | .routing _ q _ w _ c, plus, minus =>
      let v := sourceValue θ (fun i => w i * expZero
        (if q then (reported θ (c i) (plus.2 i) (minus.2 i)).1
         else (reported θ (c i) (plus.2 i) (minus.2 i)).2))
        (if q then plus.1 else minus.1)
      if q then (v,⊥) else (⊥,v)

theorem positive_parts_difference (z : ℝ) : max z 0 - max (-z) 0 = z := by
  by_cases hz : 0 ≤ z
  · simp [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
  · have hn : z ≤ 0 := le_of_not_ge hz
    simp [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]

theorem routed_coordinates {n} (θ : ℝ) (q : Bool) (m : Fin n → ℝ) (p : Policy (Fin n)) :
    (if q then (sourceValue θ m p, (⊥ : WithBot ℝ)) else (⊥, sourceValue θ m p)) =
      (Thesis.RoutingGate.logCoordinate (signed q (routedMass θ m p)),
       Thesis.RoutingGate.logCoordinate (-signed q (routedMass θ m p))) := by
  have hn := neg_nonpos.mpr (routedMass_nonnegative θ m p)
  cases q <;> simp [signed, Thesis.RoutingGate.logCoordinate_nonpositive _ hn, log_routedMass]

/-- All-profile model bridge: reported source utility is ell of the signed auxiliary value. -/
theorem reported_coordinates (θ : ℝ) (t : Tree) (plus minus : Strategy t) :
    reported θ t plus minus =
      (Thesis.RoutingGate.logCoordinate (auxiliary θ t plus minus),
       Thesis.RoutingGate.logCoordinate (-auxiliary θ t plus minus)) := by
  induction t with
  | terminal z => rfl
  | activation q p n hp hn =>
      simp only [reported, auxiliary, hp, hn, expZero_logCoordinate, positive_parts_difference]
      split_ifs <;> simp [Thesis.RoutingGate.logCoordinate]
  | routing n q outside w hw c ih =>
      simp only [reported, auxiliary, ih, routingOperator]
      have hm : (fun i => w i * expZero
          (if q then Thesis.RoutingGate.logCoordinate (auxiliary θ (c i) (plus.2 i) (minus.2 i))
           else Thesis.RoutingGate.logCoordinate (-auxiliary θ (c i) (plus.2 i) (minus.2 i)))) =
          actionMass q w (fun i => auxiliary θ (c i) (plus.2 i) (minus.2 i)) := by
        funext i
        cases q <;> simp [actionMass, signed, expZero_logCoordinate]
      rw [hm]
      exact routed_coordinates θ q _ _

/-- The signed auxiliary payoff is derived from the two actual reported coordinates. -/
theorem auxiliary_eq_reported_difference (θ : ℝ) (t : Tree) (plus minus : Strategy t) :
    auxiliary θ t plus minus =
      expZero (reported θ t plus minus).1 - expZero (reported θ t plus minus).2 := by
  rw [reported_coordinates]
  simp [expZero_logCoordinate]

def IsNash (θ : ℝ) (t : Tree) (profile : Strategy t) : Prop :=
  (∀ plus, (reported θ t plus profile).1 ≤ (reported θ t profile profile).1) ∧
  (∀ minus, (reported θ t profile minus).2 ≤ (reported θ t profile profile).2)

/-- Nash optimality for the original reported log utilities, against arbitrary player profiles. -/
theorem canonical_nash (θ : ℝ) (hθ : 0 < θ) (t : Tree) : IsNash θ t (canonical θ t) := by
  constructor
  · intro plus
    rw [reported_coordinates, reported_coordinates, canonical_value]
    exact Thesis.RoutingGate.logCoordinate_monotone
      (auxiliary_saddle θ hθ t plus (canonical θ t)).1
  · intro minus
    rw [reported_coordinates, reported_coordinates, canonical_value]
    exact Thesis.RoutingGate.logCoordinate_monotone
      (neg_le_neg (auxiliary_saddle θ hθ t (canonical θ t) minus).2)

def IsSubgamePerfect (θ : ℝ) : (t : Tree) → Strategy t → Prop
  | .terminal z, profile => IsNash θ (.terminal z) profile
  | .activation q p n, profile => IsNash θ (.activation q p n) profile ∧
      IsSubgamePerfect θ p profile.2.1 ∧ IsSubgamePerfect θ n profile.2.2
  | .routing n q outside w hw c, profile => IsNash θ (.routing n q outside w hw c) profile ∧
      ∀ i, IsSubgamePerfect θ (c i) (profile.2 i)

/-- Pure activation gates and randomized routing form a subgame-perfect source-log equilibrium. -/
theorem canonical_subgame_perfect (θ : ℝ) (hθ : 0 < θ) (t : Tree) :
    IsSubgamePerfect θ t (canonical θ t) := by
  induction t with
  | terminal z => exact canonical_nash θ hθ _
  | activation q p n hp hn => exact ⟨canonical_nash θ hθ _, hp, hn⟩
  | routing n q outside w hw c ih => exact ⟨canonical_nash θ hθ _, ih⟩

theorem canonical_stops_log_ties (θ : ℝ) (q : Bool) (p n : Tree)
    (h : signed q (value θ p + value θ n) ≤ 0) :
    (canonical θ (.activation q p n)).1 = false :=
  Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive _ h

end Thesis.RoutingProfiles
