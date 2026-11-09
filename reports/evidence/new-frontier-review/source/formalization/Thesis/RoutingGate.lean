import Thesis.Regularization

/-! Activation decisions maximize the source's extended-log values, with stopping
explicitly selected at every log-space tie. All nonpositive continuation masses
tie with stop. The selected optimizer is the positive-preactivation gate. Signed
utility comparisons are separate compatibility identities, not the RG objective.
The frozen-gate lemmas concern local conditioned operators only. -/
noncomputable section
namespace Thesis.RoutingGate

/-- The source's extended logarithm sends every nonpositive mass to bottom. -/
def logCoordinate (z : ℝ) : WithBot ℝ := if 0 < z then (Real.log z : WithBot ℝ) else ⊥

def logAction (z : ℝ) (cont : Bool) : WithBot ℝ :=
  if cont then logCoordinate z else ⊥

/-- Select continue only if its log value strictly exceeds the stopping value. -/
def chosenLogAction (z : ℝ) : Bool := decide (⊥ < logCoordinate z)

theorem chosenLogAction_eq_positive (z : ℝ) : chosenLogAction z = decide (0 < z) := by
  by_cases hz : 0 < z <;> simp [chosenLogAction, logCoordinate, hz]

theorem nonpositive_log_actions_tied (z : ℝ) (hz : z ≤ 0) (cont : Bool) :
    logAction z cont = ⊥ := by
  cases cont <;> simp [logAction, logCoordinate, not_lt_of_ge hz]

theorem chosenLogAction_stops_at_nonpositive (z : ℝ) (hz : z ≤ 0) :
    chosenLogAction z = false := by
  simp [chosenLogAction_eq_positive, not_lt_of_ge hz]

theorem positive_continue_strictly_better (z : ℝ) (hz : 0 < z) :
    logAction z false < logAction z true := by
  simp [logAction, logCoordinate, hz]

/-- The explicitly tie-selected action maximizes the original log-space objective. -/
theorem chosenLogAction_optimal (z : ℝ) (cont : Bool) :
    logAction z cont ≤ logAction z (chosenLogAction z) := by
  by_cases hz : 0 < z
  · rw [chosenLogAction_eq_positive]
    cases cont <;> simp [logAction, hz]
  · rw [nonpositive_log_actions_tied z (le_of_not_gt hz) cont,
      nonpositive_log_actions_tied z (le_of_not_gt hz) (chosenLogAction z)]

/-- Reporting the mass selected by the log optimizer gives the original ReLU value. -/
theorem chosenLogAction_mass (z : ℝ) :
    (if chosenLogAction z then z else 0) = max z 0 := by
  rw [chosenLogAction_eq_positive]
  by_cases hz : 0 < z
  · simp [hz, max_eq_left hz.le]
  · simp [hz, max_eq_right (le_of_not_gt hz)]

/-- Auxiliary signed utility, for comparing the canonical gates only. -/
def signedUtility (z : ℝ) (p : Set.Icc (0 : ℝ) 1) : ℝ := p.val * z

def gate (z : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨if 0 < z then 1 else 0, by split_ifs <;> constructor <;> norm_num⟩

theorem gate_value (z : ℝ) : signedUtility z (gate z) = max z 0 := by
  by_cases hz : 0 < z
  · simp [signedUtility, gate, hz, max_eq_left hz.le]
  · simp [signedUtility, gate, hz, max_eq_right (le_of_not_gt hz)]

theorem signed_policy_bound (z : ℝ) (p : Set.Icc (0 : ℝ) 1) :
    signedUtility z p ≤ max z 0 := by
  by_cases hz : 0 ≤ z
  · rw [max_eq_left hz]
    exact (mul_le_mul_of_nonneg_right p.property.2 hz).trans_eq (one_mul z)
  · rw [max_eq_right (le_of_not_ge hz)]
    exact mul_nonpos_of_nonneg_of_nonpos p.property.1 (le_of_not_ge hz)

theorem signed_gate_optimal (z : ℝ) (p : Set.Icc (0 : ℝ) 1) :
    signedUtility z p ≤ signedUtility z (gate z) := by
  rw [gate_value]
  exact signed_policy_bound z p

theorem logCoordinate_monotone : Monotone logCoordinate := by
  intro a b hab
  by_cases ha : 0 < a
  · have hb := ha.trans_le hab
    simp only [logCoordinate, ha, hb, ite_true]
    exact WithBot.coe_le_coe.mpr (Real.log_le_log ha hab)
  · simp [logCoordinate, ha]

/-- Scalar mass-mixing extension, ell(p*z). This is not an expected log payoff
and does not define arbitrary behavioral-policy utilities in the full game. -/
def logPolicy (z : ℝ) (p : Set.Icc (0 : ℝ) 1) : WithBot ℝ :=
  logCoordinate (p.val * z)

/-- The mixed strategy selected by the pure log-space stop-at-tie convention. -/
def chosenLogPolicy (z : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨if chosenLogAction z then 1 else 0, by split_ifs <;> constructor <;> norm_num⟩

theorem chosenLogPolicy_eq_gate (z : ℝ) : chosenLogPolicy z = gate z := by
  apply Subtype.ext
  simp [chosenLogPolicy, gate, chosenLogAction_eq_positive]

/-- The selected gate maximizes the explicit mass-mixing scalar objective. -/
theorem chosenLogPolicy_optimal (z : ℝ) (p : Set.Icc (0 : ℝ) 1) :
    logPolicy z p ≤ logPolicy z (chosenLogPolicy z) := by
  rw [chosenLogPolicy_eq_gate]
  exact logCoordinate_monotone (signed_gate_optimal z p)

theorem nonpositive_log_policies_tied (z : ℝ) (hz : z ≤ 0)
    (p : Set.Icc (0 : ℝ) 1) : logPolicy z p = ⊥ := by
  have hpz : p.val * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos p.property.1 hz
  simp [logPolicy, logCoordinate, not_lt_of_ge hpz]

theorem chosenLogPolicy_stops_at_nonpositive (z : ℝ) (hz : z ≤ 0) :
    (chosenLogPolicy z).val = 0 := by
  simp [chosenLogPolicy, chosenLogAction_stops_at_nonpositive z hz]

/-- At positive mass every mixed policy with less than full continuation is worse. -/
theorem positive_log_policy_strict (z : ℝ) (hz : 0 < z)
    (p : Set.Icc (0 : ℝ) 1) (hp : p.val < 1) :
    logPolicy z p < logPolicy z (chosenLogPolicy z) := by
  rw [chosenLogPolicy_eq_gate]
  have hgate : (gate z).val = 1 := by simp [gate, hz]
  simp only [logPolicy, hgate, one_mul]
  have hlt : p.val * z < z := by nlinarith
  by_cases hp0 : p.val = 0
  · simp [hp0, logCoordinate, hz]
  · have hpz : 0 < p.val * z := mul_pos (lt_of_le_of_ne p.property.1 (Ne.symm hp0)) hz
    simp only [logCoordinate, hpz, hz, ite_true]
    exact WithBot.coe_lt_coe.mpr (Real.log_lt_log hpz hlt)

theorem signed_optimal_iff (z : ℝ) (p : Set.Icc (0 : ℝ) 1) :
    signedUtility z p = max z 0 ↔
      (0 < z → p.val = 1) ∧ (z < 0 → p.val = 0) := by
  constructor
  · intro he
    constructor
    · intro hz
      rw [max_eq_left hz.le] at he
      unfold signedUtility at he
      nlinarith
    · intro hz
      rw [max_eq_right hz.le] at he
      unfold signedUtility at he
      exact (mul_eq_zero.mp he).resolve_right hz.ne
  · intro hp
    rcases lt_trichotomy z 0 with hz | hz | hz
    · simp [signedUtility, hp.2 hz, max_eq_right hz.le]
    · simp [signedUtility, hz]
    · simp [signedUtility, hp.1 hz, max_eq_left hz.le]

/-- Nonnegative branch masses can have a strictly negative signed continuation value. -/
theorem negative_signed_utility_strict (P N : ℝ) (h : P < N)
    (p : Set.Icc (0 : ℝ) 1) (hp : 0 < p.val) : signedUtility (P-N) p < 0 :=
  mul_neg_of_pos_of_neg hp (sub_neg.mpr h)

theorem logCoordinate_nonpositive (z : ℝ) (hz : z ≤ 0) : logCoordinate z = ⊥ := by
  simp [logCoordinate, not_lt_of_ge hz]

theorem logCoordinate_selected_value (z : ℝ) :
    logCoordinate (signedUtility z (gate z)) = logCoordinate z := by
  rw [gate_value]
  by_cases hz : 0 < z
  · rw [max_eq_left hz.le]
  · rw [max_eq_right (le_of_not_gt hz), logCoordinate_nonpositive z (le_of_not_gt hz)]
    exact logCoordinate_nonpositive 0 le_rfl

/-- Log coordinates identify stop and negative continuation even though their utilities differ. -/
theorem negative_log_tie_is_not_utility_tie (z : ℝ) (hz : z < 0) :
    logCoordinate z = logCoordinate 0 ∧ z < 0 := by
  exact ⟨by rw [logCoordinate_nonpositive z hz.le, logCoordinate_nonpositive 0 le_rfl], hz⟩

def frozenGate (c : ℝ) (z : ℝ) : ℝ := c * z

theorem frozenGate_hasDerivAt (c z : ℝ) : HasDerivAt (frozenGate c) c z := by
  convert (hasDerivAt_id z).const_mul c using 1 <;> first | rfl | ring

theorem frozenGate_nonnegative (c z : ℝ) (hc : 0 ≤ c) (hz : 0 ≤ z) :
    0 ≤ frozenGate c z := mul_nonneg hc hz

/-- Freezing a gate agrees in value at its reference point. -/
theorem frozenGate_reference_value (g : ℝ → ℝ) (z : ℝ) : frozenGate (g z) z = g z * z := rfl

/-- Differentiating the original varying gate has an additional product-rule term. -/
theorem varyingGate_hasDerivAt (g : ℝ → ℝ) (z d : ℝ) (hg : HasDerivAt g d z) :
    HasDerivAt (fun y => g y * y) (g z + z*d) z := by
  convert hg.mul (hasDerivAt_id z) using 1 <;> first | rfl | simp [id_eq, mul_comm, add_comm]

end Thesis.RoutingGate
