import Thesis.RoutingGate

/-! The source routing objective with genuine minus-infinity scores. A policy
assigning positive probability to a nonpositive action mass has value bottom.
Zero policy probabilities contribute zero, including at bottom scores. Empty
streams select the distinguished absorbing action. -/
noncomputable section
namespace Thesis.RoutingExtended
open Finset

variable {A : Type*} [Fintype A]

structure Policy (A : Type*) [Fintype A] where
  prob : A → ℝ
  nonnegative : ∀ i, 0 ≤ prob i
  normalized : ∑ i, prob i = 1

def pure [DecidableEq A] (a : A) : Policy A :=
  ⟨fun i => if i = a then 1 else 0, by intro i; split_ifs <;> norm_num, by simp⟩

def entropy (p : Policy A) : ℝ := -(∑ i, p.prob i * Real.log (p.prob i))

def Supported (p : Policy A) (m : A → ℝ) : Prop := ∀ i, 0 < p.prob i → 0 < m i

def score (θ : ℝ) (m : A → ℝ) (p : Policy A) : ℝ :=
  (∑ i, p.prob i * Real.log (m i)) + θ * entropy p

/-- Extended expected log-score plus entropy, with 0*(-infinity)=0. -/
def sourceValue (θ : ℝ) (m : A → ℝ) (p : Policy A) : WithBot ℝ := by
  classical
  exact if Supported p m then (score θ m p : WithBot ℝ) else ⊥

def expZero (z : WithBot ℝ) : ℝ := z.elim 0 Real.exp

@[simp] theorem expZero_coe (z : ℝ) : expZero (z : WithBot ℝ) = Real.exp z := rfl
@[simp] theorem expZero_bottom : expZero ⊥ = 0 := rfl

def routedMass (θ : ℝ) (m : A → ℝ) (p : Policy A) : ℝ := by
  classical
  exact if Supported p m then Real.exp (score θ m p) else 0

theorem expZero_sourceValue (θ : ℝ) (m : A → ℝ) (p : Policy A) :
    expZero (sourceValue θ m p) = routedMass θ m p := by
  unfold sourceValue routedMass
  split_ifs <;> rfl

theorem routedMass_nonnegative (θ : ℝ) (m : A → ℝ) (p : Policy A) :
    0 ≤ routedMass θ m p := by
  unfold routedMass
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem log_routedMass (θ : ℝ) (m : A → ℝ) (p : Policy A) :
    Thesis.RoutingGate.logCoordinate (routedMass θ m p) = sourceValue θ m p := by
  unfold routedMass sourceValue
  split_ifs
  · simp [Thesis.RoutingGate.logCoordinate, Real.exp_pos]
  · simp [Thesis.RoutingGate.logCoordinate]

theorem expZero_logCoordinate (z : ℝ) :
    expZero (Thesis.RoutingGate.logCoordinate z) = max z 0 := by
  by_cases hz : 0 < z
  · simp [Thesis.RoutingGate.logCoordinate, hz, Real.exp_log hz, max_eq_left hz.le]
  · simp [Thesis.RoutingGate.logCoordinate, hz, max_eq_right (le_of_not_gt hz)]

/-- Multiplication of routed masses is exactly the source's addition of extended log scores. -/
theorem source_edge_score (w : ℝ) (hw : 0 ≤ w) (v : WithBot ℝ) :
    Thesis.RoutingGate.logCoordinate (w * expZero v) =
      Thesis.RoutingGate.logCoordinate w + v := by
  induction v using WithBot.recBotCoe with
  | bot => simp [Thesis.RoutingGate.logCoordinate]
  | coe z =>
      by_cases hw0 : w = 0
      · simp [hw0, Thesis.RoutingGate.logCoordinate]
      · have hp := lt_of_le_of_ne hw (Ne.symm hw0)
        have hprod := mul_pos hp (Real.exp_pos z)
        simp [Thesis.RoutingGate.logCoordinate, hp, hprod,
          Real.log_mul hw0 (Real.exp_ne_zero z)]

theorem routedMass_monotone (θ : ℝ) (p : Policy A) : Monotone (fun m => routedMass θ m p) := by
  intro m n hmn
  by_cases hm : Supported p m
  · have hn : Supported p n := fun i hi => (hm i hi).trans_le (hmn i)
    simp only [routedMass, hm, hn, ite_true]
    apply Real.exp_le_exp.mpr
    unfold score
    apply add_le_add _ le_rfl
    apply Finset.sum_le_sum
    intro i _
    by_cases hp : p.prob i = 0
    · simp [hp]
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (hm i (lt_of_le_of_ne (p.nonnegative i) (Ne.symm hp))) (hmn i))
        (p.nonnegative i)
  · simp only [routedMass, hm, ite_false]
    exact routedMass_nonnegative θ n p

/-- Temperature-transformed mass, retaining zeros rather than exponentiating log(0)=0. -/
def tilted (θ : ℝ) (m : A → ℝ) (i : A) : ℝ :=
  if 0 < m i then Real.exp (Real.log (m i) / θ) else 0

omit [Fintype A] in
theorem tilted_nonnegative (θ : ℝ) (m : A → ℝ) (i : A) : 0 ≤ tilted θ m i := by
  unfold tilted
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

omit [Fintype A] in
theorem tilted_positive_iff (θ : ℝ) (m : A → ℝ) (i : A) :
    0 < tilted θ m i ↔ 0 < m i := by
  by_cases hm : 0 < m i <;> simp [tilted, hm, Real.exp_pos]

theorem policy_positive_some (p : Policy A) : ∃ i, 0 < p.prob i := by
  by_contra! h
  have hz : ∀ i, p.prob i = 0 := fun i => le_antisymm (h i) (p.nonnegative i)
  have hs := p.normalized
  simp [hz] at hs

theorem supported_partition_positive (θ : ℝ) (m : A → ℝ) (p : Policy A)
    (hs : Supported p m) : 0 < ∑ i, tilted θ m i := by
  obtain ⟨i, hi⟩ := policy_positive_some p
  exact (tilted_positive_iff θ m i).mpr (hs i hi) |>.trans_le
    (Finset.single_le_sum (fun j _ => tilted_nonnegative θ m j) (Finset.mem_univ i))

def normalized (a : A → ℝ) (hz : 0 < ∑ i, a i) (ha : ∀ i, 0 ≤ a i) : Policy A :=
  ⟨fun i => a i / ∑ j, a j, fun i => div_nonneg (ha i) hz.le, by
    rw [← Finset.sum_div]
    exact div_self hz.ne'⟩

theorem entropy_bound_nonnegative (a : A → ℝ) (p : Policy A) (ha : ∀ i, 0 ≤ a i)
    (hz : 0 < ∑ i, a i) (hs : Supported p a) :
    (∑ i, p.prob i * Real.log (a i)) + entropy p ≤ Real.log (∑ i, a i) := by
  let r := normalized a hz ha
  have hc : (∑ i, (p.prob i * Real.log (r.prob i) - p.prob i * Real.log (p.prob i))) ≤ 0 := by
    calc
      _ ≤ ∑ i, (r.prob i - p.prob i) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hp : p.prob i = 0
        · simpa [hp] using r.nonnegative i
        · exact Thesis.Regularization.entropy_cell_bound _ _ (p.nonnegative i)
            (div_pos (hs i (lt_of_le_of_ne (p.nonnegative i) (Ne.symm hp))) hz)
      _ = 0 := by rw [Finset.sum_sub_distrib, r.normalized, p.normalized]; ring
  have hl (i : A) : p.prob i * Real.log (r.prob i) =
      p.prob i * (Real.log (a i) - Real.log (∑ j, a j)) := by
    by_cases hp : p.prob i = 0
    · simp [hp]
    · exact congrArg (fun z => p.prob i * z)
        (Real.log_div (hs i (lt_of_le_of_ne (p.nonnegative i) (Ne.symm hp))).ne' hz.ne')
  simp_rw [hl, mul_sub] at hc
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, p.normalized, one_mul] at hc
  unfold entropy
  linarith

theorem entropy_value_nonnegative (a : A → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : 0 < ∑ i, a i) :
    (∑ i, (normalized a hz ha).prob i * Real.log (a i)) + entropy (normalized a hz ha) =
      Real.log (∑ i, a i) := by
  have hl (i : A) : (normalized a hz ha).prob i * Real.log ((normalized a hz ha).prob i) =
      (normalized a hz ha).prob i * (Real.log (a i) - Real.log (∑ j, a j)) := by
    by_cases hi : a i = 0
    · simp [normalized, hi]
    · exact congrArg (fun z => (normalized a hz ha).prob i * z) (Real.log_div hi hz.ne')
  unfold entropy
  simp_rw [hl, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (normalized a hz ha).normalized, one_mul]
  ring

theorem score_temperature_identity (θ : ℝ) (hθ : 0 < θ) (m : A → ℝ) (p : Policy A)
    (hs : Supported p m) :
    θ * ((∑ i, p.prob i * Real.log (tilted θ m i)) + entropy p) = score θ m p := by
  have he : θ * (∑ i, p.prob i * Real.log (tilted θ m i)) =
      ∑ i, p.prob i * Real.log (m i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p.prob i = 0
    · simp [hp]
    · have hm := hs i (lt_of_le_of_ne (p.nonnegative i) (Ne.symm hp))
      simp only [tilted, hm, ite_true, Real.log_exp]
      field_simp
  rw [mul_add, he]
  rfl

def gibbs [DecidableEq A] (θ : ℝ) (m : A → ℝ) (outside : A) : Policy A :=
  if hz : 0 < ∑ i, tilted θ m i then normalized (tilted θ m) hz (tilted_nonnegative θ m)
  else pure outside

theorem gibbs_supported [DecidableEq A] (θ : ℝ) (m : A → ℝ) (outside : A)
    (hz : 0 < ∑ i, tilted θ m i) : Supported (gibbs θ m outside) m := by
  intro i hi
  simp only [gibbs, hz, dite_true, normalized] at hi
  apply (tilted_positive_iff θ m i).mp
  by_contra! h
  have he := le_antisymm h (tilted_nonnegative θ m i)
  simp [he] at hi

theorem gibbs_value_positive [DecidableEq A] (θ : ℝ) (hθ : 0 < θ)
    (m : A → ℝ) (outside : A) (hz : 0 < ∑ i, tilted θ m i) :
    routedMass θ m (gibbs θ m outside) = Real.exp (θ * Real.log (∑ i, tilted θ m i)) := by
  have hs := gibbs_supported θ m outside hz
  simp only [routedMass, hs, ite_true]
  congr 1
  rw [← score_temperature_identity θ hθ m _ hs]
  simp only [gibbs, hz, dite_true]
  rw [entropy_value_nonnegative]

theorem gibbs_optimal [DecidableEq A] (θ : ℝ) (hθ : 0 < θ)
    (m : A → ℝ) (outside : A) (p : Policy A) :
    routedMass θ m p ≤ routedMass θ m (gibbs θ m outside) := by
  by_cases hs : Supported p m
  · have hz := supported_partition_positive θ m p hs
    rw [gibbs_value_positive θ hθ m outside hz]
    simp only [routedMass, hs, ite_true]
    apply Real.exp_le_exp.mpr
    rw [← score_temperature_identity θ hθ m p hs]
    apply mul_le_mul_of_nonneg_left _ hθ.le
    exact entropy_bound_nonnegative _ p (tilted_nonnegative θ m) hz
      (fun i hi => (tilted_positive_iff θ m i).mpr (hs i hi))
  · simp only [routedMass, hs, ite_false]
    exact routedMass_nonnegative θ m _

theorem empty_stream_value (θ : ℝ) (m : A → ℝ) (p : Policy A) (hm : ∀ i, m i ≤ 0) :
    sourceValue θ m p = ⊥ ∧ routedMass θ m p = 0 := by
  have hs : ¬ Supported p m := by
    intro hs
    obtain ⟨i, hi⟩ := policy_positive_some p
    exact (not_lt_of_ge (hm i)) (hs i hi)
  simp [sourceValue, routedMass, hs]

theorem empty_stream_absorbs [DecidableEq A] (θ : ℝ) (m : A → ℝ) (outside : A)
    (hm : ∀ i, m i ≤ 0) : gibbs θ m outside = pure outside := by
  have hz : (∑ i, tilted θ m i) = 0 := by simp [tilted, fun i => not_lt_of_ge (hm i)]
  simp [gibbs, hz]

/-- Full extended-score Gibbs optimality, including zero scores and empty streams. -/
theorem sourceValue_gibbs_optimal [DecidableEq A] (θ : ℝ) (hθ : 0 < θ)
    (m : A → ℝ) (outside : A) (p : Policy A) :
    sourceValue θ m p ≤ sourceValue θ m (gibbs θ m outside) := by
  rw [← log_routedMass, ← log_routedMass]
  exact Thesis.RoutingGate.logCoordinate_monotone (gibbs_optimal θ hθ m outside p)

omit [Fintype A] in
theorem tilted_one (m : A → ℝ) (hm : ∀ i, 0 ≤ m i) (i : A) : tilted 1 m i = m i := by
  by_cases hi : 0 < m i
  · simp [tilted, hi, Real.exp_log hi]
  · have hz := le_antisymm (le_of_not_gt hi) (hm i)
    simp [tilted, hz]

theorem gibbs_anchor_mass [DecidableEq A] (m : A → ℝ) (hm : ∀ i, 0 ≤ m i) (outside : A) :
    routedMass 1 m (gibbs 1 m outside) = ∑ i, m i := by
  have hsum : (∑ i, tilted 1 m i) = ∑ i, m i := by simp_rw [tilted_one m hm]
  by_cases hz : 0 < ∑ i, m i
  · rw [gibbs_value_positive 1 (by norm_num) m outside (hsum.symm ▸ hz), hsum]
    simp [Real.exp_log hz]
  · have hz0 : (∑ i, m i) = 0 :=
      le_antisymm (le_of_not_gt hz) (Finset.sum_nonneg fun i _ => hm i)
    have hs : ¬ Supported (gibbs 1 m outside) m := by
      intro hs
      have hp := supported_partition_positive 1 m _ hs
      rw [hsum, hz0] at hp
      exact (lt_irrefl 0) hp
    simp [routedMass, hs, hz0]

theorem gibbs_anchor_probability [DecidableEq A] (m : A → ℝ) (hm : ∀ i, 0 ≤ m i)
    (outside : A) (hz : 0 < ∑ i, m i) (i : A) :
    (gibbs 1 m outside).prob i = m i / ∑ j, m j := by
  simp [gibbs, hz, normalized, tilted_one m hm]

/-- Every non-outside action has its mass ratio, even in an empty stream. -/
theorem gibbs_anchor_nonoutside [DecidableEq A] (m : A → ℝ) (hm : ∀ i, 0 ≤ m i)
    (outside i : A) (hi : i ≠ outside) :
    (gibbs 1 m outside).prob i = m i / ∑ j, m j := by
  by_cases hz : 0 < ∑ j, m j
  · exact gibbs_anchor_probability m hm outside hz i
  · have hz0 : (∑ j, m j) = 0 :=
      le_antisymm (le_of_not_gt hz) (Finset.sum_nonneg fun i _ => hm i)
    simp [gibbs, tilted_one m hm, hz0, pure, hi]

end Thesis.RoutingExtended
