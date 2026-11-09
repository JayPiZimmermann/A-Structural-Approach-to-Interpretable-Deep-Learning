import Thesis.RoutingExtended
import Thesis.ReferencePolicy

/-! Attention Value routing with literal reference-KL scores. Zero reference
mass or zero contribution is an impossible action whenever its policy mass is
positive; a zero-probability action contributes zero. Thus all-zero streams
have bottom value, rather than the real logarithm convention log 0 = 0. -/
noncomputable section
set_option autoImplicit false
namespace Thesis.AttentionReference
open Finset Thesis.RoutingExtended
variable {A : Type*} [Fintype A]

def mass (reference contribution : A → ℝ) : A → ℝ :=
  fun i => reference i * contribution i

/-- The actual extended expected log-contribution minus reference KL. -/
def objective (reference contribution : A → ℝ) (p : Policy A) : WithBot ℝ := by
  classical
  exact if Supported p reference ∧ Supported p contribution then
    ((∑ i, p.prob i * Real.log (contribution i)) -
      Thesis.ReferencePolicy.kl p.prob reference : ℝ) else ⊥

theorem supported_mass (reference contribution : A → ℝ) (p : Policy A)
    (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) :
    Supported p (mass reference contribution) ↔
      Supported p reference ∧ Supported p contribution := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hp := h i hi
      by_contra! hn
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hn (hc i))) hp
    · intro i hi
      have hp := h i hi
      by_contra! hn
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (hr i) hn)) hp
  · rintro ⟨hrp, hcp⟩ i hi
    exact mul_pos (hrp i hi) (hcp i hi)

/-- This bridge identifies the independently defined KL objective, including
its impossible-action cases, with the existing extended Gibbs objective. -/
theorem objective_eq_sourceValue (reference contribution : A → ℝ) (p : Policy A)
    (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) :
    objective reference contribution p = sourceValue 1 (mass reference contribution) p := by
  classical
  by_cases hs : Supported p reference ∧ Supported p contribution
  · have hm := (supported_mass reference contribution p hr hc).mpr hs
    simp only [objective, hs, and_self, sourceValue, hm, ite_true]
    congr 1
    have hlog (i : A) : p.prob i * Real.log (mass reference contribution i) =
        p.prob i * Real.log (reference i) + p.prob i * Real.log (contribution i) := by
      by_cases hp : p.prob i = 0
      · simp [hp]
      · have hpos := lt_of_le_of_ne (p.nonnegative i) (Ne.symm hp)
        rw [mass, Real.log_mul (hs.1 i hpos).ne' (hs.2 i hpos).ne', mul_add]
    simp only [score, entropy, Thesis.ReferencePolicy.kl, hlog, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, one_mul]
    ring
  · have hm : ¬ Supported p (mass reference contribution) :=
      fun h => hs ((supported_mass reference contribution p hr hc).mp h)
    simp [objective, hs, sourceValue, hm]

/-- Strict Gibbs bound permits zero masses, provided positive policy mass
never lies outside the support. This also covers boundary simplex policies. -/
theorem entropy_strict_nonnegative (a : A → ℝ) (p : Policy A)
    (ha : ∀ i, 0 ≤ a i) (hz : 0 < ∑ i, a i) (hs : Supported p a)
    (hne : p.prob ≠ (normalized a hz ha).prob) :
    (∑ i, p.prob i * Real.log (a i)) + entropy p < Real.log (∑ i, a i) := by
  classical
  let r := normalized a hz ha
  have hex : ∃ i, p.prob i ≠ r.prob i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hex
  have cell (j : A) : p.prob j * Real.log (r.prob j) - p.prob j * Real.log (p.prob j)
      ≤ r.prob j - p.prob j := by
    by_cases hp : p.prob j = 0
    · simpa [hp] using r.nonnegative j
    · exact Thesis.Regularization.entropy_cell_bound _ _ (p.nonnegative j)
        (div_pos (hs j (lt_of_le_of_ne (p.nonnegative j) (Ne.symm hp))) hz)
  have strict : p.prob i * Real.log (r.prob i) - p.prob i * Real.log (p.prob i)
      < r.prob i - p.prob i := by
    by_cases hp : p.prob i = 0
    · have hr0 : r.prob i ≠ 0 := by intro he; exact hi (hp.trans he.symm)
      simpa [hp] using lt_of_le_of_ne (r.nonnegative i) (Ne.symm hr0)
    · exact Thesis.ReferencePolicy.entropy_cell_strict _ _ (p.nonnegative i)
        (div_pos (hs i (lt_of_le_of_ne (p.nonnegative i) (Ne.symm hp))) hz) hi
  have hsum : (∑ j, (p.prob j * Real.log (r.prob j) - p.prob j * Real.log (p.prob j))) < 0 := by
    calc
      _ < ∑ j, (r.prob j - p.prob j) :=
        Finset.sum_lt_sum (fun j _ => cell j) ⟨i, Finset.mem_univ i, strict⟩
      _ = 0 := by rw [Finset.sum_sub_distrib, r.normalized, p.normalized]; ring
  have hlog (j : A) : p.prob j * Real.log (r.prob j) =
      p.prob j * (Real.log (a j) - Real.log (∑ k, a k)) := by
    by_cases hp : p.prob j = 0
    · simp [hp]
    · exact congrArg (fun z => p.prob j * z)
        (Real.log_div (hs j (lt_of_le_of_ne (p.nonnegative j) (Ne.symm hp))).ne' hz.ne')
  simp_rw [hlog, mul_sub] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    p.normalized, one_mul] at hsum
  unfold entropy
  linarith

def valuePolicy (reference contribution : A → ℝ)
    (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)
    (hz : 0 < ∑ i, mass reference contribution i) : Policy A :=
  normalized (mass reference contribution) hz (fun i => mul_nonneg (hr i) (hc i))

theorem valuePolicy_probability (reference contribution : A → ℝ)
    (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)
    (hz : 0 < ∑ i, mass reference contribution i) (i : A) :
    (valuePolicy reference contribution hr hc hz).prob i =
      reference i * contribution i / ∑ j, reference j * contribution j := rfl

theorem valuePolicy_supported (reference contribution : A → ℝ)
    (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)
    (hz : 0 < ∑ i, mass reference contribution i) :
    Supported (valuePolicy reference contribution hr hc hz) (mass reference contribution) := by
  intro i hi
  change 0 < mass reference contribution i / ∑ j, mass reference contribution j at hi
  exact (div_pos_iff_of_pos_right hz).mp hi

theorem valuePolicy_value (reference contribution : A → ℝ)
    (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)
    (hz : 0 < ∑ i, mass reference contribution i) :
    objective reference contribution (valuePolicy reference contribution hr hc hz) =
      (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) := by
  rw [objective_eq_sourceValue reference contribution _ hr hc]
  simp only [sourceValue, valuePolicy_supported reference contribution hr hc hz, ite_true]
  congr 1
  simpa only [score, one_mul, valuePolicy, mass] using
    entropy_value_nonnegative (mass reference contribution) (fun i => mul_nonneg (hr i) (hc i)) hz

theorem objective_bound (reference contribution : A → ℝ) (p : Policy A)
    (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)
    (hz : 0 < ∑ i, mass reference contribution i) :
    objective reference contribution p ≤
      (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) := by
  rw [objective_eq_sourceValue reference contribution p hr hc]
  by_cases hs : Supported p (mass reference contribution)
  · simp only [sourceValue, hs, ite_true]
    apply WithBot.coe_le_coe.mpr
    simpa only [score, one_mul, mass] using
      entropy_bound_nonnegative (mass reference contribution) p (fun i => mul_nonneg (hr i) (hc i)) hz hs
  · simp [sourceValue, hs]

/-- Every optimizer agrees with the mass-ratio policy, even when some keys
have zero reference mass or zero Value contribution. -/
theorem valuePolicy_unique (reference contribution : A → ℝ) (p : Policy A)
    (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)
    (hz : 0 < ∑ i, mass reference contribution i) :
    objective reference contribution p =
      (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ↔
      p.prob = (valuePolicy reference contribution hr hc hz).prob := by
  constructor
  · intro he
    rw [objective_eq_sourceValue reference contribution p hr hc] at he
    by_cases hs : Supported p (mass reference contribution)
    · simp only [sourceValue, hs, ite_true] at he
      have he' : score 1 (mass reference contribution) p =
          Real.log (∑ i, reference i * contribution i) := WithBot.coe_injective he
      by_contra hn
      have hlt := entropy_strict_nonnegative (mass reference contribution) p
        (fun i => mul_nonneg (hr i) (hc i)) hz hs hn
      have hscore : score 1 (mass reference contribution) p =
          (∑ i, p.prob i * Real.log (mass reference contribution i)) + entropy p := by
        simp [score]
      rw [hscore] at he'
      exact (ne_of_lt hlt) he'
    · simp [sourceValue, hs] at he
  · intro he
    have ext {p q : Policy A} (h : p.prob = q.prob) : p = q := by
      cases p
      cases q
      simp_all
    have hp : p = valuePolicy reference contribution hr hc hz := ext he
    rw [hp]
    exact valuePolicy_value reference contribution hr hc hz

theorem zero_mass_value (reference contribution : A → ℝ) (p : Policy A)
    (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)
    (hz : (∑ i, reference i * contribution i) = 0) :
    objective reference contribution p = ⊥ := by
  rw [objective_eq_sourceValue reference contribution p hr hc]
  apply (empty_stream_value 1 (mass reference contribution) p _).1
  intro i
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset A)) =>
    mul_nonneg (hr j) (hc j)) (Finset.mem_univ i)
  rw [hz] at h
  exact h

/-- Source Value-routing proposition on the full simplex: the positive-mass
maximum is attained uniquely, and the displayed policy has the literal ratio. -/
theorem attention_value_routing (reference contribution : A → ℝ)
    (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)
    (hz : 0 < ∑ i, mass reference contribution i) :
    IsGreatest (Set.range (objective reference contribution))
      (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ∧
    (∀ p : Policy A, objective reference contribution p =
      (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ↔
      p.prob = (valuePolicy reference contribution hr hc hz).prob) ∧
    (∀ i, (valuePolicy reference contribution hr hc hz).prob i =
      reference i * contribution i / ∑ j, reference j * contribution j) := by
  refine ⟨⟨⟨valuePolicy reference contribution hr hc hz,
    valuePolicy_value reference contribution hr hc hz⟩, ?_⟩,
    fun p => valuePolicy_unique reference contribution p hr hc hz,
    valuePolicy_probability reference contribution hr hc hz⟩
  rintro _ ⟨p, rfl⟩
  exact objective_bound reference contribution p hr hc hz

end Thesis.AttentionReference
