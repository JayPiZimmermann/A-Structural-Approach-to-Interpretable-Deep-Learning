import Thesis.Regularization

/-! Finite reference-policy KL optimization. Policies may have zero coordinates;
reference masses and action scores here are finite and strictly positive/real,
respectively. Zero-reference actions can be represented by restricting the
finite action type to their positive support. -/
noncomputable section
namespace Thesis.ReferencePolicy
open Finset Thesis.Regularization

variable {A : Type*} [Fintype A] [Nonempty A]

def kl (p ρ : A → ℝ) : ℝ := ∑ i, p i * (Real.log (p i) - Real.log (ρ i))

def tiltedMass (θ : ℝ) (ρ q : A → ℝ) (i : A) : ℝ := ρ i * Real.exp (q i / θ)

def referencePolicy (θ : ℝ) (ρ q : A → ℝ) : A → ℝ := normalized (tiltedMass θ ρ q)

def referenceValue (θ : ℝ) (ρ q : A → ℝ) : ℝ := θ * Real.log (∑ i, tiltedMass θ ρ q i)

omit [Fintype A] [Nonempty A] in
theorem tiltedMass_pos (θ : ℝ) (ρ q : A → ℝ) (hρ : ∀ i, 0 < ρ i) (i : A) :
    0 < tiltedMass θ ρ q i := mul_pos (hρ i) (Real.exp_pos _)

theorem referencePolicy_pos (θ : ℝ) (ρ q : A → ℝ) (hρ : ∀ i, 0 < ρ i) (i : A) :
    0 < referencePolicy θ ρ q i := normalized_pos _ (tiltedMass_pos θ ρ q hρ) i

theorem referencePolicy_normalized (θ : ℝ) (ρ q : A → ℝ) (hρ : ∀ i, 0 < ρ i) :
    ∑ i, referencePolicy θ ρ q i = 1 := normalized_sum _ (tiltedMass_pos θ ρ q hρ)

/- The KL objective is the finite Gibbs objective for reference-weighted masses. -/
omit [Nonempty A] in
theorem kl_objective_identity (θ : ℝ) (ρ q p : A → ℝ) (hθ : 0 < θ)
    (hρ : ∀ i, 0 < ρ i) :
    (∑ i, p i * q i) - θ * kl p ρ = θ *
      ((∑ i, p i * Real.log (tiltedMass θ ρ q i)) - ∑ i, p i * Real.log (p i)) := by
  have hl (i : A) : Real.log (tiltedMass θ ρ q i) = Real.log (ρ i) + q i / θ := by
    rw [tiltedMass, Real.log_mul (hρ i).ne' (Real.exp_pos _).ne', Real.log_exp]
  simp_rw [hl]
  simp only [kl, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have he : θ * (∑ i, p i * (q i / θ)) = ∑ i, p i * q i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [he]
  ring

/-- The reference-policy variational bound, for every policy in the simplex. -/
theorem reference_variational_bound (θ : ℝ) (ρ q p : A → ℝ) (hθ : 0 < θ)
    (hρ : ∀ i, 0 < ρ i) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, p i * q i) - θ * kl p ρ ≤ referenceValue θ ρ q := by
  rw [kl_objective_identity θ ρ q p hθ hρ]
  exact mul_le_mul_of_nonneg_left
    (finite_gibbs_bound _ p (tiltedMass_pos θ ρ q hρ) hp hsum) hθ.le

/-- The reference-tilted Gibbs policy attains the exact KL-regularized value. -/
theorem reference_policy_value (θ : ℝ) (ρ q : A → ℝ) (hθ : 0 < θ)
    (hρ : ∀ i, 0 < ρ i) :
    (∑ i, referencePolicy θ ρ q i * q i) - θ * kl (referencePolicy θ ρ q) ρ =
      referenceValue θ ρ q := by
  rw [kl_objective_identity θ ρ q (referencePolicy θ ρ q) hθ hρ]
  exact congrArg (fun z : ℝ => θ*z) (finite_gibbs_value _ (tiltedMass_pos θ ρ q hρ))

theorem entropy_cell_strict (p r : ℝ) (hp : 0 ≤ p) (hr : 0 < r) (hne : p ≠ r) :
    p * Real.log r - p * Real.log p < r - p := by
  by_cases h0 : p = 0
  · subst p
    simpa using hr
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm h0)
  have hn : r / p ≠ 1 := by
    intro he
    exact hne ((div_eq_one_iff_eq hp'.ne').1 he).symm
  have h := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos hr hp') hn) hp'
  rw [Real.log_div hr.ne' hp'.ne'] at h
  have hm : p * (r / p - 1) = r - p := by field_simp
  nlinarith

/-- A distinct simplex policy has strictly smaller Gibbs objective. -/
theorem finite_gibbs_strict (a p : A → ℝ) (ha : ∀ i, 0 < a i)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hne : p ≠ normalized a) :
    (∑ i, p i * Real.log (a i)) - (∑ i, p i * Real.log (p i)) <
      Real.log (∑ i, a i) := by
  have hex : ∃ i, p i ≠ normalized a i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hex
  have hc : (∑ j, (p j * Real.log (normalized a j) - p j * Real.log (p j))) < 0 := by
    calc
      _ < ∑ j, (normalized a j - p j) :=
        Finset.sum_lt_sum
          (fun j _ => entropy_cell_bound _ _ (hp j) (normalized_pos a ha j))
          ⟨i, Finset.mem_univ i, entropy_cell_strict _ _ (hp i) (normalized_pos a ha i) hi⟩
      _ = 0 := by rw [Finset.sum_sub_distrib, normalized_sum a ha, hsum]; ring
  have hl (i : A) : Real.log (normalized a i) = Real.log (a i) - Real.log (∑ j, a j) :=
    Real.log_div (ha i).ne' (partition_pos a ha).ne'
  have hs : (∑ i, p i * Real.log (normalized a i)) =
      (∑ i, p i * Real.log (a i)) - Real.log (∑ i, a i) := by
    simp_rw [hl, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [Finset.sum_sub_distrib, hs] at hc
  linarith

/-- The full-support reference-policy optimizer is unique, including simplex boundaries. -/
theorem reference_policy_unique (θ : ℝ) (ρ q p : A → ℝ) (hθ : 0 < θ)
    (hρ : ∀ i, 0 < ρ i) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, p i * q i) - θ * kl p ρ = referenceValue θ ρ q ↔ p = referencePolicy θ ρ q := by
  constructor
  · intro he
    by_contra hn
    have h := finite_gibbs_strict (tiltedMass θ ρ q) p (tiltedMass_pos θ ρ q hρ) hp hsum hn
    have hm := mul_lt_mul_of_pos_left h hθ
    rw [← kl_objective_identity θ ρ q p hθ hρ] at hm
    exact (ne_of_lt hm) he
  · rintro rfl
    exact reference_policy_value θ ρ q hθ hρ

/-- Thesis Lemma `ptnb:lem:kl-legendre-fenchel`, finite positive-reference variant. -/
theorem thesis_kl_legendre_fenchel (θ : ℝ) (ρ q : A → ℝ) (hθ : 0 < θ)
    (hρ : ∀ i, 0 < ρ i) :
    IsGreatest ((fun p : A → ℝ => (∑ i, p i * q i) - θ * kl p ρ) ''
      {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}) (referenceValue θ ρ q) := by
  refine ⟨?_, ?_⟩
  · exact ⟨referencePolicy θ ρ q,
      ⟨fun i => (referencePolicy_pos θ ρ q hρ i).le, referencePolicy_normalized θ ρ q hρ⟩,
      reference_policy_value θ ρ q hθ hρ⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact reference_variational_bound θ ρ q p hθ hρ hp.1 hp.2

/- The conservative Value-routing policy at the logarithmic-contribution anchor. -/
omit [Nonempty A] in
theorem reference_log_policy (ρ u : A → ℝ) (hu : ∀ i, 0 < u i) :
    referencePolicy 1 ρ (fun i => Real.log (u i)) =
      (fun i => ρ i * u i / ∑ j, ρ j * u j) := by
  funext i
  simp only [referencePolicy, normalized, tiltedMass, div_one, Real.exp_log (hu _)]

/-- Attention's positive-contribution KL subgame, with the reference and scores explicit. -/
theorem thesis_attention_value_policy (ρ u : A → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hu : ∀ i, 0 < u i) :
    IsGreatest ((fun p : A → ℝ => (∑ i, p i * Real.log (u i)) - kl p ρ) ''
      {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}) (Real.log (∑ i, ρ i * u i)) := by
  have h := thesis_kl_legendre_fenchel 1 ρ (fun i => Real.log (u i)) zero_lt_one hρ
  simpa only [referenceValue, tiltedMass, div_one, one_mul, Real.exp_log (hu _)] using h

end Thesis.ReferencePolicy
