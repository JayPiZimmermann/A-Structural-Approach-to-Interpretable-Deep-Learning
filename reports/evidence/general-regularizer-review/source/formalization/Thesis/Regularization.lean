import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Tactic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! Analytic core of the entropy-regularized stopping game.
All derivatives are ordinary real derivatives, with strictly positive temperature.
The variational statement explicitly restricts policies to the probability interval. -/
noncomputable section
namespace Thesis.Regularization

def softplus (θ z : ℝ) : ℝ := θ * Real.log (1 + Real.exp (z / θ))

def gate (θ z : ℝ) : ℝ := Real.sigmoid (z / θ)

theorem gate_pos (θ z : ℝ) : 0 < gate θ z := Real.sigmoid_pos _
theorem gate_lt_one (θ z : ℝ) : gate θ z < 1 := Real.sigmoid_lt_one _

theorem sigmoid_exp_ratio (z : ℝ) :
    Real.sigmoid z = Real.exp z / (1 + Real.exp z) := by
  rw [Real.sigmoid_def, Real.exp_neg]
  field_simp
  ring

theorem hasDerivAt_softplus (θ z : ℝ) (hθ : 0 < θ) :
    HasDerivAt (softplus θ) (gate θ z) z := by
  have hd := (((hasDerivAt_id z).div_const θ).exp.const_add 1).log
    (show 1 + Real.exp (z / θ) ≠ 0 by positivity)
  convert hd.const_mul θ using 1
  · rfl
  · rw [gate, sigmoid_exp_ratio]
    simp only [id_eq]
    field_simp


theorem deriv_softplus (θ z : ℝ) (hθ : 0 < θ) :
    deriv (softplus θ) z = gate θ z := (hasDerivAt_softplus θ z hθ).deriv

theorem hasDerivAt_gate (θ z : ℝ) (_hθ : 0 < θ) :
    HasDerivAt (gate θ) (gate θ z * (1 - gate θ z) / θ) z := by
  convert (Real.hasDerivAt_sigmoid (z / θ)).comp z
    ((hasDerivAt_id z).div_const θ) using 1
  · rfl
  · simp [gate, div_eq_mul_inv, mul_assoc]

theorem gate_derivative_pos (θ z : ℝ) (hθ : 0 < θ) :
    0 < gate θ z * (1 - gate θ z) / θ := by
  exact div_pos (mul_pos (gate_pos θ z) (sub_pos.mpr (gate_lt_one θ z))) hθ

/-- The two-action Gibbs variational bound, including deterministic endpoint policies. -/
theorem binary_gibbs_bound (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * Real.log a + (1 - p) * Real.log b + Real.binEntropy p ≤ Real.log (a + b) := by
  by_cases h0 : p = 0
  · subst p
    simpa using Real.log_le_log hb (show b ≤ a + b by linarith)
  by_cases h1 : p = 1
  · subst p
    simpa using Real.log_le_log ha (show a ≤ a + b by linarith)
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm h0)
  have hp1' : p < 1 := lt_of_le_of_ne hp1 h1
  have hq : 0 < 1 - p := sub_pos.mpr hp1'
  have hj := strictConcaveOn_log_Ioi.concaveOn.2
    (show a / p ∈ Set.Ioi 0 from div_pos ha hp')
    (show b / (1 - p) ∈ Set.Ioi 0 from div_pos hb hq)
    hp (le_of_lt hq) (show p + (1 - p) = 1 by ring)
  simp only [smul_eq_mul] at hj
  have hm : p * (a / p) + (1 - p) * (b / (1 - p)) = a + b := by
    field_simp
  rw [hm, Real.log_div ha.ne' hp'.ne', Real.log_div hb.ne' hq.ne'] at hj
  simp only [Real.binEntropy, Real.log_inv]
  nlinarith

/-- The Gibbs policy attains the log-partition value. -/
theorem binary_gibbs_value (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a / (a + b)) * Real.log a + (1 - a / (a + b)) * Real.log b +
      Real.binEntropy (a / (a + b)) = Real.log (a + b) := by
  have hab : 0 < a + b := add_pos ha hb
  have hq : 1 - a / (a + b) = b / (a + b) := by field_simp; ring
  simp only [Real.binEntropy, Real.log_inv, hq,
    Real.log_div ha.ne' hab.ne', Real.log_div hb.ne' hab.ne']
  field_simp
  ring

/-- Every other policy is strictly below the positive two-action Gibbs optimum. -/
theorem binary_gibbs_strict (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hne : p ≠ a / (a + b)) :
    p * Real.log a + (1 - p) * Real.log b + Real.binEntropy p < Real.log (a + b) := by
  by_cases h0 : p = 0
  · subst p
    simpa using Real.log_lt_log hb (show b < a + b by linarith)
  by_cases h1 : p = 1
  · subst p
    simpa using Real.log_lt_log ha (show a < a + b by linarith)
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm h0)
  have hp1' : p < 1 := lt_of_le_of_ne hp1 h1
  have hq : 0 < 1 - p := sub_pos.mpr hp1'
  have hab : 0 < a + b := add_pos ha hb
  have hneq : a / p ≠ b / (1 - p) := by
    intro he
    apply hne
    apply (eq_div_iff hab.ne').2
    have hc := (div_eq_div_iff hp'.ne' hq.ne').1 he
    nlinarith
  have hj := strictConcaveOn_log_Ioi.2
    (show a / p ∈ Set.Ioi 0 from div_pos ha hp')
    (show b / (1 - p) ∈ Set.Ioi 0 from div_pos hb hq)
    hneq hp' hq (show p + (1 - p) = 1 by ring)
  simp only [smul_eq_mul] at hj
  have hm : p * (a / p) + (1 - p) * (b / (1 - p)) = a + b := by field_simp
  rw [hm, Real.log_div ha.ne' hp'.ne', Real.log_div hb.ne' hq.ne'] at hj
  simp only [Real.binEntropy, Real.log_inv]
  nlinarith

/-- Every stop/continue policy has value below Softplus. -/
theorem entropy_policy_le_softplus (θ z p : ℝ) (hθ : 0 < θ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * z + θ * Real.binEntropy p ≤ softplus θ z := by
  have h := binary_gibbs_bound (Real.exp (z / θ)) 1 p (Real.exp_pos _) zero_lt_one hp hp1
  simp only [Real.log_exp, Real.log_one, mul_zero, add_zero] at h
  have hm := mul_le_mul_of_nonneg_left h hθ.le
  have he : θ * (p * (z / θ)) = p * z := by field_simp
  simpa [softplus, mul_add, he, add_comm] using hm

/-- The sigmoid gate attains the entropy-regularized stop/continue value. -/
theorem entropy_gate_value (θ z : ℝ) (hθ : 0 < θ) :
    gate θ z * z + θ * Real.binEntropy (gate θ z) = softplus θ z := by
  have h := binary_gibbs_value (Real.exp (z / θ)) 1 (Real.exp_pos _) zero_lt_one
  simp only [Real.log_exp, Real.log_one, mul_zero, add_zero] at h
  have hg : gate θ z = Real.exp (z / θ) / (Real.exp (z / θ) + 1) := by
    rw [gate, sigmoid_exp_ratio, add_comm]
  rw [← hg] at h
  have hm := congrArg (fun t : ℝ => θ * t) h
  have he : θ * (gate θ z * (z / θ)) = gate θ z * z := by field_simp
  simpa [softplus, mul_add, he, add_comm] using hm

/-- Softplus is exactly the maximum of the binary entropy-regularized objective. -/
theorem softplus_variational (θ z : ℝ) (hθ : 0 < θ) :
    IsGreatest ((fun p : ℝ => p * z + θ * Real.binEntropy p) '' Set.Icc 0 1)
      (softplus θ z) := by
  refine ⟨?_, ?_⟩
  · exact ⟨gate θ z, ⟨(gate_pos θ z).le, (gate_lt_one θ z).le⟩,
      entropy_gate_value θ z hθ⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact entropy_policy_le_softplus θ z p hθ hp.1 hp.2

/-- The entropy-regularized stop/continue optimizer is unique at positive temperature. -/
theorem entropy_gate_unique (θ z p : ℝ) (hθ : 0 < θ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * z + θ * Real.binEntropy p = softplus θ z ↔ p = gate θ z := by
  constructor
  · intro he
    by_contra hne
    have hg : gate θ z = Real.exp (z / θ) / (Real.exp (z / θ) + 1) := by
      rw [gate, sigmoid_exp_ratio, add_comm]
    have hn : p ≠ Real.exp (z / θ) / (Real.exp (z / θ) + 1) := by rwa [← hg]
    have h := binary_gibbs_strict (Real.exp (z / θ)) 1 p (Real.exp_pos _) zero_lt_one hp hp1 hn
    simp only [Real.log_exp, Real.log_one, mul_zero, add_zero] at h
    have hm := mul_lt_mul_of_pos_left h hθ
    have hx : θ * (p * (z / θ)) = p * z := by field_simp
    have hh : p * z + θ * Real.binEntropy p < softplus θ z := by
      simpa [softplus, mul_add, hx, add_comm] using hm
    exact (ne_of_lt hh) he
  · rintro rfl
    exact entropy_gate_value θ z hθ

/-- The second derivative is positive at every input for positive temperature. -/
theorem hasDerivAt_deriv_softplus (θ z : ℝ) (hθ : 0 < θ) :
    HasDerivAt (deriv (softplus θ)) (gate θ z * (1 - gate θ z) / θ) z := by
  have hf : deriv (softplus θ) = gate θ := funext fun x => deriv_softplus θ x hθ
  rw [hf]
  exact hasDerivAt_gate θ z hθ

/-- Softplus lies between ReLU and ReLU plus the sharp uniform entropy error. -/
theorem softplus_relu_bounds (θ z : ℝ) (hθ : 0 < θ) :
    max z 0 ≤ softplus θ z ∧ softplus θ z ≤ max z 0 + θ * Real.log 2 := by
  constructor
  · by_cases hz : 0 ≤ z
    · have h := entropy_policy_le_softplus θ z 1 hθ zero_le_one le_rfl
      simpa [max_eq_left hz] using h
    · have h := entropy_policy_le_softplus θ z 0 hθ le_rfl zero_le_one
      simpa [max_eq_right (le_of_not_ge hz)] using h
  · have he := entropy_gate_value θ z hθ
    have hh := mul_le_mul_of_nonneg_left (Real.binEntropy_le_log_two (p := gate θ z)) hθ.le
    have hg : gate θ z * z ≤ max z 0 := by
      by_cases hz : 0 ≤ z
      · rw [max_eq_left hz]
        exact (mul_le_mul_of_nonneg_right (gate_lt_one θ z).le hz).trans_eq (one_mul z)
      · rw [max_eq_right (le_of_not_ge hz)]
        exact mul_nonpos_of_nonneg_of_nonpos (gate_pos θ z).le (le_of_not_ge hz)
    linarith

/-- The pairwise activation used by the entropy-regularized stopping decomposition. -/
def softSplit (θ u v : ℝ) : ℝ × ℝ :=
  (gate θ (u - v) * u + θ * Real.binEntropy (gate θ (u - v)), gate θ (u - v) * v)

theorem softSplit_recovery (θ u v : ℝ) (hθ : 0 < θ) :
    (softSplit θ u v).1 - (softSplit θ u v).2 = softplus θ (u - v) := by
  have h := entropy_gate_value θ (u - v) hθ
  simp only [softSplit]
  nlinarith

theorem softSplit_nonneg (θ u v : ℝ) (hθ : 0 < θ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (softSplit θ u v).1 ∧ 0 ≤ (softSplit θ u v).2 := by
  have hg := (gate_pos θ (u - v)).le
  have hH := Real.binEntropy_nonneg hg (gate_lt_one θ (u - v)).le
  exact ⟨add_nonneg (mul_nonneg hg hu) (mul_nonneg hθ.le hH), mul_nonneg hg hv⟩

theorem softSplit_common_shift (θ u v c : ℝ) :
    softSplit θ (u + c) (v + c) =
      ((softSplit θ u v).1 + gate θ (u - v) * c,
       (softSplit θ u v).2 + gate θ (u - v) * c) := by
  have hd : (u + c) - (v + c) = u - v := by ring
  simp only [softSplit, hd]
  congr 1 <;> ring

/-- One-cell log-sum inequality, valid even for a zero policy probability. -/
theorem entropy_cell_bound (p r : ℝ) (hp : 0 ≤ p) (hr : 0 < r) :
    p * Real.log r - p * Real.log p ≤ r - p := by
  by_cases h0 : p = 0
  · subst p
    simpa using hr.le
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm h0)
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hr hp')) hp
  rw [Real.log_div hr.ne' hp'.ne'] at h
  have hm : p * (r / p - 1) = r - p := by field_simp
  nlinarith

section FiniteGibbs
variable {A : Type*} [Fintype A] [Nonempty A]

/-- Normalized positive action masses (the Gibbs policy when masses are exponentials). -/
def normalized (a : A → ℝ) (i : A) : ℝ := a i / ∑ j, a j

theorem partition_pos (a : A → ℝ) (ha : ∀ i, 0 < a i) : 0 < ∑ i, a i :=
  Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty

theorem normalized_pos (a : A → ℝ) (ha : ∀ i, 0 < a i) (i : A) :
    0 < normalized a i := div_pos (ha i) (partition_pos a ha)

theorem normalized_sum (a : A → ℝ) (ha : ∀ i, 0 < a i) :
    ∑ i, normalized a i = 1 := by
  simp only [normalized, ← Finset.sum_div]
  exact div_self (partition_pos a ha).ne'

/-- Finite-action Gibbs variational inequality, allowing zero policy coordinates. -/
theorem finite_gibbs_bound (a p : A → ℝ) (ha : ∀ i, 0 < a i)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, p i * Real.log (a i)) - (∑ i, p i * Real.log (p i)) ≤
      Real.log (∑ i, a i) := by
  have hc : (∑ i, (p i * Real.log (normalized a i) - p i * Real.log (p i))) ≤ 0 := by
    calc
      _ ≤ ∑ i, (normalized a i - p i) :=
        Finset.sum_le_sum fun i _ => entropy_cell_bound (p i) (normalized a i) (hp i)
          (normalized_pos a ha i)
      _ = 0 := by rw [Finset.sum_sub_distrib, normalized_sum a ha, hsum]; ring
  have hl (i : A) : Real.log (normalized a i) = Real.log (a i) - Real.log (∑ j, a j) :=
    Real.log_div (ha i).ne' (partition_pos a ha).ne'
  have hs : (∑ i, p i * Real.log (normalized a i)) =
      (∑ i, p i * Real.log (a i)) - Real.log (∑ i, a i) := by
    simp_rw [hl, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [Finset.sum_sub_distrib, hs] at hc
  linarith

/-- The normalized action masses attain the log-partition value. -/
theorem finite_gibbs_value (a : A → ℝ) (ha : ∀ i, 0 < a i) :
    (∑ i, normalized a i * Real.log (a i)) -
      (∑ i, normalized a i * Real.log (normalized a i)) = Real.log (∑ i, a i) := by
  have hl (i : A) : Real.log (normalized a i) = Real.log (a i) - Real.log (∑ j, a j) :=
    Real.log_div (ha i).ne' (partition_pos a ha).ne'
  simp_rw [hl, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, normalized_sum a ha, one_mul]
  ring

/-- Finite Shannon entropy, with the continuous zero-coordinate convention. -/
def entropy (p : A → ℝ) : ℝ := -(∑ i, p i * Real.log (p i))

def gibbs (θ : ℝ) (q : A → ℝ) : A → ℝ := normalized (fun i => Real.exp (q i / θ))

def logPartition (θ : ℝ) (q : A → ℝ) : ℝ := θ * Real.log (∑ i, Real.exp (q i / θ))

/-- A finite routing policy's entropy-regularized value is bounded by the soft Bellman value. -/
theorem routing_variational_bound (θ : ℝ) (q p : A → ℝ) (hθ : 0 < θ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, p i * q i) + θ * entropy p ≤ logPartition θ q := by
  have h := finite_gibbs_bound (fun i => Real.exp (q i / θ)) p
    (fun i => Real.exp_pos _) hp hsum
  simp only [Real.log_exp] at h
  have hm := mul_le_mul_of_nonneg_left h hθ.le
  have he : θ * (∑ i, p i * (q i / θ)) = ∑ i, p i * q i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [mul_sub, he] at hm
  simpa only [logPartition, entropy, mul_neg, sub_eq_add_neg] using hm

/-- The finite Gibbs policy attains the soft Bellman value. -/
theorem routing_gibbs_value (θ : ℝ) (q : A → ℝ) (hθ : 0 < θ) :
    (∑ i, gibbs θ q i * q i) + θ * entropy (gibbs θ q) = logPartition θ q := by
  have h := finite_gibbs_value (fun i => Real.exp (q i / θ)) (fun i => Real.exp_pos _)
  simp only [Real.log_exp] at h
  have hm := congrArg (fun t : ℝ => θ * t) h
  have he : θ * (∑ i, normalized (fun j => Real.exp (q j / θ)) i * (q i / θ)) =
      ∑ i, normalized (fun j => Real.exp (q j / θ)) i * q i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [mul_sub, he] at hm
  simpa only [logPartition, entropy, gibbs, mul_neg, sub_eq_add_neg] using hm

/-- Exact finite-action variational formula for the entropy-regularized routing subgame. -/
theorem routing_variational (θ : ℝ) (q : A → ℝ) (hθ : 0 < θ) :
    IsGreatest ((fun p : A → ℝ => (∑ i, p i * q i) + θ * entropy p) ''
      {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}) (logPartition θ q) := by
  refine ⟨?_, ?_⟩
  · exact ⟨gibbs θ q, ⟨fun i => (normalized_pos _ (fun j => Real.exp_pos _) i).le,
      normalized_sum _ (fun j => Real.exp_pos _)⟩, routing_gibbs_value θ q hθ⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact routing_variational_bound θ q p hθ hp.1 hp.2

end FiniteGibbs

end Thesis.Regularization
