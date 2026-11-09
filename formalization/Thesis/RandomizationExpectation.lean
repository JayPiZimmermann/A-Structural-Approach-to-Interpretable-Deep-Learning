import Thesis.Randomization
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! The conditional-alive assumption gives the paper's geometric expectation
bound by the actual conditional-expectation pull-out property, not by assuming
an expectation recurrence. Randomness may live on an arbitrary probability space. -/
noncomputable section
namespace Thesis.RandomizationExpectation
open MeasureTheory Filter Finset Thesis.Games Thesis.Randomization
open scoped MeasureTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Nonnegative above-layer measurable mass is thinned by a conditional alive bound. -/
theorem conditional_thinning (μ : Measure Ω) (ℱ : MeasurableSpace Ω) (hm : ℱ ≤ mΩ)
    [SigmaFinite (μ.trim hm)] (g a : Ω → ℝ) (η : ℝ)
    (hg : Integrable g μ) (ha : Integrable a μ) (hga : Integrable (g*a) μ)
    (hgm : AEStronglyMeasurable[ℱ] g μ) (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hcond : ∀ᵐ ω ∂μ, μ[a | ℱ] ω ≤ η) :
    (∫ ω, g ω*a ω ∂μ) ≤ η * ∫ ω, g ω ∂μ := by
  have hpull := condExp_mul_of_aestronglyMeasurable_left hgm hga ha
  have hint : Integrable (g * μ[a | ℱ]) μ := integrable_condExp.congr hpull
  calc
    _ = ∫ ω, μ[g*a | ℱ] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, g ω * μ[a | ℱ] ω ∂μ := integral_congr_ae hpull
    _ ≤ ∫ ω, g ω * η ∂μ := by
      apply integral_mono_ae hint (hg.mul_const η)
      filter_upwards [hg0, hcond] with ω hgω haω
      exact mul_le_mul_of_nonneg_left haω hgω
    _ = η * ∫ ω, g ω ∂μ := by rw [integral_mul_const]; ring

variable {S : Type} [Fintype S] [DecidableEq S]

omit mΩ in
/-- Forward overlap mass on ordinary states, with a deterministic ordinary root. -/
def randomPrefix (K : ℕ → Ω → S → S → ℝ) (s₀ : S) : ℕ → Ω → S → ℝ
  | 0, _, s => if s = s₀ then 1 else 0
  | n+1, ω, t => transport (randomPrefix K s₀ n ω) (K n ω) t

omit mΩ in
/-- Ordinary prefix mass after n randomized layers. -/
def randomMass (K : ℕ → Ω → S → S → ℝ) (s₀ : S) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ s, randomPrefix K s₀ n ω s

omit mΩ in
theorem randomPrefix_nonneg (K : ℕ → Ω → S → S → ℝ) (s₀ : S)
    (hK : ∀ n ω s t, 0 ≤ K n ω s t) (n : ℕ) (ω : Ω) (s : S) :
    0 ≤ randomPrefix K s₀ n ω s := by
  induction n generalizing s with
  | zero => simp only [randomPrefix]; split_ifs <;> norm_num
  | succ n ih => exact transport_nonneg _ _ ih (hK n ω) s

omit mΩ in
theorem randomMass_zero (K : ℕ → Ω → S → S → ℝ) (s₀ : S) (ω : Ω) :
    randomMass K s₀ 0 ω = 1 := by simp [randomMass, randomPrefix]

omit mΩ in
theorem randomMass_step_le (K : ℕ → Ω → S → S → ℝ) (s₀ : S)
    (hK : ∀ n ω s t, 0 ≤ K n ω s t) (n : ℕ) (a : S → Ω → ℝ)
    (hrow : ∀ ω s, ∑ t, K n ω s t ≤ a s ω) (ω : Ω) :
    randomMass K s₀ (n+1) ω ≤ ∑ s, randomPrefix K s₀ n ω s * a s ω := by
  unfold randomMass
  change (∑ t, transport (randomPrefix K s₀ n ω) (K n ω) t) ≤ _
  rw [transport_mass]
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left (hrow ω s) (randomPrefix_nonneg K s₀ hK n ω s)

/-- One randomized overlap layer, using the actual conditional-alive hypothesis. -/
theorem expected_randomMass_step (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : MeasurableSpace Ω) (hm : ℱ ≤ mΩ)
    (K : ℕ → Ω → S → S → ℝ) (s₀ : S) (n : ℕ) (a : S → Ω → ℝ) (η : ℝ)
    (hK : ∀ n ω s t, 0 ≤ K n ω s t)
    (hrow : ∀ ω s, ∑ t, K n ω s t ≤ a s ω)
    (hg : ∀ s, Integrable (fun ω => randomPrefix K s₀ n ω s) μ)
    (ha : ∀ s, Integrable (a s) μ)
    (hga : ∀ s, Integrable (fun ω => randomPrefix K s₀ n ω s * a s ω) μ)
    (hgm : ∀ s, AEStronglyMeasurable[ℱ] (fun ω => randomPrefix K s₀ n ω s) μ)
    (hcond : ∀ s, ∀ᵐ ω ∂μ, μ[a s | ℱ] ω ≤ η)
    (hnext : Integrable (randomMass K s₀ (n+1)) μ) :
    (∫ ω, randomMass K s₀ (n+1) ω ∂μ) ≤ η * ∫ ω, randomMass K s₀ n ω ∂μ := by
  calc
    _ ≤ ∫ ω, ∑ s, randomPrefix K s₀ n ω s * a s ω ∂μ :=
      integral_mono hnext (integrable_finsetSum univ (fun s _ => hga s))
        (randomMass_step_le K s₀ hK n a hrow)
    _ = ∑ s, ∫ ω, randomPrefix K s₀ n ω s * a s ω ∂μ :=
      integral_finsetSum univ (fun s _ => hga s)
    _ ≤ ∑ s, η * ∫ ω, randomPrefix K s₀ n ω s ∂μ := by
      apply Finset.sum_le_sum
      intro s _
      exact conditional_thinning (mΩ := mΩ) μ ℱ hm (fun ω => randomPrefix K s₀ n ω s) (a s) η (hg s) (ha s) (hga s) (hgm s)
        (ae_of_all _ (fun ω => randomPrefix_nonneg K s₀ hK n ω s)) (hcond s)
    _ = η * ∫ ω, randomMass K s₀ n ω ∂μ := by
      rw [← Finset.mul_sum, ← integral_finsetSum univ (fun s _ => hg s)]
      rfl

/-- Thesis `ptnb:thm:rand-adf`: geometric expected ordinary-overlap contraction
on an arbitrary probability space. K is the ordinary geometric-mean model kernel;
the alive indicator bounds its row mass, and the displayed conditional expectation
is exactly the paper's above-layer conditional-alive assumption. Integrability
and above-layer measurability are explicit analytic side conditions. -/
theorem thesis_randomization_stopping (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (K : ℕ → Ω → S → S → ℝ) (s₀ : S) (alive : ℕ → S → Ω → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (hK : ∀ n ω s t, 0 ≤ K n ω s t)
    (hrow : ∀ n ω s, ∑ t, K n ω s t ≤ alive n s ω)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix K s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (alive n s) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix K s₀ n ω s * alive n s ω) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n] (fun ω => randomPrefix K s₀ n ω s) μ)
    (n : ℕ) (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ, μ[alive l s | ℱ l] ω ≤ η) :
    (∫ ω, randomMass K s₀ n ω ∂μ) ≤ η^n := by
  induction n with
  | zero => simp [randomMass_zero]
  | succ n ih =>
      have hi := ih (fun l hl s => hcond l (Nat.lt_succ_of_lt hl) s)
      have hint : Integrable (randomMass K s₀ (n+1)) μ :=
        integrable_finsetSum univ (fun s _ => hg (n+1) s)
      calc
        _ ≤ η * ∫ ω, randomMass K s₀ n ω ∂μ :=
          expected_randomMass_step μ (ℱ n) (hm n) K s₀ n (alive n) η hK (hrow n)
            (hg n) (ha n) (hga n) (hgm n) (hcond n (Nat.lt_succ_self n)) hint
        _ ≤ η * η^n := mul_le_mul_of_nonneg_left hi hη
        _ = η^(n+1) := by rw [pow_succ]; ring

omit mΩ [DecidableEq S] in
/-- Appending the last ordinary-kernel layer in the backward dynamic program. -/
theorem backwardDP_append_one (n : ℕ) (K : ℕ → S → S → ℝ) (f : S → ℝ) (s : S) :
    backwardDP (n+1) K f s = backwardDP n K (fun u => ∑ t, K n u t * f t) s := by
  induction n generalizing K s with
  | zero => rfl
  | succ n ih =>
      change (∑ t, K 0 s t * backwardDP (n+1) (fun l => K (l+1)) f t) =
        ∑ t, K 0 s t * backwardDP n (fun l => K (l+1))
          (fun u => ∑ t, K (n+1) u t * f t) t
      apply Finset.sum_congr rfl
      intro t _
      rw [ih]

omit mΩ in
/-- Forward propagated overlap masses and the path dynamic program are dual. -/
theorem randomPrefix_weighted (K : ℕ → Ω → S → S → ℝ) (s₀ : S) (n : ℕ) (ω : Ω)
    (f : S → ℝ) :
    (∑ s, randomPrefix K s₀ n ω s * f s) = backwardDP n (fun l => K l ω) f s₀ := by
  induction n generalizing f with
  | zero => simp [randomPrefix, backwardDP]
  | succ n ih =>
      change (∑ t, (∑ s, randomPrefix K s₀ n ω s * K n ω s t) * f t) = _
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [ih]
      exact (backwardDP_append_one n (fun l => K l ω) f s₀).symm

omit mΩ in
def modelKernel (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) : ℕ → Ω → S → S → ℝ :=
  fun n ω s t => Real.sqrt (A n s t * B n ω s t)

omit mΩ [DecidableEq S] in
theorem modelKernel_row_bound (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ)
    (alive : ℕ → Ω → S → Bool)
    (hA : ∀ n s t, 0 ≤ A n s t) (hB : ∀ n ω s t, 0 ≤ B n ω s t)
    (hArow : ∀ n s, ∑ t, A n s t ≤ 1) (hBrow : ∀ n ω s, ∑ t, B n ω s t ≤ 1)
    (hdead : ∀ n ω s, alive n ω s = false → ∀ t, B n ω s t = 0) (n : ℕ) (ω : Ω) (s : S) :
    (∑ t, modelKernel A B n ω s t) ≤ if alive n ω s then 1 else 0 := by
  cases h : alive n ω s
  · simp [modelKernel, hdead n ω s h]
  · simp only [ite_true]
    calc
      _ ≤ ∑ t, (A n s t + B n ω s t)/2 :=
        Finset.sum_le_sum fun t _ => sqrt_overlap_le _ _ (hA n s t) (hB n ω s t)
      _ = ((∑ t, A n s t) + ∑ t, B n ω s t)/2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ 1 := by linarith [hArow n s, hBrow n ω s]

omit mΩ in
theorem randomMass_model_overlap (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ)
    (s₀ : S) (n : ℕ) (ω : Ω) :
    randomMass (modelKernel A B) s₀ n ω = ordinaryOverlap n A (fun l => B l ω) s₀ := by
  change (∑ s, randomPrefix (modelKernel A B) s₀ n ω s) =
    backwardDP n (fun l => modelKernel A B l ω) (fun _ => 1) s₀
  simpa only [mul_one] using randomPrefix_weighted (modelKernel A B) s₀ n ω (fun _ => 1)

/-- The paper's SG randomization theorem for explicit trained/random model kernels.
The conditional-alive hypothesis is assumed exactly as in the source; no claim is
made that a Gaussian weight distribution alone implies that conditional bound. -/
theorem thesis_rand_adf_models (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) (alive : ℕ → Ω → S → Bool)
    (s₀ : S) (η : ℝ) (hη : 0 ≤ η)
    (hA : ∀ n s t, 0 ≤ A n s t) (hB : ∀ n ω s t, 0 ≤ B n ω s t)
    (hArow : ∀ n s, ∑ t, A n s t ≤ 1) (hBrow : ∀ n ω s, ∑ t, B n ω s t ≤ 1)
    (hdead : ∀ n ω s, alive n ω s = false → ∀ t, B n ω s t = 0)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (fun ω => if alive n ω s then (1:ℝ) else 0) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s *
      (if alive n ω s then (1:ℝ) else 0)) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n] (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (n : ℕ) (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ,
      μ[(fun ω => if alive l ω s then (1:ℝ) else 0) | ℱ l] ω ≤ η) :
    (∫ ω, ordinaryOverlap n A (fun l => B l ω) s₀ ∂μ) ≤ η^n := by
  have h := thesis_randomization_stopping μ ℱ hm (modelKernel A B) s₀
    (fun n s ω => if alive n ω s then (1:ℝ) else 0) η hη
    (fun _ _ _ _ => Real.sqrt_nonneg _)
    (modelKernel_row_bound A B alive hA hB hArow hBrow hdead) hg ha hga hgm n hcond
  simpa only [randomMass_model_overlap] using h

/-- Fixed layers below the randomized block preserve the geometric expectation bound. -/
theorem thesis_rand_adf_full_depth (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) (alive : ℕ → Ω → S → Bool)
    (s₀ : S) (η : ℝ) (hη : 0 ≤ η)
    (hA : ∀ n s t, 0 ≤ A n s t) (hB : ∀ n ω s t, 0 ≤ B n ω s t)
    (hArow : ∀ n s, ∑ t, A n s t ≤ 1) (hBrow : ∀ n ω s, ∑ t, B n ω s t ≤ 1)
    (hdead : ∀ n ω s, alive n ω s = false → ∀ t, B n ω s t = 0)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (fun ω => if alive n ω s then (1:ℝ) else 0) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s *
      (if alive n ω s then (1:ℝ) else 0)) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n] (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (n extra : ℕ) (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ,
      μ[(fun ω => if alive l ω s then (1:ℝ) else 0) | ℱ l] ω ≤ η) :
    (∫ ω, ordinaryOverlap (n+extra) A (fun l => B l ω) s₀ ∂μ) ≤ η^n := by
  have hprefix : Integrable (fun ω => ordinaryOverlap n A (fun l => B l ω) s₀) μ := by
    have h := integrable_finsetSum univ (fun s _ => hg n s)
    exact h.congr (ae_of_all _ (fun ω => randomMass_model_overlap A B s₀ n ω))
  have hfull : Integrable (fun ω => ordinaryOverlap (n+extra) A (fun l => B l ω) s₀) μ := by
    have h := integrable_finsetSum univ (fun s _ => hg (n+extra) s)
    exact h.congr (ae_of_all _ (fun ω => randomMass_model_overlap A B s₀ (n+extra) ω))
  have hmono := integral_mono hfull hprefix (fun ω =>
    ordinaryOverlap_antitone A (fun l => B l ω) hA (fun l u v => hB l ω u v)
      hArow (fun l u => hBrow l ω u) s₀ (Nat.le_add_right n extra))
  exact hmono.trans (thesis_rand_adf_models μ ℱ hm A B alive s₀ η hη hA hB hArow hBrow
    hdead hg ha hga hgm n hcond)

omit mΩ [Fintype S] [DecidableEq S] in
/-- Pointwise threshold bound for the survival-conditioned squared Hellinger term. -/
theorem survival_threshold_pointwise (c Z z : ℝ) (hz : 0 < z) (hc : 0 ≤ c) :
    (if z ≤ Z then (1:ℝ) else 0) - c / Real.sqrt z ≤
      (if z ≤ Z then 1 - c / Real.sqrt Z else 0) := by
  by_cases h : z ≤ Z
  · have hZ : 0 < Z := lt_of_lt_of_le hz h
    have hs : Real.sqrt z ≤ Real.sqrt Z := Real.sqrt_le_sqrt h
    have hd : c / Real.sqrt Z ≤ c / Real.sqrt z := by
      apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hZ) (Real.sqrt_pos.mpr hz)).2
      exact mul_le_mul_of_nonneg_left hs hc
    simp only [h, ite_true]
    linarith
  · simp only [h, ite_false, zero_sub]
    exact neg_nonpos.mpr (div_nonneg hc (Real.sqrt_nonneg z))

/-- The conditioned-survival expectation bound in `ptnb:thm:rand-adf`.
The input C can be instantiated by η^N from `thesis_rand_adf_models`. -/
theorem thesis_conditioned_survival_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c Z : Ω → ℝ) (z C : ℝ) (hz : 0 < z)
    (hc0 : ∀ᵐ ω ∂μ, 0 ≤ c ω) (hc : Integrable c μ)
    (hE : MeasurableSet {ω | z ≤ Z ω})
    (hH : Integrable (fun ω => if z ≤ Z ω then 1 - c ω / Real.sqrt (Z ω) else 0) μ)
    (hbound : (∫ ω, c ω ∂μ) ≤ C) :
    μ.real {ω | z ≤ Z ω} - C / Real.sqrt z ≤
      ∫ ω, (if z ≤ Z ω then 1 - c ω / Real.sqrt (Z ω) else 0) ∂μ := by
  have hfun : ({ω | z ≤ Z ω}.indicator (fun _ => (1:ℝ))) =
      (fun ω => if z ≤ Z ω then (1:ℝ) else 0) := by
    funext ω
    rfl
  have hI : Integrable (fun ω => if z ≤ Z ω then (1:ℝ) else 0) μ := by
    rw [← hfun]
    exact (integrable_const (1:ℝ)).indicator hE
  have hp : (∫ ω, (if z ≤ Z ω then (1:ℝ) else 0) ∂μ) = μ.real {ω | z ≤ Z ω} := by
    rw [← hfun]
    exact integral_indicator_one hE
  have hmono := integral_mono_ae (hI.sub (hc.div_const (Real.sqrt z))) hH
    (hc0.mono fun ω hω => survival_threshold_pointwise (c ω) (Z ω) z hz hω)
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub hI (hc.div_const (Real.sqrt z)), integral_div, hp] at hmono
  have hd : (∫ ω, c ω ∂μ) / Real.sqrt z ≤ C / Real.sqrt z :=
    div_le_div_of_nonneg_right hbound (Real.sqrt_nonneg z)
  linarith

end Thesis.RandomizationExpectation
