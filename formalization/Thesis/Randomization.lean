import Thesis.Coarsening
import Thesis.BackwardGames

/-! Ordinary-path overlap contraction and the alive-set mismatch used by the
randomization argument. Full RG paths must retain routing/stopping substeps;
ordinary surviving-path kernels may be contracted at activation boundaries. -/
noncomputable section
namespace Thesis.Randomization
open Finset Thesis.Games

variable {S : Type} [Fintype S]

/-- Complete any ordinary sub-stochastic row by absorbing missing mass. -/
def cemeteryCompletion (K : S → ℝ) : Option S → ℝ
  | none => 1 - ∑ s, K s
  | some s => K s

theorem cemeteryCompletion_normalized (K : S → ℝ) :
    (∑ s, cemeteryCompletion K s) = 1 := by
  simp [cemeteryCompletion, Fintype.sum_option]

theorem cemeteryCompletion_nonneg (K : S → ℝ) (hK : ∀ s, 0 ≤ K s) (hsum : ∑ s, K s ≤ 1)
    (s : Option S) : 0 ≤ cemeteryCompletion K s := by
  cases s with
  | none => exact sub_nonneg.mpr hsum
  | some s => exact hK s

/-- An entirely absorbed stochastic row has zero mass at every ordinary successor. -/
theorem dead_row_ordinary_zero (K : Option S → ℝ) (hK : ∀ s, 0 ≤ K s)
    (hsum : ∑ s, K s = 1) (hdead : K none = 1) : ∀ s, K (some s) = 0 := by
  have hs : (∑ s, K (some s)) = 0 := by
    rw [Fintype.sum_option] at hsum
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s ∈ Finset.univ) => hK (some s))).mp hs
  intro s
  exact hz s (Finset.mem_univ s)

/-- Correct ordinary-state alive-mismatch result, allowing routing leakage. -/
theorem thesis_alive_mismatch_ordinary (A B : Option S → ℝ)
    (hB : ∀ s, 0 ≤ B s) (hBsum : ∑ s, B s = 1) (hBdead : B none = 1) :
    (∑ s, Real.sqrt (A (some s) * B (some s))) = 0 := by
  have hz := dead_row_ordinary_zero B hB hBsum hBdead
  simp [hz]

/-- Stronger full-row mismatch is valid when the alive row has no leakage. -/
theorem thesis_alive_mismatch_full (A B : Option S → ℝ)
    (hAstop : A none = 0) (hB : ∀ s, 0 ≤ B s) (hBsum : ∑ s, B s = 1) (hBdead : B none = 1) :
    (∑ s, Real.sqrt (A s * B s)) = 0 := by
  have hz := dead_row_ordinary_zero B hB hBsum hBdead
  simp [Fintype.sum_option, hAstop, hz]

/-- Ordinary complete-path overlap, excluding every absorbed path. -/
def ordinaryOverlap (n : ℕ) (A B : ℕ → S → S → ℝ) (s : S) : ℝ :=
  backwardDP n (fun l u v => Real.sqrt (A l u v * B l u v)) (fun _ => 1) s

/-- This dynamic program is the overlap of complete surviving path sublaws. -/
theorem ordinaryOverlap_path_formula (n : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ l s t, 0 ≤ A l s t) (hB : ∀ l s t, 0 ≤ B l s t) (s : S) :
    ordinaryOverlap n A B s =
      ∑ path : Paths S n, Real.sqrt (pathLaw n A s path * pathLaw n B s path) :=
  (trajectory_overlap_eq_DP n A B hA hB s).symm

theorem backwardDP_nonneg (n : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ l s t, 0 ≤ K l s t) (f : S → ℝ) (hf : ∀ s, 0 ≤ f s) (s : S) :
    0 ≤ backwardDP n K f s := by
  induction n generalizing K s with
  | zero => exact hf s
  | succ n ih =>
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (hK 0 s t) (ih _ (fun l u v => hK (l+1) u v) t)

/-- All-depth contraction, with a bound only on the n layers actually traversed. -/
theorem backwardDP_geometric_bound (n : ℕ) (K : ℕ → S → S → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hK : ∀ l s t, 0 ≤ K l s t) (hrow : ∀ l < n, ∀ s, ∑ t, K l s t ≤ b) (s : S) :
    backwardDP n K (fun _ => 1) s ≤ b^n := by
  induction n generalizing K s with
  | zero => simp [backwardDP]
  | succ n ih =>
      have ht (t : S) : backwardDP n (fun l => K (l+1)) (fun _ => 1) t ≤ b^n :=
        ih _ (fun l u v => hK (l+1) u v)
          (fun l hl u => hrow (l+1) (Nat.succ_lt_succ hl) u) t
      calc
        _ ≤ ∑ t, K 0 s t * b^n :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (ht t) (hK 0 s t)
        _ = (∑ t, K 0 s t) * b^n := (Finset.sum_mul _ _ _).symm
        _ ≤ b * b^n := mul_le_mul_of_nonneg_right (hrow 0 (Nat.zero_lt_succ _) s) (pow_nonneg hb n)
        _ = b^(n+1) := by rw [pow_succ]; ring

/-- Exact source ordinary contraction bound under alive-set support assumptions.
The argument uses the actual geometric-mean kernel of the two model kernels. -/
theorem thesis_randomization_routing (n : ℕ) (A B : ℕ → S → S → ℝ)
    (aliveA aliveB : ℕ → S → Bool) (b : ℝ) (hb : 0 ≤ b) (_hb1 : b < 1)
    (hdeadA : ∀ l s, aliveA l s = false → ∀ t, A l s t = 0)
    (hdeadB : ∀ l s, aliveB l s = false → ∀ t, B l s t = 0)
    (hrow : ∀ l < n, ∀ s, aliveA l s = true ∧ aliveB l s = true →
      (∑ t, Real.sqrt (A l s t * B l s t)) ≤ b) (s : S) :
    ordinaryOverlap n A B s ≤ b^n := by
  apply backwardDP_geometric_bound n _ b hb (fun _ _ _ => Real.sqrt_nonneg _)
  intro l hl u
  cases ha : aliveA l u
  · simp [hdeadA l u ha, hb]
  · cases hbb : aliveB l u
    · simp [hdeadB l u hbb, hb]
    · exact hrow l hl u ⟨ha,hbb⟩

/-- Adding a sub-stochastic layer cannot increase prefix overlap, at every depth. -/
theorem prefix_overlap_monotone (n : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ l s t, 0 ≤ K l s t) (hrow : ∀ l s, ∑ t, K l s t ≤ 1) (s : S) :
    backwardDP (n+1) K (fun _ => 1) s ≤ backwardDP n K (fun _ => 1) s := by
  induction n generalizing K s with
  | zero => simpa [backwardDP] using hrow 0 s
  | succ n ih =>
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left
        (ih _ (fun l u v => hK (l+1) u v) (fun l u => hrow (l+1) u) t) (hK 0 s t)

theorem prefix_overlap_antitone (K : ℕ → S → S → ℝ)
    (hK : ∀ l s t, 0 ≤ K l s t) (hrow : ∀ l s, ∑ t, K l s t ≤ 1) (s : S) :
    Antitone (fun n => backwardDP n K (fun _ => 1) s) :=
  antitone_nat_of_succ_le (fun n => prefix_overlap_monotone n K hK hrow s)

theorem ordinaryOverlap_antitone (A B : ℕ → S → S → ℝ)
    (hA : ∀ l s t, 0 ≤ A l s t) (hB : ∀ l s t, 0 ≤ B l s t)
    (hArow : ∀ l s, ∑ t, A l s t ≤ 1) (hBrow : ∀ l s, ∑ t, B l s t ≤ 1) (s : S) :
    Antitone (fun n => ordinaryOverlap n A B s) := by
  apply prefix_overlap_antitone _ (fun _ _ _ => Real.sqrt_nonneg _) _ s
  intro l u
  calc
    _ ≤ ∑ t, (A l u t + B l u t)/2 :=
      Finset.sum_le_sum fun t _ => sqrt_overlap_le _ _ (hA l u t) (hB l u t)
    _ = ((∑ t, A l u t) + ∑ t, B l u t)/2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ 1 := by linarith [hArow l u, hBrow l u]

/-- Unrandomized layers below the randomized block cannot undo its contraction. -/
theorem thesis_randomization_routing_full_depth (n extra : ℕ) (A B : ℕ → S → S → ℝ)
    (aliveA aliveB : ℕ → S → Bool) (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1)
    (hA : ∀ l s t, 0 ≤ A l s t) (hB : ∀ l s t, 0 ≤ B l s t)
    (hArow : ∀ l s, ∑ t, A l s t ≤ 1) (hBrow : ∀ l s, ∑ t, B l s t ≤ 1)
    (hdeadA : ∀ l s, aliveA l s = false → ∀ t, A l s t = 0)
    (hdeadB : ∀ l s, aliveB l s = false → ∀ t, B l s t = 0)
    (hrow : ∀ l < n, ∀ s, aliveA l s = true ∧ aliveB l s = true →
      (∑ t, Real.sqrt (A l s t * B l s t)) ≤ b) (s : S) :
    ordinaryOverlap (n+extra) A B s ≤ b^n :=
  (ordinaryOverlap_antitone A B hA hB hArow hBrow s (Nat.le_add_right n extra)).trans
    (thesis_randomization_routing n A B aliveA aliveB b hb hb1 hdeadA hdeadB hrow s)

/-- A one-positive-edge alive routing row loses one half if the empty negative
stream is not absorbed. Its residual cemetery completion restores normalization. -/
def positiveOnlyOrdinary (p : Bool) : ℝ := if p then 0 else 1/2

theorem paper_empty_stream_counterexample :
    (∑ p, positiveOnlyOrdinary p) = (1/2 : ℝ) ∧
    cemeteryCompletion positiveOnlyOrdinary none = (1/2 : ℝ) := by
  norm_num [positiveOnlyOrdinary, cemeteryCompletion, Fintype.sum_bool]

/-- The source's missing nonnegative-contraction premise is necessary even for a dead root. -/
theorem paper_negative_contraction_counterexample :
    (∀ _s : Unit, (false = true ∧ false = true) → (0 : ℝ) ≤ -1) ∧
    ¬ ordinaryOverlap 1 (fun _ (_ : Unit) _ => 0) (fun _ (_ : Unit) _ => 0) () ≤ (-1 : ℝ)^1 := by
  norm_num [ordinaryOverlap, backwardDP]

end Thesis.Randomization
