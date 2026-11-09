import Thesis.ConditionedSurvival
import Thesis.Randomization

/-! Actual full-path marginals and Hellinger formulas for the survival-conditioned
law, composed with the zero-support conditioning theorem. -/
noncomputable section
set_option autoImplicit false
namespace Thesis.ConditionedSurvival
open Finset Thesis.Games Thesis.Randomization
open scoped Classical
variable {S : Type} [Fintype S]

/-- The original prefix occupation, before any restriction on later survival. -/
def prefixMass (n : ℕ) (K : ℕ → S → S → ℝ) (s t : S) : ℝ := by
  classical
  exact ∑ path : Paths S n, if endpoint n s path = t then pathLaw n K s path else 0

/-- The actual time-i marginal of the full length-N path sublaw. -/
def timeMass (N i : ℕ) (K : ℕ → S → S → ℝ) (s t : S) : ℝ := by
  classical
  exact ∑ path : Paths S N, if stateAt N s path i = t then pathLaw N K s path else 0

theorem prefixMass_zero (K : ℕ → S → S → ℝ) (s t : S) :
    prefixMass 0 K s t = if s = t then 1 else 0 := by
  classical
  change (∑ _ : Unit, (if s = t then (1 : ℝ) else 0)) = _
  simp

theorem timeMass_zero (N : ℕ) (K : ℕ → S → S → ℝ) (s t : S) :
    timeMass N 0 K s t = if s = t then survival N K 0 s else 0 := by
  classical
  have hz (path : Paths S N) : stateAt N s path 0 = s := by cases N <;> rfl
  simp only [timeMass, hz]
  by_cases he : s = t
  · simp [he, survival_eq_path_mass]
  · simp [he]

theorem prefixMass_succ (n : ℕ) (K : ℕ → S → S → ℝ) (s t : S) :
    prefixMass (n+1) K s t = ∑ u, K 0 s u * prefixMass n (fun i => K (i+1)) u t := by
  classical
  change (∑ path : S × Paths S n, if endpoint n path.1 path.2 = t
    then K 0 s path.1 * pathLaw n (fun i => K (i+1)) path.1 path.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [prefixMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro path _
  split_ifs <;> simp

theorem timeMass_succ (N i : ℕ) (K : ℕ → S → S → ℝ) (s t : S) :
    timeMass (N+1) (i+1) K s t =
      ∑ u, K 0 s u * timeMass N i (fun j => K (j+1)) u t := by
  classical
  change (∑ path : S × Paths S N, if stateAt N path.1 path.2 i = t
    then K 0 s path.1 * pathLaw N (fun j => K (j+1)) path.1 path.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [timeMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro path _
  split_ifs <;> simp

theorem survival_shift (N i : ℕ) (K : ℕ → S → S → ℝ) (s : S) :
    survival N (fun j => K (j+1)) i s = survival (N+1) K (i+1) s := by
  have hn : (N+1)-(i+1) = N-i := by omega
  simp only [survival, hn]
  congr 1
  funext j
  congr 1
  omega

/-- Splitting the actual full trajectory sum at its time-i state separates
the original prefix mass and the remaining backward survival probability. -/
theorem timeMass_factorization (N i : ℕ) (hi : i ≤ N)
    (K : ℕ → S → S → ℝ) (s t : S) :
    timeMass N i K s t = prefixMass i K s t * survival N K i t := by
  classical
  induction i generalizing N K s with
  | zero =>
    rw [timeMass_zero, prefixMass_zero]
    split_ifs with he
    · subst t
      simp
    · simp
  | succ i ih =>
    cases N with
    | zero => omega
    | succ N =>
      rw [timeMass_succ, prefixMass_succ, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      rw [ih N (by omega), survival_shift]
      ring

/-- Source conditioned-alpha identity for a marginal of the full conditioned
trajectory distribution, not merely a renormalized prefix definition. -/
theorem conditioned_time_marginal (N i : ℕ) (hi : i ≤ N)
    (K : ℕ → S → S → ℝ) (hK : ∀ j s t, 0 ≤ K j s t)
    (s : S) (hs : 0 < survival N K 0 s) (t : S) :
    timeMass N i (kernel K (survival N K)) s t =
      prefixMass i K s t * survival N K i t / survival N K 0 s := by
  classical
  have he : timeMass N i (kernel K (survival N K)) s t =
      timeMass N i K s t / survival N K 0 s := by
    unfold timeMass
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro path _
    rw [survival_conditioned_path N K hK s hs]
    split_ifs <;> simp
  rw [he, timeMass_factorization N i hi]

omit [Fintype S] in
theorem pathLaw_nonnegative (n : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ i s t, 0 ≤ K i s t) (s : S) (path : Paths S n) :
    0 ≤ pathLaw n K s path := by
  induction n generalizing K s with
  | zero => exact zero_le_one
  | succ n ih =>
      exact mul_nonneg (hK 0 s path.1)
        (ih (fun i => K (i+1)) (fun i => hK (i+1)) path.1 path.2)

/-- Geometric-mean conditioned edge identity, including rows where either
potential vanishes. The guarded kernels agree with totalized real quotients. -/
theorem conditioned_geometric_kernel (N : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
    (i : ℕ) (s t : S) :
    Real.sqrt (kernel A (survival N A) i s t * kernel B (survival N B) i s t) =
      Real.sqrt (A i s t * B i s t) *
        Real.sqrt (survival N A (i+1) t * survival N B (i+1) t) /
        Real.sqrt (survival N A i s * survival N B i s) := by
  rw [kernel_eq_ratio A _ (survival_nonnegative N A hA),
    kernel_eq_ratio B _ (survival_nonnegative N B hB)]
  have he : (A i s t * survival N A (i+1) t / survival N A i s) *
      (B i s t * survival N B (i+1) t / survival N B i s) =
      (A i s t * B i s t) * (survival N A (i+1) t * survival N B (i+1) t) /
      (survival N A i s * survival N B i s) := by ring
  rw [he, Real.sqrt_div (mul_nonneg (mul_nonneg (hA i s t) (hB i s t))
    (mul_nonneg (survival_nonnegative N A hA (i+1) t)
      (survival_nonnegative N B hB (i+1) t))),
    Real.sqrt_mul (mul_nonneg (hA i s t) (hB i s t))]

theorem conditioned_overlap_DP (N : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t) (s : S) :
    overlap (pathLaw N (kernel A (survival N A)) s)
      (pathLaw N (kernel B (survival N B)) s) =
    backwardDP N (fun i u v => Real.sqrt
      (kernel A (survival N A) i u v * kernel B (survival N B) i u v)) (fun _ => 1) s :=
  trajectory_overlap_eq_DP N _ _
    (kernel_nonnegative A _ hA (survival_nonnegative N A hA))
    (kernel_nonnegative B _ hB (survival_nonnegative N B hB)) s

theorem conditioned_overlap_paths (N : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t) (s : S) :
    overlap (pathLaw N (kernel A (survival N A)) s)
      (pathLaw N (kernel B (survival N B)) s) =
    ∑ path : Paths S N, pathLaw N (fun i u v => Real.sqrt
      (kernel A (survival N A) i u v * kernel B (survival N B) i u v)) s path := by
  unfold overlap
  apply Finset.sum_congr rfl
  intro path _
  exact path_geometric_mean N _ _
    (kernel_nonnegative A _ hA (survival_nonnegative N A hA))
    (kernel_nonnegative B _ hB (survival_nonnegative N B hB)) s path

/-- Normalizing both actual surviving path sublaws rescales their full path
Bhattacharyya overlap by the geometric mean of their computed survival masses. -/
theorem conditioned_overlap (N : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
    (s : S) (hsA : 0 < survival N A 0 s) (hsB : 0 < survival N B 0 s) :
    overlap (pathLaw N (kernel A (survival N A)) s)
      (pathLaw N (kernel B (survival N B)) s) =
    ordinaryOverlap N A B s / Real.sqrt (survival N A 0 s * survival N B 0 s) := by
  have heA : pathLaw N (kernel A (survival N A)) s =
      fun path => pathLaw N A s path / survival N A 0 s :=
    funext (survival_conditioned_path N A hA s hsA)
  have heB : pathLaw N (kernel B (survival N B)) s =
      fun path => pathLaw N B s path / survival N B 0 s :=
    funext (survival_conditioned_path N B hB s hsB)
  rw [heA, heB, survival_overlap _ _ _ _
    (pathLaw_nonnegative N A hA s) (pathLaw_nonnegative N B hB s) hsA hsB]
  rw [ordinaryOverlap_path_formula N A B hA hB]
  rfl

theorem conditioned_hellinger (N : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
    (s : S) (hsA : 0 < survival N A 0 s) (hsB : 0 < survival N B 0 s) :
    (1/2 : ℝ) * (∑ path : Paths S N,
      (Real.sqrt (pathLaw N (kernel A (survival N A)) s path) -
       Real.sqrt (pathLaw N (kernel B (survival N B)) s path))^2) =
    1 - ordinaryOverlap N A B s / Real.sqrt (survival N A 0 s * survival N B 0 s) := by
  rw [hellinger_identity _ _
    (pathLaw_nonnegative N _ (kernel_nonnegative A _ hA (survival_nonnegative N A hA)) s)
    (pathLaw_nonnegative N _ (kernel_nonnegative B _ hB (survival_nonnegative N B hB)) s)
    (survival_conditioned_normalized N A hA s hsA)
    (survival_conditioned_normalized N B hB s hsB),
    conditioned_overlap N A B hA hB s hsA hsB]

/-- The remaining source conditioned-survival clauses, with actual full-path
marginals, path-product overlap, the DP pass, and normalized Hellinger distance.
Only the two initial survival probabilities need be strictly positive. -/
theorem conditioned_survival_statistics (N : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
    (hArow : ∀ i s, ∑ t, A i s t ≤ 1) (hBrow : ∀ i s, ∑ t, B i s t ≤ 1)
    (s : S) (hsA : 0 < survival N A 0 s) (hsB : 0 < survival N B 0 s) :
    (survival N A 0 s ≤ 1 ∧ survival N B 0 s ≤ 1) ∧
    (∀ i ≤ N, ∀ t,
      timeMass N i (kernel A (survival N A)) s t =
        prefixMass i A s t * survival N A i t / survival N A 0 s ∧
      timeMass N i (kernel B (survival N B)) s t =
        prefixMass i B s t * survival N B i t / survival N B 0 s) ∧
    (∀ i u v,
      Real.sqrt (kernel A (survival N A) i u v * kernel B (survival N B) i u v) =
      Real.sqrt (A i u v * B i u v) *
        Real.sqrt (survival N A (i+1) v * survival N B (i+1) v) /
        Real.sqrt (survival N A i u * survival N B i u)) ∧
    (overlap (pathLaw N (kernel A (survival N A)) s)
      (pathLaw N (kernel B (survival N B)) s) =
      ∑ path : Paths S N, pathLaw N (fun i u v => Real.sqrt
        (kernel A (survival N A) i u v * kernel B (survival N B) i u v)) s path) ∧
    (overlap (pathLaw N (kernel A (survival N A)) s)
      (pathLaw N (kernel B (survival N B)) s) =
      backwardDP N (fun i u v => Real.sqrt
        (kernel A (survival N A) i u v * kernel B (survival N B) i u v)) (fun _ => 1) s) ∧
    (overlap (pathLaw N (kernel A (survival N A)) s)
      (pathLaw N (kernel B (survival N B)) s) =
      ordinaryOverlap N A B s / Real.sqrt (survival N A 0 s * survival N B 0 s)) ∧
    ((1/2 : ℝ) * (∑ path : Paths S N,
      (Real.sqrt (pathLaw N (kernel A (survival N A)) s path) -
       Real.sqrt (pathLaw N (kernel B (survival N B)) s path))^2) =
      1 - ordinaryOverlap N A B s / Real.sqrt (survival N A 0 s * survival N B 0 s)) := by
  exact ⟨⟨survival_le_one N A hA hArow 0 s, survival_le_one N B hB hBrow 0 s⟩,
    fun i hi t => ⟨conditioned_time_marginal N i hi A hA s hsA t,
      conditioned_time_marginal N i hi B hB s hsB t⟩,
    conditioned_geometric_kernel N A B hA hB,
    conditioned_overlap_paths N A B hA hB s,
    conditioned_overlap_DP N A B hA hB s,
    conditioned_overlap N A B hA hB s hsA hsB,
    conditioned_hellinger N A B hA hB s hsA hsB⟩

/-- Source bc-monotone on actual full Markov prefix laws. The ambient state
space may include a cemetery. Row stochasticity makes the squared-distance
formula the actual Hellinger distance at every depth. -/
theorem trajectory_bc_monotone (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
    (hArow : ∀ i s, ∑ t, A i s t = 1) (hBrow : ∀ i s, ∑ t, B i s t = 1) (s : S) :
    overlap (pathLaw 0 A s) (pathLaw 0 B s) = 1 ∧
    (∀ n, 0 ≤ overlap (pathLaw n A s) (pathLaw n B s) ∧
      overlap (pathLaw n A s) (pathLaw n B s) ≤ 1) ∧
    Antitone (fun n => overlap (pathLaw n A s) (pathLaw n B s)) ∧
    Monotone (fun n => (1/2 : ℝ) * ∑ path : Paths S n,
      (Real.sqrt (pathLaw n A s path) - Real.sqrt (pathLaw n B s path))^2) ∧
    (∀ n, (1/2 : ℝ) * (∑ path : Paths S n,
      (Real.sqrt (pathLaw n A s path) - Real.sqrt (pathLaw n B s path))^2) =
      1 - overlap (pathLaw n A s) (pathLaw n B s)) ∧
    (∀ n, overlap (pathLaw n A s) (pathLaw n B s) =
      backwardDP n (fun i u v => Real.sqrt (A i u v * B i u v)) (fun _ => 1) s) := by
  have he (n : ℕ) : overlap (pathLaw n A s) (pathLaw n B s) = ordinaryOverlap n A B s :=
    trajectory_overlap_eq_DP n A B hA hB s
  have ha : Antitone (fun n => overlap (pathLaw n A s) (pathLaw n B s)) := by
    simpa only [he] using ordinaryOverlap_antitone A B hA hB
      (fun i u => (hArow i u).le) (fun i u => (hBrow i u).le) s
  have hzero : overlap (pathLaw 0 A s) (pathLaw 0 B s) = 1 := by rw [he]; rfl
  have hH (n : ℕ) : (1/2 : ℝ) * (∑ path : Paths S n,
      (Real.sqrt (pathLaw n A s path) - Real.sqrt (pathLaw n B s path))^2) =
      1 - overlap (pathLaw n A s) (pathLaw n B s) :=
    hellinger_identity _ _ (pathLaw_nonnegative n A hA s) (pathLaw_nonnegative n B hB s)
      (path_law_normalized n A hArow s) (path_law_normalized n B hBrow s)
  refine ⟨hzero, fun n => ⟨overlap_nonneg _ _, ?_⟩, ha, ?_, hH, he⟩
  · simpa only [hzero] using ha (Nat.zero_le n)
  · intro n m hnm
    dsimp only
    rw [hH n, hH m]
    exact sub_le_sub_left (ha hnm) 1

end Thesis.ConditionedSurvival
