import Thesis.Games

/-! Conditioning a finite substochastic path law on survival, including zero
survival states. The transition is normalized only at positive-potential states;
all other rows are zero and are proved unreachable from a positive initial
potential under the conditioned path law. -/
noncomputable section
set_option autoImplicit false
namespace Thesis.ConditionedSurvival
open Finset Thesis.Games
variable {S : Type} [Fintype S]

def kernel (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ)
    (i : ℕ) (s t : S) : ℝ :=
  if 0 < h i s then K i s t * h (i+1) t / h i s else 0

omit [Fintype S] in
theorem kernel_eq_ratio (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ)
    (hh : ∀ i s, 0 ≤ h i s) (i : ℕ) (s t : S) :
    kernel K h i s t = K i s t * h (i+1) t / h i s := by
  by_cases hp : 0 < h i s
  · simp [kernel, hp]
  · have hz : h i s = 0 := le_antisymm (le_of_not_gt hp) (hh i s)
    simp [kernel, hz]

omit [Fintype S] in
theorem kernel_nonnegative (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ)
    (hK : ∀ i s t, 0 ≤ K i s t) (hh : ∀ i s, 0 ≤ h i s)
    (i : ℕ) (s t : S) : 0 ≤ kernel K h i s t := by
  rw [kernel_eq_ratio K h hh]
  exact div_nonneg (mul_nonneg (hK i s t) (hh (i+1) t)) (hh i s)

omit [Fintype S] in
theorem kernel_zero_source (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ)
    (i : ℕ) (s t : S) (hz : h i s = 0) : kernel K h i s t = 0 := by
  simp [kernel, hz]

omit [Fintype S] in
theorem kernel_zero_target (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ)
    (i : ℕ) (s t : S) (hz : h (i+1) t = 0) : kernel K h i s t = 0 := by
  simp [kernel, hz]

theorem kernel_row_sum (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ)
    (i : ℕ) (s : S) (hrec : h i s = ∑ t, K i s t * h (i+1) t) :
    (∑ t, kernel K h i s t) = if 0 < h i s then 1 else 0 := by
  by_cases hp : 0 < h i s
  · simp only [kernel, hp, ite_true]
    rw [← Finset.sum_div, ← hrec, div_self (ne_of_gt hp)]
  · simp [kernel, hp]

theorem zero_row_term (K : S → S → ℝ) (next : S → ℝ)
    (hK : ∀ s t, 0 ≤ K s t) (hn : ∀ t, 0 ≤ next t)
    (s t : S) (hz : (∑ u, K s u * next u) = 0) : K s t * next t = 0 := by
  have hl := Finset.single_le_sum (fun u (_ : u ∈ (Finset.univ : Finset S)) =>
    mul_nonneg (hK s u) (hn u)) (Finset.mem_univ t)
  rw [hz] at hl
  exact le_antisymm hl (mul_nonneg (hK s t) (hn t))

/-- Weighted telescoping does not divide by any intermediate potential.
The zero-start case uses the zero summands of the nonnegative recurrence. -/
theorem weighted_path_identity (n : ℕ) (K : ℕ → S → S → ℝ)
    (h : ℕ → S → ℝ) (hK : ∀ i s t, 0 ≤ K i s t)
    (hh : ∀ i s, 0 ≤ h i s)
    (hrec : ∀ i < n, ∀ s, h i s = ∑ t, K i s t * h (i+1) t)
    (s : S) (path : Paths S n) :
    pathLaw n (kernel K h) s path * h 0 s =
      pathLaw n K s path * h n (endpoint n s path) := by
  induction n generalizing K h s with
  | zero => simp [pathLaw, endpoint]
  | succ n ih =>
    have hi := ih (fun i => K (i+1)) (fun i => h (i+1))
      (fun i => hK (i+1)) (fun i => hh (i+1))
      (fun i hi s => hrec (i+1) (by omega) s) path.1 path.2
    have hshift : (fun i => kernel K h (i+1)) =
        kernel (fun i => K (i+1)) (fun i => h (i+1)) := rfl
    simp only [pathLaw, endpoint, hshift]
    rw [kernel_eq_ratio K h hh]
    by_cases hz : h 0 s = 0
    · have he := zero_row_term (K 0) (h 1) (hK 0) (hh 1) s path.1
        ((hrec 0 (by omega) s).symm.trans hz)
      rw [hz]
      simp only [div_zero, zero_mul]
      calc
        0 = K 0 s path.1 * (pathLaw n
            (kernel (fun i => K (i+1)) (fun i => h (i+1))) path.1 path.2 * h 1 path.1) := by
          calc
            0 = (K 0 s path.1 * h 1 path.1) * pathLaw n
                (kernel (fun i => K (i+1)) (fun i => h (i+1))) path.1 path.2 := by
              rw [he, zero_mul]
            _ = _ := by ring
        _ = _ := by rw [hi]; ring
    · calc
        _ = K 0 s path.1 * (pathLaw n
            (kernel (fun i => K (i+1)) (fun i => h (i+1))) path.1 path.2 * h 1 path.1) := by
          field_simp [hz]
        _ = _ := by rw [hi]; ring

theorem path_identity (n : ℕ) (K : ℕ → S → S → ℝ)
    (h : ℕ → S → ℝ) (hK : ∀ i s t, 0 ≤ K i s t)
    (hh : ∀ i s, 0 ≤ h i s)
    (hrec : ∀ i < n, ∀ s, h i s = ∑ t, K i s t * h (i+1) t)
    (s : S) (hs : 0 < h 0 s) (path : Paths S n) :
    pathLaw n (kernel K h) s path =
      pathLaw n K s path * h n (endpoint n s path) / h 0 s := by
  exact (eq_div_iff (ne_of_gt hs)).mpr (weighted_path_identity n K h hK hh hrec s path)

/-- Actual state visited after i transitions (only i ≤ n is used below). -/
def stateAt : (n : ℕ) → S → Paths S n → ℕ → S
  | 0, s, _, _ => s
  | _+1, s, _, 0 => s
  | n+1, _, path, i+1 => stateAt n path.1 path.2 i

omit [Fintype S] in
/-- Every state on a nonzero conditioned path has strictly positive potential. -/
theorem path_support_positive (n : ℕ) (K : ℕ → S → S → ℝ)
    (h : ℕ → S → ℝ) (hh : ∀ i s, 0 ≤ h i s)
    (s : S) (hs : 0 < h 0 s) (path : Paths S n)
    (hp : pathLaw n (kernel K h) s path ≠ 0) (i : ℕ) (hi : i ≤ n) :
    0 < h i (stateAt n s path i) := by
  induction n generalizing K h s i with
  | zero => have he : i = 0 := by omega
            simpa [he, stateAt] using hs
  | succ n ih =>
    cases i with
    | zero => simpa [stateAt] using hs
    | succ i =>
      have he : kernel K h 0 s path.1 ≠ 0 := (mul_ne_zero_iff.mp hp).1
      have hn : h 1 path.1 ≠ 0 := fun hz => he (kernel_zero_target K h 0 s path.1 hz)
      exact ih (fun i => K (i+1)) (fun i => h (i+1)) (fun i => hh (i+1))
        path.1 (lt_of_le_of_ne (hh 1 path.1) (Ne.symm hn)) path.2
        (mul_ne_zero_iff.mp hp).2 i (by omega)

omit [Fintype S] in
/-- Equivalent pruning bridge: any full path visiting a zero-potential state
has exactly zero conditioned mass, including its prefix and suffix weights. -/
theorem path_zero_at_zero_potential (n : ℕ) (K : ℕ → S → S → ℝ)
    (h : ℕ → S → ℝ) (hh : ∀ i s, 0 ≤ h i s)
    (s : S) (hs : 0 < h 0 s) (path : Paths S n) (i : ℕ) (hi : i ≤ n)
    (hz : h i (stateAt n s path i) = 0) : pathLaw n (kernel K h) s path = 0 := by
  by_contra hp
  have hpos := path_support_positive n K h hh s hs path hp i hi
  rw [hz] at hpos
  exact (lt_irrefl 0) hpos

theorem backwardDP_nonnegative (n : ℕ) (K : ℕ → S → S → ℝ) (payoff : S → ℝ)
    (hK : ∀ i s t, 0 ≤ K i s t) (hp : ∀ s, 0 ≤ payoff s) (s : S) :
    0 ≤ backwardDP n K payoff s := by
  induction n generalizing K s with
  | zero => exact hp s
  | succ n ih => exact Finset.sum_nonneg (fun t _ => mul_nonneg (hK 0 s t)
      (ih (fun i => K (i+1)) (fun i => hK (i+1)) t))

theorem backwardDP_le_one (n : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ i s t, 0 ≤ K i s t) (hrow : ∀ i s, ∑ t, K i s t ≤ 1) (s : S) :
    backwardDP n K (fun _ => 1) s ≤ 1 := by
  induction n generalizing K s with
  | zero => exact le_rfl
  | succ n ih =>
    apply le_trans (Finset.sum_le_sum (fun t _ =>
      mul_le_mul_of_nonneg_left (ih (fun i => K (i+1)) (fun i => hK (i+1))
        (fun i => hrow (i+1)) t) (hK 0 s t)))
    simpa using hrow 0 s

/-- Survival is calculated from the original substochastic kernels, not supplied
as a representation hypothesis. -/
def survival (N : ℕ) (K : ℕ → S → S → ℝ) (i : ℕ) (s : S) : ℝ :=
  backwardDP (N-i) (fun j => K (i+j)) (fun _ => 1) s

theorem survival_terminal (N : ℕ) (K : ℕ → S → S → ℝ) (s : S) :
    survival N K N s = 1 := by simp [survival, backwardDP]

theorem survival_recurrence (N : ℕ) (K : ℕ → S → S → ℝ) (i : ℕ) (hi : i < N) (s : S) :
    survival N K i s = ∑ t, K i s t * survival N K (i+1) t := by
  have he : N-i = (N-(i+1))+1 := by omega
  simp only [survival]
  rw [he, backwardDP]
  simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]

theorem survival_nonnegative (N : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ i s t, 0 ≤ K i s t) (i : ℕ) (s : S) : 0 ≤ survival N K i s :=
  backwardDP_nonnegative _ _ _ (fun j => hK (i+j)) (fun _ => zero_le_one) s

theorem survival_le_one (N : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ i s t, 0 ≤ K i s t) (hrow : ∀ i s, ∑ t, K i s t ≤ 1)
    (i : ℕ) (s : S) : survival N K i s ≤ 1 :=
  backwardDP_le_one _ _ (fun j => hK (i+j)) (fun j => hrow (i+j)) s

theorem survival_eq_path_mass (N : ℕ) (K : ℕ → S → S → ℝ) (s : S) :
    survival N K 0 s = ∑ path : Paths S N, pathLaw N K s path := by
  simpa [survival] using (path_integral_eq_DP N K (fun _ => 1) s).symm

theorem survival_conditioned_path (N : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ i s t, 0 ≤ K i s t) (s : S) (hs : 0 < survival N K 0 s)
    (path : Paths S N) :
    pathLaw N (kernel K (survival N K)) s path = pathLaw N K s path / survival N K 0 s := by
  rw [path_identity N K (survival N K) hK (survival_nonnegative N K hK)
    (survival_recurrence N K) s hs path, survival_terminal, mul_one]

theorem survival_conditioned_normalized (N : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ i s t, 0 ≤ K i s t) (s : S) (hs : 0 < survival N K 0 s) :
    (∑ path : Paths S N, pathLaw N (kernel K (survival N K)) s path) = 1 := by
  simp_rw [survival_conditioned_path N K hK s hs]
  rw [← Finset.sum_div, ← survival_eq_path_mass, div_self (ne_of_gt hs)]

/-- Even the original surviving sublaw has no path mass when the initial
survival potential is zero. -/
theorem survival_zero_path (N : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ i s t, 0 ≤ K i s t) (s : S) (hs : survival N K 0 s = 0)
    (path : Paths S N) : pathLaw N K s path = 0 := by
  have he := weighted_path_identity N K (survival N K) hK
    (survival_nonnegative N K hK) (survival_recurrence N K) s path
  simpa [hs, survival_terminal] using he.symm

/-- The complete finite survival/conditioning/pruning statement. Dead states
remain in the original finite space, but their transformed rows and every
conditioned path through them carry zero mass. -/
theorem conditioned_survival (N : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ i s t, 0 ≤ K i s t) (hrow : ∀ i s, ∑ t, K i s t ≤ 1)
    (s : S) (hs : 0 < survival N K 0 s) :
    (∀ i t, 0 ≤ survival N K i t ∧ survival N K i t ≤ 1) ∧
    (∀ t, survival N K N t = 1) ∧
    (∀ i < N, ∀ u, survival N K i u = ∑ t, K i u t * survival N K (i+1) t) ∧
    (survival N K 0 s = ∑ path : Paths S N, pathLaw N K s path) ∧
    (∀ i < N, ∀ u, (∑ t, kernel K (survival N K) i u t) =
      if 0 < survival N K i u then 1 else 0) ∧
    (∀ i u t, survival N K (i+1) t = 0 → kernel K (survival N K) i u t = 0) ∧
    (∀ path : Paths S N, pathLaw N (kernel K (survival N K)) s path =
      pathLaw N K s path / survival N K 0 s) ∧
    ((∑ path : Paths S N, pathLaw N (kernel K (survival N K)) s path) = 1) ∧
    (∀ (path : Paths S N) (i : ℕ), i ≤ N →
      survival N K i (stateAt N s path i) = 0 →
      pathLaw N (kernel K (survival N K)) s path = 0) := by
  exact ⟨fun i t => ⟨survival_nonnegative N K hK i t, survival_le_one N K hK hrow i t⟩,
    survival_terminal N K, survival_recurrence N K, survival_eq_path_mass N K s,
    fun i hi u => kernel_row_sum K (survival N K) i u (survival_recurrence N K i hi u),
    fun i u t => kernel_zero_target K (survival N K) i u t,
    survival_conditioned_path N K hK s hs, survival_conditioned_normalized N K hK s hs,
    fun path i hi hz => path_zero_at_zero_potential N K (survival N K)
      (survival_nonnegative N K hK) s hs path i hi hz⟩

end Thesis.ConditionedSurvival
