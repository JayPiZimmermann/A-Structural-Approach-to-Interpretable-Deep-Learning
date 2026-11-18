import Thesis.Games

/-!
Hellinger distance of actual layered trajectory laws, computed by transporting
geometric-mean overlap mass. The state type may vary at every layer. We index
the traversal by elapsed steps `n`; in the thesis notation this is `n = L - l`,
with the full trajectory law obtained at `n = L`. A cemetery can be included
in each state type, but absorption is not required by the distance identity.
-/
noncomputable section
set_option autoImplicit false
namespace Thesis.TrajectoryHellinger
open Finset
open scoped Classical

/-- A prefix includes its initial state and every subsequently visited state. -/
def Prefix (S : ℕ → Type) : ℕ → Type
  | 0 => S 0
  | n + 1 => Prefix S n × S (n + 1)

instance prefixFintype (S : ℕ → Type) [∀ n, Fintype (S n)] :
    (n : ℕ) → Fintype (Prefix S n)
  | 0 => inferInstanceAs (Fintype (S 0))
  | n + 1 => @instFintypeProd (Prefix S n) (S (n + 1))
      (prefixFintype S n) inferInstance

def last {S : ℕ → Type} : (n : ℕ) → Prefix S n → S n
  | 0, p => p
  | _ + 1, p => p.2

abbrev Kernel (S : ℕ → Type) := (n : ℕ) → S n → S (n + 1) → ℝ

variable {S : ℕ → Type} [∀ n, Fintype (S n)]

/-- Independent product law of all prefixes, including the common delta start. -/
def pathLaw (K : Kernel S) (s₀ : S 0) : (n : ℕ) → Prefix S n → ℝ
  | 0, p => if p = s₀ then 1 else 0
  | n + 1, p => pathLaw K s₀ n p.1 * K n (last n p.1) p.2

/-- Forward transport, independently defined without enumerating paths. -/
def mass (K : Kernel S) (s₀ : S 0) : (n : ℕ) → S n → ℝ
  | 0, s => if s = s₀ then 1 else 0
  | n + 1, t => ∑ s, mass K s₀ n s * K n s t

def geometricKernel (A B : Kernel S) : Kernel S :=
  fun n s t => Real.sqrt (A n s t * B n s t)

/-- The thesis quantity g, initialized at the start and propagated edgewise. -/
def g (A B : Kernel S) (s₀ : S 0) (n : ℕ) : S n → ℝ :=
  mass (geometricKernel A B) s₀ n

/-- Computed overlap mass; identification with path overlap is proved below. -/
def BC (A B : Kernel S) (s₀ : S 0) (n : ℕ) : ℝ := ∑ s, g A B s₀ n s

/-- Squared Hellinger distance is defined from differences of square roots. -/
def hellingerSquared {X : Type} [Fintype X] (p q : X → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2

/-- The distance, independently of any overlap recursion. -/
def hellinger {X : Type} [Fintype X] (p q : X → ℝ) : ℝ :=
  Real.sqrt (hellingerSquared p q)

theorem hellingerSquared_nonneg {X : Type} [Fintype X] (p q : X → ℝ) :
    0 ≤ hellingerSquared p q := by
  unfold hellingerSquared
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => sq_nonneg _)

theorem hellinger_sq {X : Type} [Fintype X] (p q : X → ℝ) :
    hellinger p q ^ 2 = hellingerSquared p q := by
  exact Real.sq_sqrt (hellingerSquared_nonneg p q)

omit [∀ n, Fintype (S n)] in
theorem pathLaw_nonnegative (K : Kernel S) (s₀ : S 0)
    (n : ℕ) (hK : ∀ i < n, ∀ s t, 0 ≤ K i s t) (p : Prefix S n) :
    0 ≤ pathLaw K s₀ n p := by
  classical
  induction n with
  | zero =>
      change 0 ≤ if p = s₀ then (1 : ℝ) else 0
      split_ifs <;> norm_num
  | succ n ih =>
      exact mul_nonneg (ih (fun i hi => hK i (Nat.lt_succ_of_lt hi)) p.1)
        (hK n (Nat.lt_succ_self n) (last n p.1) p.2)

theorem pathLaw_normalized (K : Kernel S) (s₀ : S 0)
    (n : ℕ) (hKrow : ∀ i < n, ∀ s, ∑ t, K i s t = 1) :
    (∑ p : Prefix S n, pathLaw K s₀ n p) = 1 := by
  classical
  induction n with
  | zero =>
      change (∑ p : S 0, if p = s₀ then (1 : ℝ) else 0) = 1
      simp
  | succ n ih =>
    change (∑ p : Prefix S n × S (n + 1),
      pathLaw K s₀ n p.1 * K n (last n p.1) p.2) = 1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hKrow n (Nat.lt_succ_self n), mul_one]
    exact ih (fun i hi => hKrow i (Nat.lt_succ_of_lt hi))

/-- The transported mass equals the sum over paths with the given endpoint. -/
theorem mass_eq_endpoint_sum (K : Kernel S) (s₀ : S 0) (n : ℕ) (t : S n) :
    mass K s₀ n t = ∑ p : Prefix S n,
      if last n p = t then pathLaw K s₀ n p else 0 := by
  classical
  induction n with
  | zero =>
      change (if t = s₀ then (1 : ℝ) else 0) =
        ∑ p : S 0, if p = t then (if p = s₀ then 1 else 0) else 0
      simp
  | succ n ih =>
    change (∑ s, mass K s₀ n s * K n s t) =
      ∑ p : Prefix S n × S (n + 1),
        if p.2 = t then pathLaw K s₀ n p.1 * K n (last n p.1) p.2 else 0
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp_rw [ih, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simp only [ite_mul, zero_mul]
    simp

theorem mass_total_eq_path_sum (K : Kernel S) (s₀ : S 0) (n : ℕ) :
    (∑ s, mass K s₀ n s) = ∑ p : Prefix S n, pathLaw K s₀ n p := by
  simp_rw [mass_eq_endpoint_sum]
  rw [Finset.sum_comm]
  simp

omit [∀ n, Fintype (S n)] in
/-- Geometric means factor along the actual varying-state prefix law. -/
theorem pathLaw_geometric (A B : Kernel S) (s₀ : S 0)
    (n : ℕ) (hA : ∀ i < n, ∀ s t, 0 ≤ A i s t)
    (hB : ∀ i < n, ∀ s t, 0 ≤ B i s t) (p : Prefix S n) :
    Real.sqrt (pathLaw A s₀ n p * pathLaw B s₀ n p) =
      pathLaw (geometricKernel A B) s₀ n p := by
  classical
  induction n with
  | zero =>
      change Real.sqrt ((if p = s₀ then (1 : ℝ) else 0) *
        (if p = s₀ then (1 : ℝ) else 0)) = if p = s₀ then 1 else 0
      split_ifs <;> norm_num
  | succ n ih =>
    simp only [pathLaw]
    have he : (pathLaw A s₀ n p.1 * A n (last n p.1) p.2) *
        (pathLaw B s₀ n p.1 * B n (last n p.1) p.2) =
        (pathLaw A s₀ n p.1 * pathLaw B s₀ n p.1) *
        (A n (last n p.1) p.2 * B n (last n p.1) p.2) := by ring
    have hAn := fun i hi => hA i (Nat.lt_succ_of_lt hi)
    have hBn := fun i hi => hB i (Nat.lt_succ_of_lt hi)
    rw [he, Real.sqrt_mul (mul_nonneg
      (pathLaw_nonnegative A s₀ n hAn p.1) (pathLaw_nonnegative B s₀ n hBn p.1)),
      ih hAn hBn]
    rfl

/-- The computed total mass is the overlap of whole prefixes, not merely endpoints. -/
theorem BC_eq_path_overlap (A B : Kernel S) (s₀ : S 0)
    (n : ℕ) (hA : ∀ i < n, ∀ s t, 0 ≤ A i s t)
    (hB : ∀ i < n, ∀ s t, 0 ≤ B i s t) :
    BC A B s₀ n = Thesis.Games.overlap (pathLaw A s₀ n) (pathLaw B s₀ n) := by
  unfold BC g Thesis.Games.overlap
  rw [mass_total_eq_path_sum]
  simp_rw [pathLaw_geometric A B s₀ n hA hB]

/-- Remove the last k coordinates of a longer path. -/
def truncate (n : ℕ) : (k : ℕ) → Prefix S (n + k) → Prefix S n
  | 0, p => p
  | k + 1, p => truncate n k p.1

/-- Normalized future transitions make the shorter law the true marginal
of the longer trajectory distribution. -/
theorem prefix_marginal (K : Kernel S) (s₀ : S 0)
    (n k : ℕ) (hKrow : ∀ i < n + k, ∀ s, ∑ t, K i s t = 1)
    (q : Prefix S n) :
    (∑ p : Prefix S (n + k),
      if truncate n k p = q then pathLaw K s₀ (n + k) p else 0) =
      pathLaw K s₀ n q := by
  classical
  induction k with
  | zero =>
      change (∑ p : Prefix S n, if p = q then pathLaw K s₀ n p else 0) = _
      exact Fintype.sum_ite_eq' q (pathLaw K s₀ n)
  | succ k ih =>
    change (∑ p : Prefix S (n + k) × S (n + k + 1),
      if truncate n k p.1 = q then
        pathLaw K s₀ (n + k) p.1 * K (n + k) (last (n + k) p.1) p.2
      else 0) = _
    rw [Fintype.sum_prod_type]
    have hs (p : Prefix S (n + k)) :
        (∑ t, if truncate n k p = q then
          pathLaw K s₀ (n + k) p * K (n + k) (last (n + k) p) t else 0) =
        if truncate n k p = q then pathLaw K s₀ (n + k) p else 0 := by
      by_cases hp : truncate n k p = q
      · simp [hp, ← Finset.mul_sum, hKrow (n + k) (Nat.lt_succ_self (n + k))]
      · simp [hp]
    simp_rw [hs]
    exact ih (fun i hi => hKrow i (Nat.lt_succ_of_lt hi))

/-- The exact displayed Hellinger identities for every prefix length n,
including the full law at n=L and the common-start boundary n=0.
The equation uses layer index l=L-n; BC and g are the independently computed
overlap recursion, and H is defined from square-root differences of path laws. -/
theorem trajectory_hellinger_recursion (A B : Kernel S) (s₀ : S 0)
    (n : ℕ) (hA : ∀ i < n, ∀ s t, 0 ≤ A i s t)
    (hB : ∀ i < n, ∀ s t, 0 ≤ B i s t)
    (hArow : ∀ i < n, ∀ s, ∑ t, A i s t = 1)
    (hBrow : ∀ i < n, ∀ s, ∑ t, B i s t = 1) :
    hellingerSquared (pathLaw A s₀ n) (pathLaw B s₀ n) =
        hellinger (pathLaw A s₀ n) (pathLaw B s₀ n) ^ 2 ∧
    hellinger (pathLaw A s₀ n) (pathLaw B s₀ n) ^ 2 = 1 - BC A B s₀ n ∧
    hellinger (pathLaw A s₀ n) (pathLaw B s₀ n) = Real.sqrt (1 - BC A B s₀ n) ∧
    hellinger (pathLaw A s₀ n) (pathLaw B s₀ n) =
        Real.sqrt (1 - ∑ s, g A B s₀ n s) := by
  have hs : hellingerSquared (pathLaw A s₀ n) (pathLaw B s₀ n) =
      1 - BC A B s₀ n := by
    rw [BC_eq_path_overlap A B s₀ n hA hB]
    exact Thesis.Games.hellinger_identity _ _
      (pathLaw_nonnegative A s₀ n hA) (pathLaw_nonnegative B s₀ n hB)
      (pathLaw_normalized A s₀ n hArow) (pathLaw_normalized B s₀ n hBrow)
  have hd : hellinger (pathLaw A s₀ n) (pathLaw B s₀ n) =
      Real.sqrt (1 - BC A B s₀ n) := by
    unfold hellinger
    rw [hs]
  exact ⟨(hellinger_sq _ _).symm, (hellinger_sq _ _).trans hs, hd, hd⟩

theorem common_start_distance (A B : Kernel S) (s₀ : S 0) :
    hellinger (pathLaw A s₀ 0) (pathLaw B s₀ 0) = 0 := by
  simp [hellinger, hellingerSquared, Prefix, pathLaw]

end Thesis.TrajectoryHellinger
