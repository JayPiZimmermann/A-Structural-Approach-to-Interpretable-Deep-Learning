import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-! Finite game and trajectory identities from arXiv:2605.06212v2.
Theorems here state their positivity/normalization assumptions explicitly. -/
noncomputable section
namespace Thesis.Games
open Finset

variable {S T : Type*} [Fintype S] [Fintype T]

def overlap (p q : S → ℝ) : ℝ := ∑ s, Real.sqrt (p s * q s)

def transport (m : S → ℝ) (K : S → T → ℝ) (t : T) : ℝ := ∑ s, m s * K s t

theorem transport_mass (m : S → ℝ) (K : S → T → ℝ) :
    (∑ t, transport m K t) = ∑ s, m s * ∑ t, K s t := by
  simp only [transport, Finset.mul_sum]
  exact Finset.sum_comm

theorem transport_probability (m : S → ℝ) (K : S → T → ℝ)
    (hm : ∑ s, m s = 1) (hK : ∀ s, ∑ t, K s t = 1) :
    ∑ t, transport m K t = 1 := by
  rw [transport_mass]
  simp only [hK, mul_one]
  exact hm

theorem transport_nonneg (m : S → ℝ) (K : S → T → ℝ)
    (hm : ∀ s, 0 ≤ m s) (hK : ∀ s t, 0 ≤ K s t) (t : T) :
    0 ≤ transport m K t :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hm s) (hK s t)

theorem sqrt_overlap_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a*b) ≤ (a+b)/2 := by
  have hs := Real.sq_sqrt (mul_nonneg ha hb)
  have hn := Real.sqrt_nonneg (a*b)
  nlinarith [sq_nonneg (a-b)]

theorem overlap_nonneg (p q : S → ℝ) : 0 ≤ overlap p q :=
  Finset.sum_nonneg fun _s _ => Real.sqrt_nonneg _

theorem overlap_le_one (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1) : overlap p q ≤ 1 := by
  calc
    overlap p q ≤ ∑ s, (p s + q s) / 2 :=
      Finset.sum_le_sum fun s _ => sqrt_overlap_le _ _ (hp s) (hq s)
    _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, hp1, hq1]; norm_num

/-- The geometric-mean transition kernel is sub-stochastic. -/
theorem geometric_kernel_substochastic (A B : S → T → ℝ)
    (hA : ∀ s t, 0 ≤ A s t) (hB : ∀ s t, 0 ≤ B s t)
    (hA1 : ∀ s, ∑ t, A s t = 1) (hB1 : ∀ s, ∑ t, B s t = 1) (s : S) :
    (∑ t, Real.sqrt (A s t * B s t)) ≤ 1 :=
  overlap_le_one (A s) (B s) (hA s) (hB s) (hA1 s) (hB1 s)

/-- Prefix overlap cannot increase when a sub-stochastic overlap kernel is appended. -/
theorem overlap_mass_decreases (g : S → ℝ) (K : S → T → ℝ)
    (hg : ∀ s, 0 ≤ g s) (hK : ∀ s, ∑ t, K s t ≤ 1) :
    (∑ t, transport g K t) ≤ ∑ s, g s := by
  rw [transport_mass]
  exact Finset.sum_le_sum fun s _ => by simpa using mul_le_mul_of_nonneg_left (hK s) (hg s)

/-- Exact two-block Bhattacharyya factorization, including zero probabilities. -/
theorem overlap_chain_rule (p q : S → ℝ) (A B : S → T → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (_hA : ∀ s t, 0 ≤ A s t) (_hB : ∀ s t, 0 ≤ B s t) :
    (∑ s, ∑ t, Real.sqrt ((p s * A s t) * (q s * B s t))) =
      ∑ s, Real.sqrt (p s * q s) * ∑ t, Real.sqrt (A s t * B s t) := by
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have he : (p s * A s t) * (q s * B s t) = (p s * q s) * (A s t * B s t) := by ring
  rw [he, Real.sqrt_mul (mul_nonneg (hp s) (hq s))]

/-- Factorization over any finite set of edges gives the pathwise chain rule. -/
theorem overlap_path_factorization {I : Type*} (edges : Finset I) (a b : I → ℝ)
    (ha : ∀ i ∈ edges, 0 ≤ a i) (hb : ∀ i ∈ edges, 0 ≤ b i) :
    Real.sqrt ((∏ i ∈ edges, a i) * (∏ i ∈ edges, b i)) =
      ∏ i ∈ edges, Real.sqrt (a i * b i) := by
  classical
  rw [← Finset.prod_mul_distrib]
  exact Real.sqrt_prod _ (fun i hi => mul_nonneg (ha i hi) (hb i hi))

/-- Local discount cancels the normalization of the stopping-game transition. -/
theorem discounted_edge_recovery (w γ : ℝ) (hγ : γ ≠ 0) : γ * (w / γ) = w := by
  field_simp

/-- The signed positive/negative streams recover the original weighted edge. -/
theorem signed_discounted_edge_recovery (wp wn γ : ℝ) (hγ : γ ≠ 0) :
    γ * (wp / γ) - γ * (wn / γ) = wp - wn := by
  rw [discounted_edge_recovery _ _ hγ, discounted_edge_recovery _ _ hγ]

/-- Exact alpha-beta redistribution for a single routing state. -/
theorem routing_recovery (α β wp wn ap an Zp Zn rp rn : ℝ)
    (_hZp : Zp ≠ 0) (_hZn : Zn ≠ 0) :
    α * ((wp * ap) / Zp) * rp - β * ((wn * an) / Zn) * rn =
      (α * wp * ap * rp) / Zp - (β * wn * an * rn) / Zn := by ring

/-- Conditioning both laws on the same surviving path set rescales overlap by sqrt(ZA ZB). -/
theorem survival_overlap (p q : S → ℝ) (ZA ZB : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (_hZA : 0 < ZA) (_hZB : 0 < ZB) :
    overlap (fun s => p s / ZA) (fun s => q s / ZB) = overlap p q / Real.sqrt (ZA*ZB) := by
  unfold overlap
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  have he : p s / ZA * (q s / ZB) = (p s * q s) / (ZA * ZB) := by ring
  rw [he, Real.sqrt_div (mul_nonneg (hp s) (hq s))]

/-- The arithmetic/geometric formula for squared Hellinger distance. -/
theorem hellinger_identity (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1) :
    (1/2 : ℝ) * (∑ s, (Real.sqrt (p s) - Real.sqrt (q s))^2) = 1-overlap p q := by
  have he : ∀ s, (Real.sqrt (p s) - Real.sqrt (q s))^2 =
      p s + q s - 2 * Real.sqrt (p s * q s) := by
    intro s
    rw [Real.sqrt_mul (hp s)]
    nlinarith [Real.sq_sqrt (hp s), Real.sq_sqrt (hq s)]
  simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hq1]
  unfold overlap
  ring
end Thesis.Games

namespace Thesis.Games
open Finset

/-- A complete length-n walk, including its n visited successor states. -/
def Paths (S : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => S × Paths S n

instance pathsFintype (S : Type) [Fintype S] : (n : ℕ) → Fintype (Paths S n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd S (Paths S n) _ (pathsFintype S n)

variable {S : Type} [Fintype S]

/-- Markov path law conditional on its initial state. -/
noncomputable def pathLaw : (n : ℕ) → (ℕ → S → S → ℝ) → S → Paths S n → ℝ
  | 0, _, _, _ => 1
  | n+1, K, s, path => K 0 s path.1 * pathLaw n (fun i => K (i+1)) path.1 path.2

/-- Linear-time dynamic program with a terminal payoff. -/
noncomputable def backwardDP : ℕ → (ℕ → S → S → ℝ) → (S → ℝ) → S → ℝ
  | 0, _, payoff, s => payoff s
  | n+1, K, payoff, s => ∑ t, K 0 s t * backwardDP n (fun i => K (i+1)) payoff t

noncomputable def endpoint : (n : ℕ) → S → Paths S n → S
  | 0, s, _ => s
  | n+1, _, path => endpoint n path.1 path.2

/-- Exact trajectory path integral equals the backward dynamic program at every depth. -/
theorem path_integral_eq_DP (n : ℕ) (K : ℕ → S → S → ℝ) (payoff : S → ℝ) (s : S) :
    (∑ path : Paths S n, pathLaw n K s path * payoff (endpoint n s path)) =
      backwardDP n K payoff s := by
  induction n generalizing K s with
  | zero =>
    change (∑ _ : Unit, (1 : ℝ) * payoff s) = payoff s
    simp
  | succ n ih =>
    change (∑ path : S × Paths S n,
      (K 0 s path.1 * pathLaw n (fun i => K (i+1)) path.1 path.2) *
      payoff (endpoint n path.1 path.2)) = _
    rw [Fintype.sum_prod_type]
    simp_rw [mul_assoc, ← Finset.mul_sum, ih]
    rfl

/-- Proper stochastic rows induce a probability distribution on full trajectories. -/
theorem path_law_normalized (n : ℕ) (K : ℕ → S → S → ℝ)
    (hK : ∀ i s, ∑ t, K i s t = 1) (s : S) :
    (∑ path : Paths S n, pathLaw n K s path) = 1 := by
  have h := path_integral_eq_DP n K (fun _ => 1) s
  simp only [mul_one] at h
  rw [h]
  clear h
  induction n generalizing K s with
  | zero => rfl
  | succ n ih =>
    simp only [backwardDP]
    have hn : ∀ t, backwardDP n (fun i => K (i+1)) (fun _ => 1) t = 1 :=
      fun t => ih _ (fun i u => hK (i+1) u) t
    simp only [hn, mul_one]
    exact hK 0 s

/-- Pathwise geometric means factor into the geometric-mean kernels for every depth. -/
theorem path_geometric_mean (n : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
    (s : S) (path : Paths S n) :
    Real.sqrt (pathLaw n A s path * pathLaw n B s path) =
      pathLaw n (fun i u v => Real.sqrt (A i u v * B i u v)) s path := by
  induction n generalizing A B s with
  | zero => norm_num [pathLaw]
  | succ n ih =>
    simp only [pathLaw]
    have he : (A 0 s path.1 * pathLaw n (fun i => A (i+1)) path.1 path.2) *
        (B 0 s path.1 * pathLaw n (fun i => B (i+1)) path.1 path.2) =
        (A 0 s path.1 * B 0 s path.1) *
        (pathLaw n (fun i => A (i+1)) path.1 path.2 * pathLaw n (fun i => B (i+1)) path.1 path.2) := by ring
    rw [he, Real.sqrt_mul (mul_nonneg (hA 0 s path.1) (hB 0 s path.1))]
    rw [ih _ _ (fun i u v => hA (i+1) u v) (fun i u v => hB (i+1) u v)]

/-- The paper's Hellinger pass computes overlap of full path laws, not just endpoint marginals. -/
theorem trajectory_overlap_eq_DP (n : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t) (s : S) :
    (∑ path : Paths S n, Real.sqrt (pathLaw n A s path * pathLaw n B s path)) =
      backwardDP n (fun i u v => Real.sqrt (A i u v * B i u v)) (fun _ => 1) s := by
  simp_rw [path_geometric_mean n A B hA hB]
  simpa using path_integral_eq_DP n (fun i u v => Real.sqrt (A i u v * B i u v)) (fun _ => 1) s

/-- Discount-weighted trajectory law is exactly the product of unnormalized edges. -/
theorem discount_path_recovery (n : ℕ) (W : ℕ → S → S → ℝ) (γ : ℕ → S → ℝ)
    (hγ : ∀ i s, γ i s ≠ 0) (s : S) (path : Paths S n) :
    pathLaw n (fun i u _ => γ i u) s path *
      pathLaw n (fun i u v => W i u v / γ i u) s path = pathLaw n W s path := by
  induction n generalizing W γ s with
  | zero => simp [pathLaw]
  | succ n ih =>
    simp only [pathLaw]
    calc
      _ = (γ 0 s * (W 0 s path.1 / γ 0 s)) *
          (pathLaw n (fun i u _ => γ (i+1) u) path.1 path.2 *
           pathLaw n (fun i u v => W (i+1) u v / γ (i+1) u) path.1 path.2) := by ring
      _ = _ := by
        rw [discounted_edge_recovery _ _ (hγ 0 s)]
        rw [ih (fun i => W (i+1)) (fun i => γ (i+1)) (fun i u => hγ (i+1) u)]
end Thesis.Games

namespace Thesis.Games
open Finset
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- Exact non-negative disagreement assigned to an individual trajectory. -/
noncomputable def pathDisagreement (p q : X → ℝ) (x : X) : ℝ :=
  (p x + q x)/2 - Real.sqrt (p x * q x)

/-- The terminal map groups whole trajectories, rather than first marginalizing them. -/
noncomputable def pixelDisagreement (p q : X → ℝ) (terminal : X → Y) (y : Y) : ℝ :=
  ∑ x, if terminal x = y then pathDisagreement p q x else 0

theorem pathDisagreement_nonneg (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (x : X) :
    0 ≤ pathDisagreement p q x := by
  exact sub_nonneg.mpr (sqrt_overlap_le _ _ (hp x) (hq x))

theorem pixelDisagreement_nonneg (p q : X → ℝ) (terminal : X → Y)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (y : Y) :
    0 ≤ pixelDisagreement p q terminal y := by
  unfold pixelDisagreement
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact pathDisagreement_nonneg p q hp hq x
  · exact le_rfl

/-- The per-pixel disagreement formula (including a cemetery terminal when present). -/
theorem pixelDisagreement_formula (p q : X → ℝ) (terminal : X → Y) (y : Y) :
    pixelDisagreement p q terminal y =
      ((∑ x, if terminal x = y then p x else 0) +
       (∑ x, if terminal x = y then q x else 0))/2 -
       ∑ x, if terminal x = y then Real.sqrt (p x * q x) else 0 := by
  unfold pixelDisagreement pathDisagreement
  rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Exact sum of all pixel contributions equals the full squared Hellinger distance. -/
theorem pixelDisagreement_total (p q : X → ℝ) (terminal : X → Y)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    (∑ y, pixelDisagreement p q terminal y) = 1 - overlap p q := by
  unfold pixelDisagreement
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold pathDisagreement
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, hp1, hq1]
  unfold overlap
  ring

/-- General finite Cauchy--Schwarz bound for unnormalized path submeasures. -/
theorem overlap_sq_le_masses (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    (overlap p q)^2 ≤ (∑ x, p x) * ∑ x, q x := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => hp x) (fun x _ => hq x)
    (fun x _ => (Real.sq_sqrt (mul_nonneg (hp x) (hq x))).le)
end Thesis.Games

namespace Thesis.Games
open Finset
variable {S : Type*} [Fintype S]

theorem overlap_self (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) : overlap p p = ∑ s, p s := by
  unfold overlap
  apply Finset.sum_congr rfl
  intro s _
  exact Real.sqrt_mul_self (hp s)

theorem overlap_eq_one_iff (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1) :
    overlap p q = 1 ↔ p = q := by
  constructor
  · intro h
    have hi := hellinger_identity p q hp hq hp1 hq1
    have hs : (∑ s, (Real.sqrt (p s) - Real.sqrt (q s))^2) = 0 := by
      rw [h] at hi
      linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s ∈ Finset.univ) =>
      sq_nonneg (Real.sqrt (p s) - Real.sqrt (q s)))).mp hs
    funext s
    have he := hz s (Finset.mem_univ s)
    have hr : Real.sqrt (p s) = Real.sqrt (q s) := by nlinarith
    have hp' := Real.sq_sqrt (hp s)
    have hq' := Real.sq_sqrt (hq s)
    rw [hr] at hp'
    linarith
  · rintro rfl
    rw [overlap_self p hp, hp1]

/-- Zero overlap is exactly disjoint support, without any strict-positivity assumption. -/
theorem overlap_eq_zero_iff (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) :
    overlap p q = 0 ↔ ∀ s, p s = 0 ∨ q s = 0 := by
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s ∈ Finset.univ) =>
      Real.sqrt_nonneg (p s * q s))).mp h
    intro s
    have he := hz s (Finset.mem_univ s)
    have ht := Real.sq_sqrt (mul_nonneg (hp s) (hq s))
    rw [he] at ht
    exact mul_eq_zero.mp (by linarith)
  · intro h
    apply Finset.sum_eq_zero
    intro s _
    rcases h s with he | he <;> simp [he]
end Thesis.Games

namespace Thesis.Games
open Finset
variable {S T : Type*} [Fintype S] [Fintype T]

/-- The Doob survival transform is stochastic wherever its survival potential is positive. -/
theorem doob_kernel_normalized (K : S → T → ℝ) (h : S → ℝ) (next : T → ℝ)
    (hh : ∀ s, h s ≠ 0) (hrec : ∀ s, h s = ∑ t, K s t * next t) (s : S) :
    (∑ t, K s t * next t / h s) = 1 := by
  rw [← Finset.sum_div, ← hrec s]
  exact div_self (hh s)

/-- Non-negativity is preserved by conditioning on positive survival. -/
theorem doob_kernel_nonneg (K : S → T → ℝ) (h : S → ℝ) (next : T → ℝ)
    (hK : ∀ s t, 0 ≤ K s t) (hh : ∀ s, 0 < h s) (hn : ∀ t, 0 ≤ next t)
    (s : S) (t : T) : 0 ≤ K s t * next t / h s :=
  div_nonneg (mul_nonneg (hK s t) (hn t)) (hh s).le
end Thesis.Games

namespace Thesis.Games
variable {S : Type} [Fintype S]

/-- The survival potentials telescope along complete paths (strictly positive potential variant).
Zero-survival states are excluded from this state space, as in the conditioned law. -/
theorem doob_path_telescoping (n : ℕ) (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ)
    (hh : ∀ i s, h i s ≠ 0) (s : S) (path : Paths S n) :
    pathLaw n (fun i u v => K i u v * h (i+1) v / h i u) s path =
      pathLaw n K s path * h n (endpoint n s path) / h 0 s := by
  induction n generalizing K h s with
  | zero => simp [pathLaw, endpoint, hh]
  | succ n ih =>
    simp only [pathLaw, endpoint]
    rw [ih (fun i => K (i+1)) (fun i => h (i+1)) (fun i u => hh (i+1) u)]
    dsimp
    field_simp [hh 0 s, hh 1 path.1]

/-- With terminal survival potential one, the Doob-transformed path law is the
ordinary surviving path sublaw divided by initial survival mass. -/
theorem doob_survival_path (n : ℕ) (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ)
    (hh : ∀ i s, h i s ≠ 0) (hterminal : ∀ t, h n t = 1) (s : S) (path : Paths S n) :
    pathLaw n (fun i u v => K i u v * h (i+1) v / h i u) s path =
      pathLaw n K s path / h 0 s := by
  rw [doob_path_telescoping n K h hh, hterminal, mul_one]
end Thesis.Games
