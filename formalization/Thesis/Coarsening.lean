import Thesis.Games
import Mathlib.Data.Fin.VecNotation

/-! Coarsening a trajectory retains endpoint masses but can erase stopping
phase/cause information. Bhattacharyya overlap increases under coarsening;
it is exactly preserved by a genuine bijective recovery map. -/
noncomputable section
namespace Thesis.Coarsening
open Finset Thesis.Games

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

def pushforward (f : X → Y) (p : X → ℝ) (y : Y) : ℝ :=
  ∑ x, if f x = y then p x else 0

def fiber (f : X → Y) (p : X → ℝ) (y : Y) (x : X) : ℝ := if f x = y then p x else 0

omit [Fintype Y] in
theorem pushforward_nonneg (f : X → Y) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (y : Y) :
    0 ≤ pushforward f p y := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hp x
  · exact le_rfl

theorem pushforward_mass (f : X → Y) (p : X → ℝ) :
    (∑ y, pushforward f p y) = ∑ x, p x := by
  unfold pushforward
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [Fintype X] [Fintype Y] in
theorem fiber_nonneg (f : X → Y) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (y : Y) (x : X) :
    0 ≤ fiber f p y x := by
  unfold fiber
  split_ifs
  · exact hp x
  · exact le_rfl

omit [Fintype Y] in
theorem fiber_overlap_formula (f : X → Y) (p q : X → ℝ) (y : Y) :
    overlap (fiber f p y) (fiber f q y) =
      ∑ x, if f x = y then Real.sqrt (p x * q x) else 0 := by
  unfold overlap
  apply Finset.sum_congr rfl
  intro x _
  unfold fiber
  split_ifs <;> simp

theorem fiber_overlap_total (f : X → Y) (p q : X → ℝ) :
    (∑ y, overlap (fiber f p y) (fiber f q y)) = overlap p q := by
  simp_rw [fiber_overlap_formula]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

/-- Finite Bhattacharyya data processing, without requiring normalized masses. -/
theorem overlap_coarsening (f : X → Y) (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    overlap p q ≤ overlap (pushforward f p) (pushforward f q) := by
  rw [← fiber_overlap_total f p q]
  apply Finset.sum_le_sum
  intro y _
  have h := overlap_sq_le_masses (fiber f p y) (fiber f q y)
    (fiber_nonneg f p hp y) (fiber_nonneg f q hq y)
  have hs := Real.sq_sqrt (mul_nonneg (pushforward_nonneg f p hp y) (pushforward_nonneg f q hq y))
  have hn := Real.sqrt_nonneg (pushforward f p y * pushforward f q y)
  change overlap (fiber f p y) (fiber f q y) ≤ Real.sqrt (pushforward f p y * pushforward f q y)
  change (overlap (fiber f p y) (fiber f q y))^2 ≤ pushforward f p y * pushforward f q y at h
  nlinarith

/-- The squared Hellinger diagnostic can only decrease after trajectory coarsening. -/
theorem hellinger_coarsening (f : X → Y) (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    1 - overlap (pushforward f p) (pushforward f q) ≤ 1 - overlap p q := by
  linarith [overlap_coarsening f p q hp hq]

omit [DecidableEq Y] in
/-- A genuinely recoverable intermediate-coordinate deletion preserves overlap exactly. -/
theorem overlap_reindex (e : X ≃ Y) (p q : X → ℝ) :
    overlap (fun y => p (e.symm y)) (fun y => q (e.symm y)) = overlap p q := by
  exact e.symm.sum_comp (fun x => Real.sqrt (p x*q x))

omit [DecidableEq Y] in
/-- In particular, ordinary surviving trajectories are equivalent whenever their
intermediate state is uniquely reconstructible in both directions. -/
theorem surviving_overlap_recovery (erase : X → Y) (recover : Y → X)
    (hleft : Function.LeftInverse recover erase) (hright : Function.RightInverse recover erase)
    (p q : X → ℝ) :
    overlap (fun y => p (recover y)) (fun y => q (recover y)) = overlap p q :=
  overlap_reindex ⟨erase,recover,hleft,hright⟩ p q

/-- Fine outcomes: gate-stop, negative-branch-stop, ordinary-positive path. -/
def fineA : Fin 3 → ℝ := ![0, 1/2, 1/2]
def fineB : Fin 3 → ℝ := ![1, 0, 0]

/-- Erasing linear routing states merges the two distinct stopping causes. -/
def eraseCause (i : Fin 3) : Fin 2 := if i = 2 then 1 else 0

theorem counterexample_laws :
    (∀ i, 0 ≤ fineA i) ∧ (∀ i, 0 ≤ fineB i) ∧ (∑ i, fineA i) = 1 ∧ (∑ i, fineB i) = 1 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [fineA]
  constructor
  · intro i
    fin_cases i <;> norm_num [fineB]
  norm_num [fineA, fineB, Fin.sum_univ_succ]

/-- Refutes full-path BC equality after deleting stopping cause/phase. -/
theorem paper_full_path_bijection_counterexample :
    overlap fineA fineB = 0 ∧
    overlap (pushforward eraseCause fineA) (pushforward eraseCause fineB) = Real.sqrt (1/2) := by
  norm_num [overlap, pushforward, eraseCause, fineA, fineB, Fin.sum_univ_succ]

/-- The inequality is strict in the explicit routing-empty-branch example. -/
theorem paper_full_path_overlap_strict :
    overlap fineA fineB < overlap (pushforward eraseCause fineA) (pushforward eraseCause fineB) := by
  rw [paper_full_path_bijection_counterexample.1, paper_full_path_bijection_counterexample.2]
  positivity

end Thesis.Coarsening
