import HiddenMonotonicity.Chunks
import Mathlib.Analysis.Convex.Function

namespace HiddenMonotonicity
open scoped BigOperators

/-- The exact finite convex-pool construction, including every other negative
stream in each positive candidate. -/
noncomputable def finitePool {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (x : (ι → ℝ) × (ι → ℝ)) : ℝ × ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty (fun j => x.1 j + ∑ i ∈ Finset.univ.erase j, x.2 i),
    ∑ i, x.2 i)

theorem finitePool_recovery {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (x : (ι → ℝ) × (ι → ℝ)) :
    (finitePool x).1-(finitePool x).2 =
      Finset.univ.sup' Finset.univ_nonempty (fun j => x.1 j-x.2 j) := maxpool_correct x.1 x.2

theorem finitePool_nonnegative {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (x : (ι → ℝ) × (ι → ℝ)) (hx : 0≤x) : 0≤finitePool x := by
  constructor
  · obtain ⟨j⟩ := ‹Nonempty ι›
    change 0 ≤ Finset.univ.sup' Finset.univ_nonempty _
    exact le_trans (add_nonneg (hx.1 j) (Finset.sum_nonneg (s := Finset.univ.erase j) (fun i _ => hx.2 i)))
      (Finset.le_sup' (fun j => x.1 j + ∑ i ∈ Finset.univ.erase j, x.2 i) (Finset.mem_univ j))
  · exact Finset.sum_nonneg (fun i _ => hx.2 i)

theorem finitePool_monotone {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] :
    Monotone (finitePool (ι := ι)) := by
  intro x y h
  constructor
  · change Finset.univ.sup' Finset.univ_nonempty _ ≤ _
    apply (Finset.sup'_le_iff _ _).mpr
    intro j _
    exact le_trans (add_le_add (h.1 j) (Finset.sum_le_sum (fun i _ => h.2 i)))
      (Finset.le_sup' (fun j => y.1 j + ∑ i ∈ Finset.univ.erase j, y.2 i) (Finset.mem_univ j))
  · exact Finset.sum_le_sum (fun i _ => h.2 i)

theorem finitePool_convex {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] :
    ConvexOn ℝ Set.univ (fun x => (finitePool (ι := ι) x).1) ∧
    ConvexOn ℝ Set.univ (fun x => (finitePool (ι := ι) x).2) := by
  constructor <;> refine ⟨convex_univ, ?_⟩ <;> intro x _ y _ a b ha hb hab
  · change Finset.univ.sup' Finset.univ_nonempty _ ≤ _
    apply (Finset.sup'_le_iff _ _).mpr
    intro j _
    change a*x.1 j+b*y.1 j + (∑ i ∈ Finset.univ.erase j, (a*x.2 i+b*y.2 i)) ≤
      a*(finitePool x).1+b*(finitePool y).1
    have hx := Finset.le_sup' (fun j => x.1 j+∑ i ∈ Finset.univ.erase j, x.2 i)
      (Finset.mem_univ j)
    have hy := Finset.le_sup' (fun j => y.1 j+∑ i ∈ Finset.univ.erase j, y.2 i)
      (Finset.mem_univ j)
    have h := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    simpa only [Prod.fst_add, Prod.snd_add, Prod.fst_smul, Prod.snd_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, mul_add, finitePool, add_assoc, add_left_comm, add_comm] using h
  · change (∑ i, (a*x.2 i+b*y.2 i)) ≤ a*(∑ i, x.2 i)+b*(∑ i, y.2 i)
    simp only [Prod.snd_add, Prod.snd_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, finitePool, le_refl]

/-- Complete source maxpool proposition for the actual sup/erase-sum functions. -/
theorem maxpool_properties {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] :
    (∀ x, (finitePool (ι := ι) x).1-(finitePool x).2 =
      Finset.univ.sup' Finset.univ_nonempty (fun j => x.1 j-x.2 j)) ∧
    (∀ x, 0≤x → 0≤finitePool (ι := ι) x) ∧
    Monotone (finitePool (ι := ι)) ∧
    ConvexOn ℝ Set.univ (fun x => (finitePool (ι := ι) x).1) ∧
    ConvexOn ℝ Set.univ (fun x => (finitePool (ι := ι) x).2) :=
  ⟨finitePool_recovery, finitePool_nonnegative, finitePool_monotone,
    finitePool_convex⟩

/-- A shared winning index is selected from the represented activations. -/
def PoolWinner {ι : Type*} (x : (ι → ℝ) × (ι → ℝ)) (j : ι) : Prop :=
  ∀ i, x.1 i-x.2 i ≤ x.1 j-x.2 j

theorem poolWinner_exists {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : (ι → ℝ) × (ι → ℝ)) : ∃ j, PoolWinner x j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => x.1 j-x.2 j)
  refine ⟨j, fun i => ?_⟩
  rw [← hj]
  exact Finset.le_sup' (fun j => x.1 j-x.2 j) (Finset.mem_univ i)

noncomputable def poolWinner {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : (ι → ℝ) × (ι → ℝ)) : ι := Classical.choose (poolWinner_exists x)

noncomputable def winnerPool {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : (ι → ℝ) × (ι → ℝ)) : ℝ × ℝ :=
  (x.1 (poolWinner x), x.2 (poolWinner x))

theorem winnerPool_recovery {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : (ι → ℝ) × (ι → ℝ)) :
    (winnerPool x).1-(winnerPool x).2 =
      Finset.univ.sup' Finset.univ_nonempty (fun j => x.1 j-x.2 j) := by
  change x.1 (poolWinner x)-x.2 (poolWinner x) = _
  apply le_antisymm
  · exact Finset.le_sup' (fun j => x.1 j-x.2 j) (Finset.mem_univ (poolWinner x))
  · exact (Finset.sup'_le_iff _ _).mpr (fun i _ => (Classical.choose_spec (poolWinner_exists x)) i)

theorem winnerPool_nonnegative {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : (ι → ℝ) × (ι → ℝ)) (hx : 0≤x) : 0≤winnerPool x :=
  ⟨hx.1 _, hx.2 _⟩

end HiddenMonotonicity
