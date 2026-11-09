import Thesis.Tropical
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Exact finite signed-max elimination. A globally dominated member of one
side of a partition makes its alternating powerset sum vanish, pointwise. -/
noncomputable section
namespace Thesis.SignedMaxIdentities
open Finset

variable {A : Type} [DecidableEq A]

def baseMax (f : A → ℝ) (B : Finset A) (hB : B.Nonempty) (S : Finset A) : ℝ :=
  (B ∪ S).sup' (hB.mono subset_union_left) f

theorem baseMax_insert_dominated (f : A → ℝ) (B : Finset A) (hB : B.Nonempty)
    (a : A) (ha : f a ≤ B.sup' hB f) (S : Finset A) :
    baseMax f B hB (insert a S) = baseMax f B hB S := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (B.le_sup' f hi).trans (Finset.sup'_mono f subset_union_left hB)
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha.trans (Finset.sup'_mono f subset_union_left hB)
      · exact (B ∪ S).le_sup' f (Finset.mem_union_right B hi)
  · exact Finset.sup'_mono f (Finset.union_subset_union_right (Finset.subset_insert a S)) _

theorem alternating_sum_zero_of_insertion (S : Finset A) (a : A) (ha : a ∈ S)
    (F : Finset A → ℝ)
    (hF : ∀ T ⊆ S.erase a, F (insert a T) = F T) :
    (∑ T ∈ S.powerset, (-1 : ℝ)^T.card * F T) = 0 := by
  have hsum := Finset.sum_powerset_insert (Finset.notMem_erase a S)
    (fun T => (-1 : ℝ)^T.card * F T)
  rw [Finset.insert_erase ha] at hsum
  rw [hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro T hT
  have hsub := Finset.mem_powerset.mp hT
  have hnot : a ∉ T := fun h => Finset.notMem_erase a S (hsub h)
  rw [Finset.card_insert_of_notMem hnot, pow_succ, hF T hsub]
  ring

/-- Inclusion-exclusion eliminates the full maximum whenever min(A) ≤ max(B). -/
theorem alternating_max_zero (f : A → ℝ) (A₀ B : Finset A) (hB : B.Nonempty)
    (hdom : ∃ a ∈ A₀, f a ≤ B.sup' hB f) :
    (∑ S ∈ A₀.powerset, (-1 : ℝ)^S.card * baseMax f B hB S) = 0 := by
  obtain ⟨a, ha, hdom⟩ := hdom
  exact alternating_sum_zero_of_insertion A₀ a ha _
    (fun S _ => baseMax_insert_dominated f B hB a hdom S)

end Thesis.SignedMaxIdentities
