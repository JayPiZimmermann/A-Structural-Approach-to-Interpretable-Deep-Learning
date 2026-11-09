import Thesis.SignedMaxIdentities
import Mathlib.Analysis.Convex.Radon
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! A dimension-controlled affine dependence of gradients, oriented by the
intercepts, gives a global min-versus-max partition of the affine functions.
The constant offset is retained; the argument does not homogenize into dimension d+1. -/
noncomputable section
namespace Thesis.AffineMaxPartition
open Finset Matrix Thesis.Tropical
open scoped Classical

variable {I : Type} [Fintype I]

theorem dependence_coefficients (p : Polynomial I)
    (hcard : Fintype.card I + 1 < Fintype.card p.Terms) :
    ∃ c : p.Terms → ℝ, (∑ i, c i) = 0 ∧ (∑ i, c i • p.slope i) = 0 ∧ ∃ i, c i ≠ 0 := by
  have hdep : ¬ AffineIndependent ℝ p.slope := by
    intro hi
    have hc := hi.card_le_finrank_succ
    have hd := Submodule.finrank_le (vectorSpan ℝ (Set.range p.slope))
    rw [Module.finrank_pi] at hd
    omega
  rw [affineIndependent_iff_of_fintype] at hdep
  push Not at hdep
  obtain ⟨c, hc, hv, i, hi⟩ := hdep
  refine ⟨c, hc, ?_, i, hi⟩
  rwa [Finset.weightedVSub_eq_linear_combination _ hc] at hv

theorem oriented_dependence (p : Polynomial I)
    (hcard : Fintype.card I + 1 < Fintype.card p.Terms) :
    ∃ c : p.Terms → ℝ, (∑ i, c i) = 0 ∧ (∑ i, c i • p.slope i) = 0 ∧
      (∑ i, c i * p.intercept i) ≤ 0 ∧ ∃ i, c i ≠ 0 := by
  obtain ⟨c, hc, hv, i, hi⟩ := dependence_coefficients p hcard
  by_cases hb : (∑ i, c i * p.intercept i) ≤ 0
  · exact ⟨c, hc, hv, hb, i, hi⟩
  · refine ⟨fun i => -c i, ?_, ?_, ?_, i, neg_ne_zero.mpr hi⟩
    · simp [hc]
    · simp_rw [neg_smul, Finset.sum_neg_distrib, hv, neg_zero]
    · simpa only [neg_mul, Finset.sum_neg_distrib] using
        (neg_nonpos.mpr (le_of_not_ge hb))

theorem weighted_affine_constant (p : Polynomial I) (c : p.Terms → ℝ)
    (hv : (∑ i, c i • p.slope i) = 0) (x : I → ℝ) :
    (∑ i, c i * (p.slope i ⬝ᵥ x + p.intercept i)) = ∑ i, c i * p.intercept i := by
  have hz : (∑ i, c i * (p.slope i ⬝ᵥ x)) = 0 := by
    simpa only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] using
      congrArg (fun v : I → ℝ => v ⬝ᵥ x) hv
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, hz, zero_add]

theorem global_partition (p : Polynomial I)
    (hcard : Fintype.card I + 1 < Fintype.card p.Terms) :
    ∃ (A B : Finset p.Terms) (_ : A.Nonempty) (hB : B.Nonempty),
      Disjoint A B ∧ A ∪ B = Finset.univ ∧
      ∀ x : I → ℝ, ∃ a ∈ A,
        p.slope a ⬝ᵥ x + p.intercept a ≤ B.sup' hB (fun b => p.slope b ⬝ᵥ x + p.intercept b) := by
  classical
  obtain ⟨c, hc, hv, hb, i, hi⟩ := oriented_dependence p hcard
  obtain ⟨a, _, ha⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero c hc
    ⟨i, Finset.mem_univ i, hi⟩
  obtain ⟨b, _, hbn⟩ := Finset.exists_neg_of_sum_zero_of_exists_nonzero c hc
    ⟨i, Finset.mem_univ i, hi⟩
  let A : Finset p.Terms := Finset.univ.filter (fun i => 0 < c i)
  let B : Finset p.Terms := Finset.univ \ A
  have hA : A.Nonempty := ⟨a, by simp [A, ha]⟩
  have hB : B.Nonempty := ⟨b, by simp [B, A, not_lt_of_ge hbn.le]⟩
  refine ⟨A, B, hA, hB, ?_, ?_, ?_⟩
  · exact Finset.disjoint_sdiff
  · ext i
    by_cases hi : i ∈ A <;> simp [B, hi]
  · intro x
    by_contra! hn
    let M := B.sup' hB (fun b => p.slope b ⬝ᵥ x + p.intercept b)
    have ht (j : p.Terms) : 0 ≤ c j * ((p.slope j ⬝ᵥ x + p.intercept j) - M) := by
      by_cases hj : 0 < c j
      · exact (mul_pos hj (sub_pos.mpr (hn j (by simp [A, hj])))).le
      · have hjB : j ∈ B := by simp [B, A, hj]
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hj)
          (sub_nonpos.mpr (B.le_sup' (fun b => p.slope b ⬝ᵥ x + p.intercept b) hjB))
    have hpos : 0 < ∑ j, c j * ((p.slope j ⬝ᵥ x + p.intercept j) - M) :=
      Finset.sum_pos' (fun j _ => ht j)
        ⟨a, Finset.mem_univ a, mul_pos ha (sub_pos.mpr (hn a (by simp [A, ha])))⟩
    have he : (∑ j, c j * ((p.slope j ⬝ᵥ x + p.intercept j) - M)) =
        ∑ j, c j * p.intercept j := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hc, zero_mul, sub_zero,
        weighted_affine_constant p c hv x]
    rw [he] at hpos
    exact (not_lt_of_ge hb) hpos

end Thesis.AffineMaxPartition
