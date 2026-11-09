import Thesis.AffineMaxPartition
import Thesis.SignedMaxIdentities
import Thesis.SignedMaxReduction
set_option pp.explicit true
set_option pp.universes true

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxIdentities
open scoped Classical
example : ∀ {A : Type} [DecidableEq A] (f : A → ℝ) (B : Finset A) (hB : B.Nonempty)
    (a : A) (ha : f a ≤ B.sup' hB f) (S : Finset A),
    baseMax f B hB (insert a S) = baseMax f B hB S := @Thesis.SignedMaxIdentities.baseMax_insert_dominated
#check @Thesis.SignedMaxIdentities.baseMax_insert_dominated
#print axioms Thesis.SignedMaxIdentities.baseMax_insert_dominated
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxIdentities
open scoped Classical
example : ∀ {A : Type} [DecidableEq A] (S : Finset A) (a : A) (ha : a ∈ S)
    (F : Finset A → ℝ)
    (hF : ∀ T ⊆ S.erase a, F (insert a T) = F T),
    (∑ T ∈ S.powerset, (-1 : ℝ)^T.card * F T) = 0 := @Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion
#check @Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion
#print axioms Thesis.SignedMaxIdentities.alternating_sum_zero_of_insertion
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxIdentities
open scoped Classical
example : ∀ {A : Type} [DecidableEq A] (f : A → ℝ) (A₀ B : Finset A) (hB : B.Nonempty)
    (hdom : ∃ a ∈ A₀, f a ≤ B.sup' hB f),
    (∑ S ∈ A₀.powerset, (-1 : ℝ)^S.card * baseMax f B hB S) = 0 := @Thesis.SignedMaxIdentities.alternating_max_zero
#check @Thesis.SignedMaxIdentities.alternating_max_zero
#print axioms Thesis.SignedMaxIdentities.alternating_max_zero
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.AffineMaxPartition
open scoped Classical
example : ∀ {I : Type} [Fintype I] (p : Polynomial I)
    (hcard : Fintype.card I + 1 < Fintype.card p.Terms),
    ∃ c : p.Terms → ℝ, (∑ i, c i) = 0 ∧ (∑ i, c i • p.slope i) = 0 ∧ ∃ i, c i ≠ 0 := @Thesis.AffineMaxPartition.dependence_coefficients
#check @Thesis.AffineMaxPartition.dependence_coefficients
#print axioms Thesis.AffineMaxPartition.dependence_coefficients
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.AffineMaxPartition
open scoped Classical
example : ∀ {I : Type} [Fintype I] (p : Polynomial I)
    (hcard : Fintype.card I + 1 < Fintype.card p.Terms),
    ∃ c : p.Terms → ℝ, (∑ i, c i) = 0 ∧ (∑ i, c i • p.slope i) = 0 ∧
      (∑ i, c i * p.intercept i) ≤ 0 ∧ ∃ i, c i ≠ 0 := @Thesis.AffineMaxPartition.oriented_dependence
#check @Thesis.AffineMaxPartition.oriented_dependence
#print axioms Thesis.AffineMaxPartition.oriented_dependence
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.AffineMaxPartition
open scoped Classical
example : ∀ {I : Type} [Fintype I] (p : Polynomial I) (c : p.Terms → ℝ)
    (hv : (∑ i, c i • p.slope i) = 0) (x : I → ℝ),
    (∑ i, c i * (p.slope i ⬝ᵥ x + p.intercept i)) = ∑ i, c i * p.intercept i := @Thesis.AffineMaxPartition.weighted_affine_constant
#check @Thesis.AffineMaxPartition.weighted_affine_constant
#print axioms Thesis.AffineMaxPartition.weighted_affine_constant
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.AffineMaxPartition
open scoped Classical
example : ∀ {I : Type} [Fintype I] (p : Polynomial I)
    (hcard : Fintype.card I + 1 < Fintype.card p.Terms),
    ∃ (A B : Finset p.Terms) (_ : A.Nonempty) (hB : B.Nonempty),
      Disjoint A B ∧ A ∪ B = Finset.univ ∧
      ∀ x : I → ℝ, ∃ a ∈ A,
        p.slope a ⬝ᵥ x + p.intercept a ≤ B.sup' hB (fun b => p.slope b ⬝ᵥ x + p.intercept b) := @Thesis.AffineMaxPartition.global_partition
#check @Thesis.AffineMaxPartition.global_partition
#print axioms Thesis.AffineMaxPartition.global_partition
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
example : ∀ {I : Type} (p : Polynomial I) (S : Finset p.Terms) (hS : S.Nonempty),
    Fintype.card (restrict p S hS).Terms = S.card := @Thesis.SignedMaxReduction.restrict_card
#check @Thesis.SignedMaxReduction.restrict_card
#print axioms Thesis.SignedMaxReduction.restrict_card
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
example : ∀ {I : Type} [Fintype I] (p : Polynomial I) (S : Finset p.Terms) (hS : S.Nonempty)
    (x : I → ℝ),
    (restrict p S hS).eval x = S.sup' hS (fun a => p.slope a ⬝ᵥ x + p.intercept a) := @Thesis.SignedMaxReduction.restrict_eval
#check @Thesis.SignedMaxReduction.restrict_eval
#print axioms Thesis.SignedMaxReduction.restrict_eval
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
example : ∀ {I : Type} [Fintype I] (p : Polynomial I),
    p.eval ∈ smallSpan I := @Thesis.SignedMaxReduction.eval_mem_smallSpan
#check @Thesis.SignedMaxReduction.eval_mem_smallSpan
#print axioms Thesis.SignedMaxReduction.eval_mem_smallSpan
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
example : ∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ)
    (hf : f ∈ smallSpan I),
    ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Polynomial I),
      (∀ j, Fintype.card (q j).Terms ≤ Fintype.card I + 1) ∧
      ∀ x, f x = ∑ j, c j * (q j).eval x := @Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan
#check @Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan
#print axioms Thesis.SignedMaxReduction.finite_representation_of_mem_smallSpan
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
example : ∀ {I : Type} [Fintype I] (p : Polynomial I),
    ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Polynomial I),
      (∀ j, Fintype.card (q j).Terms ≤ Fintype.card I + 1) ∧
      ∀ x, p.eval x = ∑ j, c j * (q j).eval x := @Thesis.SignedMaxReduction.polynomial_signed_small_max
#check @Thesis.SignedMaxReduction.polynomial_signed_small_max
#print axioms Thesis.SignedMaxReduction.polynomial_signed_small_max
end

noncomputable section
open Finset Matrix Thesis.Tropical Thesis.SignedMaxReduction
open scoped Classical
example : ∀ {I : Type} [Fintype I] (p r : Polynomial I),
    ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Polynomial I),
      (∀ j, Fintype.card (q j).Terms ≤ Fintype.card I + 1) ∧
      ∀ x, p.eval x - r.eval x = ∑ j, c j * (q j).eval x := @Thesis.SignedMaxReduction.difference_signed_small_max
#check @Thesis.SignedMaxReduction.difference_signed_small_max
#print axioms Thesis.SignedMaxReduction.difference_signed_small_max
end
