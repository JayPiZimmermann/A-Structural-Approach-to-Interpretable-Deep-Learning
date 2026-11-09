import Thesis.AffineMaxPartition

/-! Every finite maximum of affine functions on `ℝ^d` is a real linear
combination of maxima with at most `d+1` terms. The proof reduces the number
of terms using affine dependence and finite inclusion-exclusion. -/
noncomputable section
namespace Thesis.SignedMaxReduction
open Finset Matrix Thesis.Tropical
open scoped Classical

variable {I : Type} [Fintype I]

def restrict (p : Polynomial I) (S : Finset p.Terms) (hS : S.Nonempty) : Polynomial I where
  Terms := S
  finite := inferInstance
  inhabited := hS.to_subtype
  slope := fun a => p.slope a
  intercept := fun a => p.intercept a

omit [Fintype I] in
theorem restrict_card (p : Polynomial I) (S : Finset p.Terms) (hS : S.Nonempty) :
    Fintype.card (restrict p S hS).Terms = S.card := Fintype.card_coe S

theorem restrict_eval (p : Polynomial I) (S : Finset p.Terms) (hS : S.Nonempty)
    (x : I → ℝ) :
    (restrict p S hS).eval x = S.sup' hS (fun a => p.slope a ⬝ᵥ x + p.intercept a) := by
  let : Nonempty S := hS.to_subtype
  change finiteMax (fun a : S => p.slope a ⬝ᵥ x + p.intercept a) = _
  apply le_antisymm
  · apply finiteMax_le
    intro a
    exact S.le_sup' (fun a => p.slope a ⬝ᵥ x + p.intercept a) a.property
  · apply Finset.sup'_le
    intro a ha
    exact le_finiteMax (fun b : S => p.slope b ⬝ᵥ x + p.intercept b) ⟨a, ha⟩

def smallSpan (I : Type) [Fintype I] : Submodule ℝ ((I → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (fun p : {q : Polynomial I //
    Fintype.card q.Terms ≤ Fintype.card I + 1} => p.val.eval))

theorem eval_mem_smallSpan (p : Polynomial I) : p.eval ∈ smallSpan I := by
  classical
  suffices ∀ n (q : Polynomial I), Fintype.card q.Terms = n → q.eval ∈ smallSpan I from
    this _ p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q hq
    by_cases hsmall : Fintype.card q.Terms ≤ Fintype.card I + 1
    · exact Submodule.subset_span ⟨⟨q, hsmall⟩, rfl⟩
    obtain ⟨A, B, hA, hB, hd, hab, hdom⟩ :=
      Thesis.AffineMaxPartition.global_partition q (lt_of_not_ge hsmall)
    let F : Finset q.Terms → ((I → ℝ) → ℝ) :=
      fun S => (restrict q (B ∪ S) (hB.mono Finset.subset_union_left)).eval
    have hzero : (∑ S ∈ A.powerset, (-1 : ℝ)^S.card • F S) = 0 := by
      ext x
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        F, restrict_eval, Thesis.SignedMaxIdentities.baseMax] using
        Thesis.SignedMaxIdentities.alternating_max_zero
          (fun a => q.slope a ⬝ᵥ x + q.intercept a) A B hB (hdom x)
    have htop : F A = q.eval := by
      funext x
      rw [show F A x = (B ∪ A).sup' (hB.mono Finset.subset_union_left)
        (fun a => q.slope a ⬝ᵥ x + q.intercept a) from restrict_eval q _ _ x]
      simp only [Finset.union_comm B A, hab]
      rfl
    have hrest : (∑ S ∈ A.powerset.erase A, (-1 : ℝ)^S.card • F S) ∈ smallSpan I := by
      apply Submodule.sum_mem
      intro S hS
      apply Submodule.smul_mem
      have hsA : S ⊆ A := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS)
      have hne : S ≠ A := (Finset.mem_erase.mp hS).1
      have hlt : S.card < A.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsA, hne⟩)
      have hbs : Disjoint B S := hd.symm.mono_right hsA
      have hcard : Fintype.card (restrict q (B ∪ S) (hB.mono Finset.subset_union_left)).Terms < n := by
        rw [restrict_card, Finset.card_union_of_disjoint hbs]
        have habcard := Finset.card_union_of_disjoint hd
        rw [hab, Finset.card_univ, hq] at habcard
        omega
      exact ih _ hcard _ rfl
    have hsum := Finset.sum_erase_add A.powerset
      (fun S => (-1 : ℝ)^S.card • F S) (Finset.mem_powerset_self A)
    rw [hzero, htop] at hsum
    have hscaled : (-1 : ℝ)^A.card • q.eval ∈ smallSpan I := by
      have heq : (-1 : ℝ)^A.card • q.eval =
          -(∑ S ∈ A.powerset.erase A, (-1 : ℝ)^S.card • F S) :=
        eq_neg_of_add_eq_zero_right hsum
      rw [heq]
      exact Submodule.neg_mem _ hrest
    exact ((smallSpan I).smul_mem_iff
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))).mp hscaled

theorem finite_representation_of_mem_smallSpan (f : (I → ℝ) → ℝ)
    (hf : f ∈ smallSpan I) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Polynomial I),
      (∀ j, Fintype.card (q j).Terms ≤ Fintype.card I + 1) ∧
      ∀ x, f x = ∑ j, c j * (q j).eval x := by
  classical
  let Small := {q : Polynomial I // Fintype.card q.Terms ≤ Fintype.card I + 1}
  have hm : f ∈ Submodule.span ℝ (Set.range (fun q : Small => q.val.eval)) := hf
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  let e := (Fintype.equivFin c.support).symm
  refine ⟨Fintype.card c.support, (fun j => c (e j).val),
    (fun j => (e j).val.val), (fun j => (e j).val.property), ?_⟩
  intro x
  have hx := congrFun hc x
  change f x = ∑ j, c (e j).val * (e j).val.val.eval x
  rw [e.sum_comp (fun i : c.support => c i.val * i.val.val.eval x)]
  rw [Finset.sum_coe_sort c.support (fun i : Small => c i * i.val.eval x)]
  simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx.symm

/-- Dimension-only finite signed-max representation. Coefficients are unrestricted
real numbers; every maximum is nonempty and has at most `dim+1` affine terms. -/
theorem polynomial_signed_small_max (p : Polynomial I) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Polynomial I),
      (∀ j, Fintype.card (q j).Terms ≤ Fintype.card I + 1) ∧
      ∀ x, p.eval x = ∑ j, c j * (q j).eval x :=
  finite_representation_of_mem_smallSpan p.eval (eval_mem_smallSpan p)

theorem difference_signed_small_max (p r : Polynomial I) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Polynomial I),
      (∀ j, Fintype.card (q j).Terms ≤ Fintype.card I + 1) ∧
      ∀ x, p.eval x - r.eval x = ∑ j, c j * (q j).eval x :=
  finite_representation_of_mem_smallSpan (p.eval - r.eval)
    ((smallSpan I).sub_mem (eval_mem_smallSpan p) (eval_mem_smallSpan r))

end Thesis.SignedMaxReduction
