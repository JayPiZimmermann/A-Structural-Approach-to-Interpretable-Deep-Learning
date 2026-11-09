import Thesis.SupportGeometry
import Mathlib.Topology.Order.Compact

/-! Support calculus at the full nonempty compact convex scope of the thesis,
not restricted to finite polytopes. -/
noncomputable section
namespace Thesis.Tropical
open Finset Matrix
open scoped Pointwise
variable {I : Type} [Fintype I]
variable {P Q : Set (I → ℝ)}

theorem support_greatest (hP : IsCompact P) (hne : P.Nonempty) (x : I → ℝ) :
    IsGreatest ((fun p => p ⬝ᵥ x) '' P) (support P x) := by
  obtain ⟨p,hp,hm⟩ := hP.exists_isMaxOn hne (dotLinear x).toContinuousLinearMap.continuous.continuousOn
  have hg : IsGreatest ((fun p => p ⬝ᵥ x) '' P) (p ⬝ᵥ x) := by
    refine ⟨⟨p,hp,rfl⟩,?_⟩
    rintro _ ⟨q,hq,rfl⟩
    exact hm hq
  change IsGreatest _ (sSup _)
  rw [hg.csSup_eq]
  exact hg

theorem support_attained (hP : IsCompact P) (hne : P.Nonempty) (x : I → ℝ) :
    ∃ p ∈ P, p ⬝ᵥ x = support P x := (support_greatest hP hne x).1

theorem dot_le_support (hP : IsCompact P) (hne : P.Nonempty) {p : I → ℝ}
    (hp : p ∈ P) (x : I → ℝ) : p ⬝ᵥ x ≤ support P x :=
  (support_greatest hP hne x).2 ⟨p,hp,rfl⟩

/-- Convexity on the full ambient space for every nonempty compact set. -/
theorem support_convex (hP : IsCompact P) (hne : P.Nonempty) :
    ConvexOn ℝ Set.univ (support P) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb _
  obtain ⟨p,hp,he⟩ := support_attained hP hne (a • x+b • y)
  rw [← he,dotProduct_add,dotProduct_smul,dotProduct_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left (dot_le_support hP hne hp x) ha)
    (mul_le_mul_of_nonneg_left (dot_le_support hP hne hp y) hb)

theorem support_homogeneous (hP : IsCompact P) (hne : P.Nonempty)
    (c : ℝ) (hc : 0 ≤ c) (x : I → ℝ) : support P (c • x) = c*support P x := by
  obtain ⟨p,hp,he⟩ := support_attained hP hne (c • x)
  obtain ⟨q,hq,hq'⟩ := support_attained hP hne x
  apply le_antisymm
  · rw [← he,dotProduct_smul]
    exact mul_le_mul_of_nonneg_left (dot_le_support hP hne hp x) hc
  · rw [← hq']
    have h := dot_le_support hP hne hq (c • x)
    simpa only [dotProduct_smul,smul_eq_mul] using h

/-- Taking a convex hull leaves every support value unchanged. -/
theorem support_convexHull_compact (hP : IsCompact P) (hne : P.Nonempty) (x : I → ℝ) :
    support (convexHull ℝ P) x = support P x := by
  apply IsGreatest.csSup_eq
  refine ⟨?_,?_⟩
  · obtain ⟨p,hp,he⟩ := support_attained hP hne x
    exact ⟨p,subset_convexHull ℝ _ hp,he⟩
  · rintro _ ⟨p,hp,rfl⟩
    have hs : convexHull ℝ P ⊆ {p | p ⬝ᵥ x ≤ support P x} :=
      convexHull_min (fun _ hp => dot_le_support hP hne hp x)
        ((convex_Iic _).linear_preimage (dotLinear x))
    exact hs hp

/-- Minkowski sums turn into sums of support functions. -/
theorem support_minkowski (hP : IsCompact P) (hneP : P.Nonempty)
    (hQ : IsCompact Q) (hneQ : Q.Nonempty) (x : I → ℝ) :
    support (P+Q) x = support P x+support Q x := by
  apply IsGreatest.csSup_eq
  refine ⟨?_,?_⟩
  · obtain ⟨p,hp,he⟩ := support_attained hP hneP x
    obtain ⟨q,hq,hq'⟩ := support_attained hQ hneQ x
    refine ⟨p+q,⟨p,hp,q,hq,rfl⟩,?_⟩
    dsimp only
    rw [add_dotProduct,he,hq']
  · rintro _ ⟨_,⟨p,hp,q,hq,rfl⟩,rfl⟩
    dsimp only
    rw [add_dotProduct]
    exact add_le_add (dot_le_support hP hneP hp x) (dot_le_support hQ hneQ hq x)

theorem support_union (hP : IsCompact P) (hneP : P.Nonempty)
    (hQ : IsCompact Q) (hneQ : Q.Nonempty) (x : I → ℝ) :
    support (P∪Q) x = max (support P x) (support Q x) := by
  apply IsGreatest.csSup_eq
  refine ⟨?_,?_⟩
  · rcases le_total (support P x) (support Q x) with h | h
    · obtain ⟨q,hq,he⟩ := support_attained hQ hneQ x
      exact ⟨q,Or.inr hq,he.trans (max_eq_right h).symm⟩
    · obtain ⟨p,hp,he⟩ := support_attained hP hneP x
      exact ⟨p,Or.inl hp,he.trans (max_eq_left h).symm⟩
  · rintro _ ⟨p,hp,rfl⟩
    rcases hp with hp | hp
    · exact (dot_le_support hP hneP hp x).trans (le_max_left _ _)
    · exact (dot_le_support hQ hneQ hp x).trans (le_max_right _ _)

/-- Convex hull of a union turns into the pointwise maximum of support functions. -/
theorem support_hull_union (hP : IsCompact P) (hneP : P.Nonempty)
    (hQ : IsCompact Q) (hneQ : Q.Nonempty) (x : I → ℝ) :
    support (convexHull ℝ (P∪Q)) x = max (support P x) (support Q x) := by
  rw [support_convexHull_compact (hP.union hQ) hneP.inl,support_union hP hneP hQ hneQ]

/-- Full compact-convex halfspace description by strict Hahn--Banach separation. -/
theorem mem_compact_iff_support (hP : IsCompact P) (hne : P.Nonempty) (hc : Convex ℝ P)
    (p : I → ℝ) : p ∈ P ↔ ∀ x, p ⬝ᵥ x ≤ support P x := by
  constructor
  · exact fun hp x => dot_le_support hP hne hp x
  · intro h
    by_contra hp
    obtain ⟨f,u,hf,hp'⟩ := geometric_hahn_banach_closed_point hc hP.isClosed hp
    obtain ⟨x,hx⟩ := linear_eq_dot f.toLinearMap
    obtain ⟨q,hq,he⟩ := support_attained hP hne x
    have hqx := hx q
    have hpx := hx p
    change f q = _ at hqx
    change f p = _ at hpx
    have hq' := hf q hq
    have hbound := h x
    rw [← he] at hbound
    linarith

/-- lem:support_properties.3 at its original arbitrary compact-convex scope. -/
theorem compact_subset_iff_support (hP : IsCompact P) (hneP : P.Nonempty)
    (hQ : IsCompact Q) (hneQ : Q.Nonempty) (hcQ : Convex ℝ Q) :
    P ⊆ Q ↔ ∀ x, support P x ≤ support Q x := by
  constructor
  · intro h x
    obtain ⟨p,hp,he⟩ := support_attained hP hneP x
    rw [← he]
    exact dot_le_support hQ hneQ (h hp) x
  · intro h p hp
    exact (mem_compact_iff_support hQ hneQ hcQ p).mpr fun x =>
      (dot_le_support hP hneP hp x).trans (h x)

theorem compact_eq_of_support_eq (hP : IsCompact P) (hneP : P.Nonempty) (hcP : Convex ℝ P)
    (hQ : IsCompact Q) (hneQ : Q.Nonempty) (hcQ : Convex ℝ Q)
    (h : support P = support Q) : P = Q := by
  apply Set.Subset.antisymm
  · exact (compact_subset_iff_support hP hneP hQ hneQ hcQ).mpr (fun x => (congrFun h x).le)
  · exact (compact_subset_iff_support hQ hneQ hP hneP hcP).mpr (fun x => (congrFun h.symm x).le)

end Thesis.Tropical
