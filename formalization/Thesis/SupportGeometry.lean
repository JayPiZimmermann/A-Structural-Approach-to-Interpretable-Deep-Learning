import Thesis.Tropical
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

/-! Support-function geometry of finite convex hulls, including separation and
an exact subdifferential/maximizing-face characterization. -/
noncomputable section
namespace Thesis.Tropical
open Finset Matrix
variable {I A B : Type} [Fintype I] [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

/-- Every real linear functional in coordinates has the usual dot-product form. -/
theorem linear_eq_dot (f : (I → ℝ) →ₗ[ℝ] ℝ) : ∃ c : I → ℝ, ∀ y, f y = y ⬝ᵥ c := by
  classical
  refine ⟨fun i => f (Pi.single i 1),?_⟩
  intro y
  have hy : y = ∑ i, y i • (Pi.single i 1 : I → ℝ) := by
    funext j
    simp [Finset.sum_apply,Pi.single_apply]
  rw [hy,map_sum]
  simp only [map_smul,smul_eq_mul,dotProduct,Finset.sum_apply,Pi.smul_apply]
  simp [Pi.single_apply]

/-- Every point of a polytope satisfies all inequalities prescribed by its support. -/
theorem dot_le_support_hull (v : A → I → ℝ) {p : I → ℝ}
    (hp : p ∈ convexHull ℝ (Set.range v)) (x : I → ℝ) :
    p ⬝ᵥ x ≤ support (convexHull ℝ (Set.range v)) x := by
  rw [support_convexHull]
  have hs : convexHull ℝ (Set.range v) ⊆ {p | p ⬝ᵥ x ≤ finiteMax (fun a => v a ⬝ᵥ x)} := by
    apply convexHull_min
    · rintro _ ⟨a,rfl⟩; exact le_finiteMax (fun a => v a ⬝ᵥ x) a
    · exact (convex_Iic _).linear_preimage (dotLinear x)
  exact hs hp

/-- Halfspace description, proved using strict separation, not assumed as a
property of a renamed support function. -/
theorem mem_hull_iff_support (v : A → I → ℝ) (p : I → ℝ) :
    p ∈ convexHull ℝ (Set.range v) ↔ ∀ x, p ⬝ᵥ x ≤ support (convexHull ℝ (Set.range v)) x := by
  constructor
  · exact fun hp x => dot_le_support_hull v hp x
  · intro h
    by_contra hp
    obtain ⟨f,u,hv,hp'⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (Set.range v)) ((Set.finite_range v).isClosed_convexHull ℝ) hp
    obtain ⟨c,hc⟩ := linear_eq_dot f.toLinearMap
    obtain ⟨a,ha⟩ := finiteMax_attained (fun a => v a ⬝ᵥ c)
    have hv' := hv (v a) (subset_convexHull ℝ _ ⟨a,rfl⟩)
    have hbound := h c
    rw [support_convexHull,ha] at hbound
    have hc1 := hc (v a)
    have hc2 := hc p
    change f (v a) = _ at hc1
    change f p = _ at hc2
    linarith

/-- Polytope inclusion is exactly pointwise support-function domination. -/
theorem hull_subset_iff_support (v : A → I → ℝ) (w : B → I → ℝ) :
    convexHull ℝ (Set.range v) ⊆ convexHull ℝ (Set.range w) ↔
      ∀ x, support (convexHull ℝ (Set.range v)) x ≤ support (convexHull ℝ (Set.range w)) x := by
  constructor
  · intro h x
    rw [support_convexHull]
    apply finiteMax_le
    intro a
    exact dot_le_support_hull w (h (subset_convexHull ℝ _ ⟨a,rfl⟩)) x
  · intro h p hp
    exact (mem_hull_iff_support w p).mpr fun x => (dot_le_support_hull v hp x).trans (h x)

/-- In particular, a finite convex hull is uniquely determined by its support function. -/
theorem hull_eq_of_support_eq (v : A → I → ℝ) (w : B → I → ℝ)
    (h : support (convexHull ℝ (Set.range v)) = support (convexHull ℝ (Set.range w))) :
    convexHull ℝ (Set.range v) = convexHull ℝ (Set.range w) := by
  apply Set.Subset.antisymm
  · exact (hull_subset_iff_support v w).mpr (fun x => (congrFun h x).le)
  · exact (hull_subset_iff_support w v).mpr (fun x => (congrFun h.symm x).le)

theorem support_hull_zero (v : A → I → ℝ) : support (convexHull ℝ (Set.range v)) 0 = 0 := by
  rw [support_convexHull]
  simp [finiteMax]

theorem support_hull_homogeneous (v : A → I → ℝ) (c : ℝ) (hc : 0 ≤ c) (x : I → ℝ) :
    support (convexHull ℝ (Set.range v)) (c • x) = c*support (convexHull ℝ (Set.range v)) x := by
  rw [support_convexHull,support_convexHull]
  simp only [dotProduct_smul,smul_eq_mul]
  apply le_antisymm
  · apply finiteMax_le
    intro a
    exact mul_le_mul_of_nonneg_left (le_finiteMax (fun a => v a ⬝ᵥ x) a) hc
  · obtain ⟨a,ha⟩ := finiteMax_attained (fun a => v a ⬝ᵥ x)
    rw [ha]
    exact le_finiteMax (fun a => c*(v a ⬝ᵥ x)) a

/-- The standard supporting-hyperplane inequality defining a subgradient. -/
def Subgradient (u : (I → ℝ) → ℝ) (x s : I → ℝ) : Prop :=
  ∀ y, u x+s ⬝ᵥ (y-x) ≤ u y

/-- prop:subdifferential_face, equality of the entire subdifferential with the
maximizing face of the actual finite convex hull. -/
theorem subgradient_iff_maximizing_face (v : A → I → ℝ) (x s : I → ℝ) :
    Subgradient (support (convexHull ℝ (Set.range v))) x s ↔
      s ∈ convexHull ℝ (Set.range v) ∧ s ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x := by
  constructor
  · intro h
    have hzero := h 0
    have htwo := h ((2 : ℝ) • x)
    rw [support_hull_zero] at hzero
    rw [support_hull_homogeneous v 2 (by norm_num)] at htwo
    simp only [dotProduct_sub,dotProduct_zero,dotProduct_smul,smul_eq_mul] at hzero htwo
    have he : s ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x := by linarith
    refine ⟨(mem_hull_iff_support v s).mpr ?_,he⟩
    intro y
    have hy := h y
    rw [dotProduct_sub,he] at hy
    linarith
  · rintro ⟨hs,he⟩ y
    have hy := dot_le_support_hull v hs y
    rw [dotProduct_sub,he]
    linarith

end Thesis.Tropical
