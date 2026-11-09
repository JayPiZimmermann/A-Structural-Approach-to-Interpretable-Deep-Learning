import Thesis.SupportGeometry
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Extreme

/-! Actual Fréchet derivatives of polytope support functions. Vertices are defined
by mathlib extreme points; attained gradients are continuous linear dot products. -/
noncomputable section
namespace Thesis.Tropical
open Finset Matrix Filter
open scoped Topology
variable {I A : Type} [Fintype I] [Fintype A] [Nonempty A]

/-- The linear differential represented by a gradient vector. -/
def gradientRow (p : I → ℝ) : (I → ℝ) →L[ℝ] ℝ := (dotLinear p).toContinuousLinearMap

theorem gradientRow_apply (p y : I → ℝ) : gradientRow p y = p ⬝ᵥ y :=
  dotProduct_comm y p

theorem gradientRow_injective : Function.Injective (gradientRow (I := I)) := by
  classical
  intro p q h
  funext i
  have he := congrArg (fun D : (I → ℝ) →L[ℝ] ℝ => D (Pi.single i 1)) h
  simpa only [gradientRow_apply,dotProduct_single_one] using he

/-- Every maximizing point must equal the actual differential, by Fermat's theorem
applied to support minus the supporting linear function. -/
theorem maximizing_point_derivative (v : A → I → ℝ) (x p : I → ℝ)
    (hp : p ∈ convexHull ℝ (Set.range v))
    (he : p ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x)
    (D : (I → ℝ) →L[ℝ] ℝ)
    (hd : HasFDerivAt (support (convexHull ℝ (Set.range v))) D x) : D = gradientRow p := by
  have hm : IsLocalMin (fun y => support (convexHull ℝ (Set.range v)) y-gradientRow p y) x := by
    apply Filter.Eventually.of_forall
    intro y
    simp only [gradientRow_apply]
    have hy := dot_le_support_hull v hp y
    linarith
  exact sub_eq_zero.mp (hm.hasFDerivAt_eq_zero (hd.sub (gradientRow p).hasFDerivAt))

/-- A finite strict gap to every different generator persists on a neighborhood,
where the support function is exactly its unique maximizing linear form. -/
theorem unique_generator_hasFDerivAt (v : A → I → ℝ) (x p : I → ℝ)
    (hp : ∃ a, v a = p) (hgap : ∀ a, v a ≠ p → v a ⬝ᵥ x < p ⬝ᵥ x) :
    HasFDerivAt (support (convexHull ℝ (Set.range v))) (gradientRow p) x := by
  have heach : ∀ a, ∀ᶠ y in 𝓝 x, v a ⬝ᵥ y ≤ p ⬝ᵥ y := by
    intro a
    by_cases he : v a = p
    · exact Filter.Eventually.of_forall fun y => by rw [he]
    · have hc := ((gradientRow (v a)).continuous.continuousAt).eventually_lt
        ((gradientRow p).continuous.continuousAt) (by simpa only [gradientRow_apply] using hgap a he)
      exact hc.mono fun y hy => by simpa only [gradientRow_apply] using hy.le
  have hall : ∀ᶠ y in 𝓝 x, ∀ a, v a ⬝ᵥ y ≤ p ⬝ᵥ y := Filter.eventually_all.mpr heach
  apply (gradientRow p).hasFDerivAt.congr_of_eventuallyEq
  filter_upwards [hall] with y hy
  rw [gradientRow_apply,support_convexHull]
  apply le_antisymm
  · exact finiteMax_le _ _ (hy)
  · obtain ⟨a,rfl⟩ := hp
    exact le_finiteMax (fun a => v a ⬝ᵥ y) a

/-- A unique maximizing point of a convex hull is an extreme point. -/
theorem unique_face_extreme (v : A → I → ℝ) (x p : I → ℝ)
    (hp : p ∈ convexHull ℝ (Set.range v))
    (he : p ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x)
    (huniq : ∀ q ∈ convexHull ℝ (Set.range v),
      q ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x → q = p) :
    p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ := by
  refine ⟨hp,?_⟩
  intro u hu w hw hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  apply huniq u hu
  have hu' := dot_le_support_hull v hu x
  have hw' := dot_le_support_hull v hw x
  have hdot := congrArg (fun y => y ⬝ᵥ x) heq
  simp only [add_dotProduct,smul_dotProduct,smul_eq_mul] at hdot
  rw [he] at hdot
  have hweighted : a*(support (convexHull ℝ (Set.range v)) x-u ⬝ᵥ x) +
      b*(support (convexHull ℝ (Set.range v)) x-w ⬝ᵥ x) = 0 := by
    calc
      _ = (a+b)*support (convexHull ℝ (Set.range v)) x-
          (a*(u ⬝ᵥ x)+b*(w ⬝ᵥ x)) := by ring
      _ = 0 := by rw [hab,one_mul,hdot,sub_self]
  have hterm := mul_nonneg hb.le (sub_nonneg.mpr hw')
  have : support (convexHull ℝ (Set.range v)) x-u ⬝ᵥ x = 0 := by nlinarith
  linarith

/-- Every vertex is strictly exposed among the finitely many different generators.
The strict separator is constructed from the convex hull of all other generators. -/
theorem extreme_exposing_direction (v : A → I → ℝ) (p : I → ℝ)
    (hp : p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ) :
    ∃ x, ∀ a, v a ≠ p → v a ⬝ᵥ x < p ⬝ᵥ x := by
  let rest : Set (I → ℝ) := Set.range v \ {p}
  have hnot : p ∉ convexHull ℝ rest := by
    have he := ((convex_convexHull ℝ (Set.range v)).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff).mp hp
    intro h
    apply he.2
    have hs : rest ⊆ convexHull ℝ (Set.range v) \ {p} :=
      fun q hq => ⟨subset_convexHull ℝ _ hq.1,hq.2⟩
    exact convexHull_mono hs h
  have hclosed : IsClosed (convexHull ℝ rest) :=
    (Set.Finite.sdiff (Set.finite_range v)).isClosed_convexHull ℝ
  obtain ⟨f,c,hf,hp'⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ rest) hclosed hnot
  obtain ⟨x,hx⟩ := linear_eq_dot f.toLinearMap
  refine ⟨x,?_⟩
  intro a ha
  have hr : v a ∈ rest := ⟨⟨a,rfl⟩,ha⟩
  have hlt := (hf (v a) (subset_convexHull ℝ rest hr)).trans hp'
  have h1 := hx (v a)
  have h2 := hx p
  change f (v a) = _ at h1
  change f p = _ at h2
  rwa [h1,h2] at hlt

/-- thm:vertices_gradients: extreme points are exactly the gradient vectors
attained at points with an actual Fréchet derivative. No gate mask is substituted
for differentiability, and no generic-position assumption is made. -/
theorem vertices_eq_attainable_gradients (v : A → I → ℝ) (p : I → ℝ) :
    p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ ↔
      ∃ x, HasFDerivAt (support (convexHull ℝ (Set.range v))) (gradientRow p) x := by
  constructor
  · intro hp
    obtain ⟨x,hx⟩ := extreme_exposing_direction v p hp
    have hgen : p ∈ Set.range v := extremePoints_convexHull_subset hp
    exact ⟨x,unique_generator_hasFDerivAt v x p hgen hx⟩
  · rintro ⟨x,hd⟩
    obtain ⟨a,ha⟩ := finiteMax_attained (fun a => v a ⬝ᵥ x)
    have ha' : v a ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x := by rw [support_convexHull,ha]
    have hamem := subset_convexHull ℝ (Set.range v) (Set.mem_range_self a)
    have he := maximizing_point_derivative v x (v a) hamem ha' (gradientRow p) hd
    have hp : p = v a := gradientRow_injective he
    have hpmem : p ∈ convexHull ℝ (Set.range v) := by rw [hp]; exact hamem
    have hpe : p ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x := by rw [hp]; exact ha'
    apply unique_face_extreme v x p hpmem hpe
    intro q hq heq
    have hD := maximizing_point_derivative v x q hq heq (gradientRow p) hd
    exact (gradientRow_injective hD).symm

/-- Full differentiability/singleton-face equivalence from prop:subdifferential_face. -/
theorem support_differentiable_iff_singleton_face (v : A → I → ℝ) (x : I → ℝ) :
    DifferentiableAt ℝ (support (convexHull ℝ (Set.range v))) x ↔
      ∃ p, p ∈ convexHull ℝ (Set.range v) ∧
        p ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x ∧
        ∀ q ∈ convexHull ℝ (Set.range v),
          q ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x → q = p := by
  constructor
  · intro hd
    obtain ⟨a,ha⟩ := finiteMax_attained (fun a => v a ⬝ᵥ x)
    have hamem := subset_convexHull ℝ (Set.range v) (Set.mem_range_self a)
    have he : v a ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x := by rw [support_convexHull,ha]
    have hD := maximizing_point_derivative v x (v a) hamem he _ hd.hasFDerivAt
    refine ⟨v a,hamem,he,?_⟩
    intro q hq hq'
    have hD' := maximizing_point_derivative v x q hq hq' _ hd.hasFDerivAt
    exact gradientRow_injective (hD'.symm.trans hD)
  · rintro ⟨p,hp,he,huniq⟩
    have hex : ∃ a, v a = p := by
      obtain ⟨a,ha⟩ := finiteMax_attained (fun a => v a ⬝ᵥ x)
      refine ⟨a,huniq _ (subset_convexHull ℝ _ (Set.mem_range_self a)) ?_⟩
      rw [support_convexHull,ha]
    apply (unique_generator_hasFDerivAt v x p hex ?_).differentiableAt
    intro a hne
    have hle := dot_le_support_hull v (subset_convexHull ℝ _ (Set.mem_range_self a)) x
    rw [← he] at hle
    apply lt_of_le_of_ne hle
    intro heq
    apply hne
    exact huniq _ (subset_convexHull ℝ _ (Set.mem_range_self a)) (heq.trans he)

end Thesis.Tropical
