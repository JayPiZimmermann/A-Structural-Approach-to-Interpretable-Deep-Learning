import Thesis.PiecewiseLinear
import Thesis.CompactSupport
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Analysis.Convex.Extrema

/-! The converse representation bridge for convex CPWL functions.  CPWL retains
its independent continuous finite-polyhedral-cover definition. -/
noncomputable section
namespace Thesis.PiecewiseLinear
open Finset Matrix Thesis.Tropical
open scoped Topology
variable {I O : Type} [Fintype I]

/-- A piece on a cell with nonempty interior is a global affine minorant of a
convex function. Local equality is promoted using convex local-to-global minima. -/
theorem AffineCover.piece_le {f : (I → ℝ) → O → ℝ} (C : AffineCover f)
    (i : O) (hc : ConvexOn ℝ Set.univ (fun x => f x i)) (a : C.Pieces)
    (ha : (interior (C.cell a).carrier).Nonempty) (y : I → ℝ) :
    C.slope a i ⬝ᵥ y+C.bias a i ≤ f y i := by
  obtain ⟨x,hx⟩ := ha
  let g := fun z => f z i-(C.slope a i ⬝ᵥ z+C.bias a i)
  have hx' : g x=0 := by
    dsimp [g]
    rw [C.affine_on a x (interior_subset hx) i,sub_self]
  have hlocal : IsLocalMin g x := by
    have hn : ∀ᶠ z in 𝓝 x, z ∈ interior (C.cell a).carrier := isOpen_interior.mem_nhds hx
    filter_upwards [hn] with z hz
    change g x ≤ g z
    rw [hx']
    dsimp [g]
    rw [C.affine_on a z (interior_subset hz) i,sub_self]
  have hconv : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ,?_⟩
    intro u hu v hv r t hr ht hrt
    have h := hc.2 hu hv hr ht hrt
    dsimp [g]
    simp only [dotProduct_add,dotProduct_smul,smul_eq_mul] at *
    calc
      f (r • u+t • v) i-(r*(C.slope a i ⬝ᵥ u)+t*(C.slope a i ⬝ᵥ v)+C.bias a i) ≤
          r*f u i+t*f v i-(r*(C.slope a i ⬝ᵥ u)+t*(C.slope a i ⬝ᵥ v)+C.bias a i) :=
        sub_le_sub_right h _
      _ = r*(f u i-(C.slope a i ⬝ᵥ u+C.bias a i))+
          t*(f v i-(C.slope a i ⬝ᵥ v+C.bias a i)) := by
        nlinarith [congrArg (fun z : ℝ => z*C.bias a i) hrt]
  have hm := IsMinOn.of_isLocalMin_of_convex_univ hlocal hconv y
  rw [hx'] at hm
  dsimp [g] at hm
  linarith

/-- Convex continuous piecewise affine functions are genuine finite max-affine
polynomials. Empty-interior cells are eliminated using density of the interiors
of a finite closed cover, rather than by assuming a max representation. -/
theorem convex_cpwl_representation {f : (I → ℝ) → O → ℝ} (hf : CPWL f)
    (i : O) (hc : ConvexOn ℝ Set.univ (fun x => f x i)) :
    ∃ p : Polynomial I, ∀ x, f x i=p.eval x := by
  classical
  obtain ⟨hcont,⟨C⟩⟩ := hf
  have hcover : (⋃ a, (C.cell a).carrier)=Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a,ha⟩ := C.covers x
    exact Set.mem_iUnion.mpr ⟨a,ha⟩
  have hdense := dense_iUnion_interior_of_closed (fun a => (C.cell a).closed) hcover
  let T := {a : C.Pieces // (interior (C.cell a).carrier).Nonempty}
  have hn : Nonempty T := by
    obtain ⟨a,ha⟩ := nonempty_interior_of_iUnion_of_closed (fun a => (C.cell a).closed) hcover
    exact ⟨⟨a,ha⟩⟩
  let : Nonempty T := hn
  let p : Polynomial I :=
    { Terms := T
      finite := inferInstance
      inhabited := inferInstance
      slope := fun a => C.slope a.val i
      intercept := fun a => C.bias a.val i }
  refine ⟨p,?_⟩
  have he : (fun x => f x i)=p.eval := by
    apply Continuous.ext_on hdense (continuous_apply i |>.comp hcont) (polynomial_continuous p)
    intro x hx
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
    apply le_antisymm
    · have hm := le_finiteMax (fun b : T => C.slope b.val i ⬝ᵥ x+C.bias b.val i)
        ⟨a,⟨x,ha⟩⟩
      change f x i ≤ p.eval x
      rw [C.affine_on a x (interior_subset ha) i]
      exact hm
    · exact finiteMax_le _ _ (fun b => C.piece_le i hc b.val b.property x)
  exact congrFun he

/-- The max-affine characterization at the source observation's exact scalar
scope, with both directions proved for the independent CPWL definition. -/
theorem convex_cpwl_iff_max_affine (u : (I → ℝ) → ℝ) :
    (CPWL (fun x (_ : Unit) => u x) ∧ ConvexOn ℝ Set.univ u) ↔
      ∃ p : Polynomial I, u=p.eval := by
  constructor
  · rintro ⟨hp,hc⟩
    obtain ⟨p,he⟩ := convex_cpwl_representation hp () hc
    exact ⟨p,funext he⟩
  · rintro ⟨p,rfl⟩
    refine ⟨?_,p.convex⟩
    have h := polynomial_difference_cpwl (fun _ : Unit => p)
      (fun _ : Unit => Thesis.Tropical.Polynomial.monomial (0 : I → ℝ) 0)
    simpa only [Thesis.Tropical.Polynomial.eval_monomial,zero_dotProduct,zero_add,sub_zero] using h

/-- Homogeneity removes all intercepts from a max-affine representation. This
argument is global: every listed slope is bounded by scaling the original function. -/
theorem homogeneous_polynomial_eq_support (p : Polynomial I)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ x, p.eval (c • x)=c*p.eval x) :
    ∀ x, p.eval x=support p.newton x := by
  have hz : p.eval 0=0 := by
    have h := hh 0 le_rfl 0
    simpa using h
  have hb : ∀ a, p.intercept a ≤ 0 := by
    intro a
    have h := le_finiteMax (fun a => p.slope a ⬝ᵥ (0 : I → ℝ)+p.intercept a) a
    change _ ≤ p.eval 0 at h
    simpa [hz] using h
  have hs : ∀ a x, p.slope a ⬝ᵥ x ≤ p.eval x := by
    intro a x
    by_contra h
    have hdiff : 0 < p.slope a ⬝ᵥ x-p.eval x := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨n,hn⟩ := exists_lt_nsmul hdiff (-p.intercept a)
    have hm := le_finiteMax (fun a => p.slope a ⬝ᵥ ((n : ℝ) • x)+p.intercept a) a
    change _ ≤ p.eval ((n : ℝ) • x) at hm
    rw [hh n (Nat.cast_nonneg n),dotProduct_smul] at hm
    simp only [smul_eq_mul] at hm
    simp only [nsmul_eq_mul] at hn
    nlinarith
  intro x
  rw [Polynomial.newton,support_convexHull]
  apply le_antisymm
  · exact finiteMax_le _ _ fun a =>
      (add_le_of_nonpos_right (hb a)).trans (le_finiteMax (fun a => p.slope a ⬝ᵥ x) a)
  · exact finiteMax_le _ _ fun a => hs a x

/-- Every convex homogeneous CPWL function has a finite-polytope support
representation, derived from its actual polyhedral cover. -/
theorem homogeneous_convex_cpwl_support (u : (I → ℝ) → ℝ)
    (hp : CPWL (fun x (_ : Unit) => u x)) (hc : ConvexOn ℝ Set.univ u)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ x, u (c • x)=c*u x) :
    ∃ p : Polynomial I, u=support p.newton := by
  obtain ⟨p,he⟩ := convex_cpwl_representation hp () hc
  have hrep : u=p.eval := funext he
  refine ⟨p,?_⟩
  rw [hrep]
  exact funext (homogeneous_polynomial_eq_support p (by simpa only [← hrep] using hh))

/-- Nonempty finite convex hulls, with no support-representability built into the
primitive CPWL property. -/
def IsPolytope (P : Set (I → ℝ)) : Prop := ∃ p : Polynomial I, p.newton=P

/-- The representing nonempty finite polytope is unique. The proof uses the
stronger compact-convex support uniqueness theorem. -/
theorem homogeneous_convex_cpwl_unique_polytope (u : (I → ℝ) → ℝ)
    (hp : CPWL (fun x (_ : Unit) => u x)) (hc : ConvexOn ℝ Set.univ u)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ x, u (c • x)=c*u x) :
    ∃! P : Set (I → ℝ), IsPolytope P ∧ u=support P := by
  obtain ⟨p,he⟩ := homogeneous_convex_cpwl_support u hp hc hh
  refine ⟨p.newton,⟨⟨p,rfl⟩,he⟩,?_⟩
  rintro Q ⟨⟨q,rfl⟩,hq⟩
  exact compact_eq_of_support_eq ((Set.finite_range q.slope).isCompact_convexHull ℝ)
    (Set.range_nonempty q.slope).convexHull (convex_convexHull ℝ _)
    ((Set.finite_range p.slope).isCompact_convexHull ℝ)
    (Set.range_nonempty p.slope).convexHull (convex_convexHull ℝ _)
    (hq.symm.trans he)

/-- The arbitrary-function vertex theorem, including the formerly missing
CPWL-to-polytope bridge and actual Fréchet derivatives. -/
theorem homogeneous_convex_cpwl_vertices (u : (I → ℝ) → ℝ)
    (hp : CPWL (fun x (_ : Unit) => u x)) (hc : ConvexOn ℝ Set.univ u)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ x, u (c • x)=c*u x) :
    ∃ P : Set (I → ℝ), IsPolytope P ∧ u=support P ∧
      (∀ Q, IsPolytope Q → u=support Q → Q=P) ∧
      ∀ s, s ∈ P.extremePoints ℝ ↔ ∃ x, HasFDerivAt u (gradientRow s) x := by
  obtain ⟨P,⟨⟨p,hpP⟩,he⟩,huniq⟩ := homogeneous_convex_cpwl_unique_polytope u hp hc hh
  refine ⟨P,⟨p,hpP⟩,he,fun Q hQ heQ => huniq Q ⟨hQ,heQ⟩,?_⟩
  intro s
  rw [he,← hpP]
  exact vertices_eq_attainable_gradients p.slope s

end Thesis.PiecewiseLinear
