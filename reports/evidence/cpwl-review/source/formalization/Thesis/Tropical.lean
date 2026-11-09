import Thesis.Foundations
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Fintype.Sum

/-! Finite max-affine polynomials with explicit monomials, actual convex-hull
Newton polytopes, and support functions defined as suprema over those sets. -/
noncomputable section
namespace Thesis.Tropical
open Finset Matrix
open scoped Pointwise

variable {I J : Type} [Fintype I] [Fintype J]

def finiteMax {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) : ℝ :=
  univ.sup' univ_nonempty f

theorem finiteMax_attained {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) :
    ∃ a, finiteMax f = f a := by
  obtain ⟨a,_,ha⟩ := univ.exists_mem_eq_sup' univ_nonempty f
  exact ⟨a,ha⟩

theorem le_finiteMax {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) (a : A) :
    f a ≤ finiteMax f := univ.le_sup' f (mem_univ a)

theorem finiteMax_le {A : Type} [Fintype A] [Nonempty A] (f : A → ℝ) (b : ℝ)
    (h : ∀ a, f a ≤ b) : finiteMax f ≤ b :=
  (univ.sup'_le_iff univ_nonempty f).mpr (fun a _ => h a)

/-- Terms are explicitly indexed; repeated exponents cause no difficulty. -/
structure Polynomial (I : Type) where
  Terms : Type
  finite : Fintype Terms
  inhabited : Nonempty Terms
  slope : Terms → I → ℝ
  intercept : Terms → ℝ
attribute [instance] Polynomial.finite Polynomial.inhabited

def Polynomial.eval (p : Polynomial I) (x : I → ℝ) : ℝ :=
  finiteMax (fun a => p.slope a ⬝ᵥ x + p.intercept a)

def Polynomial.newton (p : Polynomial I) : Set (I → ℝ) := convexHull ℝ (Set.range p.slope)

def Polynomial.max (p q : Polynomial I) : Polynomial I where
  Terms := p.Terms ⊕ q.Terms
  finite := inferInstance
  inhabited := inferInstance
  slope := Sum.elim p.slope q.slope
  intercept := Sum.elim p.intercept q.intercept

def Polynomial.add (p q : Polynomial I) : Polynomial I where
  Terms := p.Terms × q.Terms
  finite := inferInstance
  inhabited := inferInstance
  slope := fun a => p.slope a.1 + q.slope a.2
  intercept := fun a => p.intercept a.1 + q.intercept a.2

def Polynomial.scale (c : ℝ) (p : Polynomial I) : Polynomial I where
  Terms := p.Terms
  finite := inferInstance
  inhabited := inferInstance
  slope := fun a => c • p.slope a
  intercept := fun a => c * p.intercept a

def Polynomial.monomial (v : I → ℝ) (b : ℝ) : Polynomial I where
  Terms := Unit
  finite := inferInstance
  inhabited := inferInstance
  slope := fun _ => v
  intercept := fun _ => b

theorem Polynomial.eval_monomial (v : I → ℝ) (b : ℝ) (x : I → ℝ) :
    (Polynomial.monomial v b).eval x = v ⬝ᵥ x+b := by simp [Polynomial.eval,finiteMax,monomial]

theorem Polynomial.eval_max (p q : Polynomial I) (x : I → ℝ) :
    (p.max q).eval x = Max.max (p.eval x) (q.eval x) := by
  apply le_antisymm
  · apply finiteMax_le
    intro a
    cases a with
    | inl a => exact (le_finiteMax (fun a => p.slope a ⬝ᵥ x+p.intercept a) a).trans (le_max_left _ _)
    | inr a => exact (le_finiteMax (fun a => q.slope a ⬝ᵥ x+q.intercept a) a).trans (le_max_right _ _)
  · apply max_le
    · apply finiteMax_le
      intro a
      exact le_finiteMax (fun b => (p.max q).slope b ⬝ᵥ x+(p.max q).intercept b) (Sum.inl a)
    · apply finiteMax_le
      intro a
      exact le_finiteMax (fun b => (p.max q).slope b ⬝ᵥ x+(p.max q).intercept b) (Sum.inr a)

theorem Polynomial.eval_add (p q : Polynomial I) (x : I → ℝ) :
    (p.add q).eval x = p.eval x + q.eval x := by
  have hterm : ∀ a : (p.add q).Terms,
      (p.add q).slope a ⬝ᵥ x + (p.add q).intercept a =
      (p.slope a.1 ⬝ᵥ x+p.intercept a.1)+(q.slope a.2 ⬝ᵥ x+q.intercept a.2) := by
    intro a
    simp only [add, add_dotProduct]
    ring
  apply le_antisymm
  · apply finiteMax_le
    intro a
    rw [hterm]
    exact add_le_add (le_finiteMax (fun a => p.slope a ⬝ᵥ x+p.intercept a) a.1) (le_finiteMax (fun a => q.slope a ⬝ᵥ x+q.intercept a) a.2)
  · obtain ⟨a,ha⟩ := finiteMax_attained (fun a => p.slope a ⬝ᵥ x+p.intercept a)
    obtain ⟨b,hb⟩ := finiteMax_attained (fun b => q.slope b ⬝ᵥ x+q.intercept b)
    change finiteMax _ + finiteMax _ ≤ _
    rw [ha,hb]
    have := le_finiteMax (fun c => (p.add q).slope c ⬝ᵥ x+(p.add q).intercept c) (a,b)
    rwa [hterm (a,b)] at this

theorem Polynomial.eval_scale (p : Polynomial I) (c : ℝ) (hc : 0 ≤ c) (x : I → ℝ) :
    (p.scale c).eval x = c*p.eval x := by
  have hterm : ∀ a, (p.scale c).slope a ⬝ᵥ x+(p.scale c).intercept a =
      c * (p.slope a ⬝ᵥ x+p.intercept a) := by
    intro a; simp [scale,smul_dotProduct,mul_add]
  apply le_antisymm
  · apply finiteMax_le
    intro a
    rw [hterm]
    exact mul_le_mul_of_nonneg_left (le_finiteMax (fun a => p.slope a ⬝ᵥ x+p.intercept a) a) hc
  · obtain ⟨a,ha⟩ := finiteMax_attained (fun a => p.slope a ⬝ᵥ x+p.intercept a)
    change c*finiteMax _ ≤ _
    rw [ha]
    have := le_finiteMax (fun a => (p.scale c).slope a ⬝ᵥ x+(p.scale c).intercept a) a
    rwa [hterm a] at this

/-- Newton tropical sum is the convex hull of the union, for actual convex sets. -/
theorem Polynomial.newton_max (p q : Polynomial I) :
    (p.max q).newton = convexHull ℝ (p.newton ∪ q.newton) := by
  have hr : Set.range (p.max q).slope = Set.range p.slope ∪ Set.range q.slope := by
    ext v
    constructor
    · rintro ⟨a,rfl⟩
      cases a with
      | inl a => exact Or.inl ⟨a,rfl⟩
      | inr a => exact Or.inr ⟨a,rfl⟩
    · rintro (⟨a,rfl⟩ | ⟨a,rfl⟩)
      · exact ⟨Sum.inl a,rfl⟩
      · exact ⟨Sum.inr a,rfl⟩
  simp only [newton,hr,convexHull_convexHull_union_left,convexHull_convexHull_union_right]

/-- Newton tropical product is the Minkowski sum. -/
theorem Polynomial.newton_add (p q : Polynomial I) :
    (p.add q).newton = p.newton + q.newton := by
  have hr : Set.range (p.add q).slope = Set.range p.slope + Set.range q.slope := by
    ext v
    constructor
    · rintro ⟨⟨a,b⟩,rfl⟩
      exact ⟨p.slope a,⟨a,rfl⟩,q.slope b,⟨b,rfl⟩,rfl⟩
    · rintro ⟨u,⟨a,rfl⟩,v,⟨b,rfl⟩,rfl⟩
      exact ⟨(a,b),rfl⟩
  rw [newton,hr,convexHull_add]
  rfl

/-- Dot product against a fixed vector is a linear functional. -/
def dotLinear (x : I → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun p => p ⬝ᵥ x
  map_add' := fun _ _ => add_dotProduct _ _ _
  map_smul' := fun _ _ => smul_dotProduct _ _ _

/-- Actual support function of a set, as a supremum of linear objectives. -/
def support (P : Set (I → ℝ)) (x : I → ℝ) : ℝ := sSup ((fun p => p ⬝ᵥ x) '' P)

/-- A linear objective over a finite convex hull attains precisely the same maximum
as over its listed generators. This proves the finite-polytope support formula. -/
theorem support_convexHull {A : Type} [Fintype A] [Nonempty A]
    (v : A → I → ℝ) (x : I → ℝ) :
    support (convexHull ℝ (Set.range v)) x = finiteMax (fun a => v a ⬝ᵥ x) := by
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨a,ha⟩ := finiteMax_attained (fun a => v a ⬝ᵥ x)
    exact ⟨v a,subset_convexHull ℝ _ ⟨a,rfl⟩,ha.symm⟩
  · rintro z ⟨p,hp,rfl⟩
    have hsub : convexHull ℝ (Set.range v) ⊆
        {p | p ⬝ᵥ x ≤ finiteMax (fun a => v a ⬝ᵥ x)} := by
      apply convexHull_min
      · rintro _ ⟨a,rfl⟩; exact le_finiteMax (fun a => v a ⬝ᵥ x) a
      · exact (convex_Iic _).linear_preimage (dotLinear x)
    exact hsub hp

/-- Zero-coefficient tropical polynomials are support functions of their Newton polytopes. -/
theorem Polynomial.eval_eq_support (p : Polynomial I) (h : ∀ a, p.intercept a = 0)
    (x : I → ℝ) : p.eval x = support p.newton x := by
  rw [newton,support_convexHull]
  simp only [eval,h,add_zero]

/-- Homogenization retains every intercept as an additional coordinate. -/
def Polynomial.lift (p : Polynomial I) : Polynomial (I ⊕ Unit) where
  Terms := p.Terms
  finite := inferInstance
  inhabited := inferInstance
  slope := fun a => Sum.elim (p.slope a) (fun _ => p.intercept a)
  intercept := fun _ => 0

/-- eq:lifted_support, with the actual lifted convex hull and affine slice (x,1). -/
theorem Polynomial.lifted_support (p : Polynomial I) (x : I → ℝ) :
    p.eval x = support p.lift.newton (Sum.elim x (fun _ => 1)) := by
  rw [← p.lift.eval_eq_support (fun _ => rfl)]
  simp [eval,lift,dotProduct,Fintype.sum_sum_type]

/-- Maxout convexity for arbitrary signed slopes and biases. -/
theorem Polynomial.convex (p : Polynomial I) : ConvexOn ℝ Set.univ p.eval := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  apply finiteMax_le
  intro t
  have h : p.slope t ⬝ᵥ (a • x+b • y)+p.intercept t =
      a*(p.slope t ⬝ᵥ x+p.intercept t)+b*(p.slope t ⬝ᵥ y+p.intercept t) := by
    simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]
    rw [show b = 1-a by linarith]
    ring
  rw [h]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_finiteMax (fun t => p.slope t ⬝ᵥ x+p.intercept t) t) ha)
    (mul_le_mul_of_nonneg_left (le_finiteMax (fun t => p.slope t ⬝ᵥ y+p.intercept t) t) hb)

/-- Nonnegative slopes make the polynomial coordinatewise monotone. -/
theorem Polynomial.monotone (p : Polynomial I) (h : ∀ a i, 0 ≤ p.slope a i) :
    Monotone p.eval := by
  intro x y hxy
  apply finiteMax_le
  intro a
  apply le_trans _ (le_finiteMax _ a)
  apply add_le_add _ le_rfl
  exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxy i) (h a i)

/-- cor:polytopes_nonneg: the entire Newton convex hull, not only the generators,
lies in the nonnegative orthant whenever its exponents do. -/
theorem Polynomial.newton_nonnegative (p : Polynomial I) (h : ∀ a i, 0 ≤ p.slope a i) :
    ∀ v ∈ p.newton, ∀ i, 0 ≤ v i := by
  have hc : Convex ℝ {v : I → ℝ | ∀ i, 0 ≤ v i} := by
    intro x hx y hy a b ha hb _ i
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  have hs : Set.range p.slope ⊆ {v : I → ℝ | ∀ i, 0 ≤ v i} := by
    rintro _ ⟨a,rfl⟩; exact h a
  exact convexHull_min hs hc

end Thesis.Tropical
