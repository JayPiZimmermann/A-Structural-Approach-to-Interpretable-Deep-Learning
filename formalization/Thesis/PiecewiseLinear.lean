import Thesis.TropicalNetwork
import Thesis.SupportDerivatives
import Mathlib.Topology.Order.Lattice

/-! Conventional finite-polyhedral continuous piecewise affine functions.
A cell is a finite intersection of closed affine halfspaces; the cover is explicit.
This module proves the network-to-CPWL direction without changing the CPWL definition
into a neural-network or difference-of-maxima representation. -/
noncomputable section
namespace Thesis.PiecewiseLinear
open Finset Matrix HiddenMonotonicity Thesis.Tropical
variable {I O : Type} [Fintype I] [Fintype O]

structure Polyhedron (I : Type) where
  Constraints : Type
  finite : Fintype Constraints
  normal : Constraints → I → ℝ
  bound : Constraints → ℝ
attribute [instance] Polyhedron.finite

def Polyhedron.carrier (P : Polyhedron I) : Set (I → ℝ) :=
  {x | ∀ i, P.normal i ⬝ᵥ x ≤ P.bound i}

theorem Polyhedron.closed (P : Polyhedron I) : IsClosed P.carrier := by
  have he : P.carrier = ⋂ i, {x | P.normal i ⬝ᵥ x ≤ P.bound i} := by ext x; simp [carrier]
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_le _ continuous_const
  have he : (fun x => P.normal i ⬝ᵥ x) = gradientRow (P.normal i) :=
    funext fun x => (gradientRow_apply _ _).symm
  change Continuous (fun x => P.normal i ⬝ᵥ x)
  rw [he]
  exact (gradientRow (P.normal i)).continuous

theorem Polyhedron.convex (P : Polyhedron I) : Convex ℝ P.carrier := by
  intro x hx y hy a b ha hb hab i
  simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]
  calc
    a*(P.normal i ⬝ᵥ x)+b*(P.normal i ⬝ᵥ y) ≤ a*P.bound i+b*P.bound i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = P.bound i := by rw [← add_mul,hab,one_mul]

/-- A finite closed-polyhedral cover with affine maps on each cell. -/
structure AffineCover (f : (I → ℝ) → (O → ℝ)) where
  Pieces : Type
  finite : Fintype Pieces
  cell : Pieces → Polyhedron I
  slope : Pieces → O → I → ℝ
  bias : Pieces → O → ℝ
  covers : ∀ x, ∃ a, x ∈ (cell a).carrier
  affine_on : ∀ a x, x ∈ (cell a).carrier → ∀ i, f x i = slope a i ⬝ᵥ x+bias a i
attribute [instance] AffineCover.finite

/-- This is the standard definition: continuity and an actual finite polyhedral affine cover. -/
def CPWL (f : (I → ℝ) → (O → ℝ)) : Prop := Continuous f ∧ Nonempty (AffineCover f)

theorem polynomial_continuous (p : Polynomial I) : Continuous p.eval := by
  apply Continuous.finset_sup'_apply univ_nonempty
  intro a _
  have hc : Continuous (fun x => p.slope a ⬝ᵥ x) := by
    have he : (fun x => p.slope a ⬝ᵥ x) = gradientRow (p.slope a) :=
      funext fun x => (gradientRow_apply _ _).symm
    rw [he]
    exact (gradientRow (p.slope a)).continuous
  exact hc.add continuous_const

def differenceCell (g h : O → Polynomial I)
    (choice : (i : O) → (g i).Terms × (h i).Terms) : Polyhedron I where
  Constraints := (i : O) × ((g i).Terms ⊕ (h i).Terms)
  finite := by classical exact inferInstance
  normal := fun c => match c.2 with
    | Sum.inl a => (g c.1).slope a-(g c.1).slope (choice c.1).1
    | Sum.inr a => (h c.1).slope a-(h c.1).slope (choice c.1).2
  bound := fun c => match c.2 with
    | Sum.inl a => (g c.1).intercept (choice c.1).1-(g c.1).intercept a
    | Sum.inr a => (h c.1).intercept (choice c.1).2-(h c.1).intercept a

theorem differenceCell_cover (g h : O → Polynomial I) (x : I → ℝ) :
    ∃ choice : (i : O) → (g i).Terms × (h i).Terms, x ∈ (differenceCell g h choice).carrier := by
  let chosenG : (i : O) → (g i).Terms := fun i => Classical.choose
    (finiteMax_attained (fun a => (g i).slope a ⬝ᵥ x+(g i).intercept a))
  let chosenH : (i : O) → (h i).Terms := fun i => Classical.choose
    (finiteMax_attained (fun a => (h i).slope a ⬝ᵥ x+(h i).intercept a))
  refine ⟨fun i => (chosenG i,chosenH i),?_⟩
  intro c
  obtain ⟨i,a⟩ := c
  cases a with
  | inl a =>
      have hm := le_finiteMax (fun a => (g i).slope a ⬝ᵥ x+(g i).intercept a) a
      have he := Classical.choose_spec (finiteMax_attained (fun a => (g i).slope a ⬝ᵥ x+(g i).intercept a))
      change _ = (g i).slope (chosenG i) ⬝ᵥ x+(g i).intercept (chosenG i) at he
      change ((g i).slope a-(g i).slope (chosenG i)) ⬝ᵥ x ≤
        (g i).intercept (chosenG i)-(g i).intercept a
      rw [sub_dotProduct]
      linarith
  | inr a =>
      have hm := le_finiteMax (fun a => (h i).slope a ⬝ᵥ x+(h i).intercept a) a
      have he := Classical.choose_spec (finiteMax_attained (fun a => (h i).slope a ⬝ᵥ x+(h i).intercept a))
      change _ = (h i).slope (chosenH i) ⬝ᵥ x+(h i).intercept (chosenH i) at he
      change ((h i).slope a-(h i).slope (chosenH i)) ⬝ᵥ x ≤
        (h i).intercept (chosenH i)-(h i).intercept a
      rw [sub_dotProduct]
      linarith

theorem differenceCell_affine (g h : O → Polynomial I)
    (choice : (i : O) → (g i).Terms × (h i).Terms) (x : I → ℝ)
    (hx : x ∈ (differenceCell g h choice).carrier) (i : O) :
    (g i).eval x-(h i).eval x =
      ((g i).slope (choice i).1-(h i).slope (choice i).2) ⬝ᵥ x+
      ((g i).intercept (choice i).1-(h i).intercept (choice i).2) := by
  have hg : (g i).eval x = (g i).slope (choice i).1 ⬝ᵥ x+(g i).intercept (choice i).1 := by
    apply le_antisymm
    · apply finiteMax_le
      intro a
      have hc := hx ⟨i,Sum.inl a⟩
      change ((g i).slope a-(g i).slope (choice i).1) ⬝ᵥ x ≤
        (g i).intercept (choice i).1-(g i).intercept a at hc
      rw [sub_dotProduct] at hc
      linarith
    · exact le_finiteMax (fun a => (g i).slope a ⬝ᵥ x+(g i).intercept a) (choice i).1
  have hh : (h i).eval x = (h i).slope (choice i).2 ⬝ᵥ x+(h i).intercept (choice i).2 := by
    apply le_antisymm
    · apply finiteMax_le
      intro a
      have hc := hx ⟨i,Sum.inr a⟩
      change ((h i).slope a-(h i).slope (choice i).2) ⬝ᵥ x ≤
        (h i).intercept (choice i).2-(h i).intercept a at hc
      rw [sub_dotProduct] at hc
      linarith
    · exact le_finiteMax (fun a => (h i).slope a ⬝ᵥ x+(h i).intercept a) (choice i).2
  rw [hg,hh,sub_dotProduct]
  ring

/-- Finite differences of max-affine polynomials are CPWL, using their actual
active-monomial polyhedral cells and a common cover for every output coordinate. -/
theorem polynomial_difference_cpwl (g h : O → Polynomial I) :
    CPWL (fun x i => (g i).eval x-(h i).eval x) := by
  refine ⟨continuous_pi (fun i => (polynomial_continuous (g i)).sub (polynomial_continuous (h i))),?_⟩
  refine ⟨{ Pieces := (i : O) → (g i).Terms × (h i).Terms
            finite := by classical exact inferInstance
            cell := differenceCell g h
            slope := fun choice i => (g i).slope (choice i).1-(h i).slope (choice i).2
            bias := fun choice i => (g i).intercept (choice i).1-(h i).intercept (choice i).2
            covers := differenceCell_cover g h
            affine_on := differenceCell_affine g h }⟩

/-- Restrict a polynomial on doubled inputs to the affine input embedding (x,0). -/
def restrictInput (p : Polynomial (I ⊕ I)) : Polynomial I where
  Terms := p.Terms
  finite := inferInstance
  inhabited := inferInstance
  slope := fun a i => p.slope a (Sum.inl i)
  intercept := p.intercept

theorem restrictInput_eval (p : Polynomial (I ⊕ I)) (x : I → ℝ) :
    (restrictInput p).eval x = p.eval (Sum.elim x 0) := by
  simp only [Thesis.Tropical.Polynomial.eval,restrictInput,dotProduct,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,mul_zero,sum_const_zero,add_zero]

/-- Canonicalize only the stored weight split, preserving every actual signed weight. -/
def canonicalize {n m} : Network n m → Network n m
  | .output n => .output n
  | .layer wp wn bp bn tail =>
      .layer (fun i j => max (wp i j-wn i j) 0) (fun i j => max (-(wp i j-wn i j)) 0)
        bp bn (canonicalize tail)

theorem canonicalize_nonnegative {n m} (net : Network n m) : (canonicalize net).Nonnegative := by
  induction net with
  | output n => trivial
  | layer wp wn bp bn tail ih => exact ⟨fun _ _ => le_max_right _ _,fun _ _ => le_max_right _ _,ih⟩

theorem canonicalize_eval {n m} (net : Network n m) : (canonicalize net).eval = net.eval := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [canonicalize,Network.eval,ih]
      funext x
      apply congrArg tail.eval
      funext i
      apply congrArg relu
      simp only [Matrix.mulVec,dotProduct,Pi.add_apply,Pi.sub_apply]
      congr 1
      apply sum_congr rfl
      intro j _
      change (max (wp i j-wn i j) 0-max (-(wp i j-wn i j)) 0)*x j =
        (wp i j-wn i j)*x j
      exact congrArg (fun z => z*x j) (canonical_weight_split (wp i j-wn i j)).1

/-- obs:relu_is_cpwl for arbitrary weights, biases, depth, and varying widths.
The conclusion uses a literal finite cover by closed polyhedra, not a substitute definition. -/
theorem network_cpwl {n m} (net : Network n m) : CPWL net.eval := by
  obtain ⟨g,h,_,he⟩ := network_tropical_representation (canonicalize net) (canonicalize_nonnegative net)
  have hf : net.eval = fun x i => (restrictInput (g i)).eval x-(restrictInput (h i)).eval x := by
    funext x i
    rw [restrictInput_eval,restrictInput_eval]
    have hh := (he x 0).2.2 i
    rw [canonicalize_eval] at hh
    simpa only [sub_zero] using hh.symm
  rw [hf]
  exact polynomial_difference_cpwl _ _

/-- Affine readouts are also covered, with arbitrary signed output weights and bias. -/
theorem affine_network_cpwl {n m k} (net : Network n m)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ) :
    CPWL (fun x => W.mulVec (net.eval x)+b) := by
  let wp : Matrix (Fin k) (Fin m) ℝ := fun i j => max (W i j) 0
  let wn : Matrix (Fin k) (Fin m) ℝ := fun i j => max (-(W i j)) 0
  have hw : wp-wn=W := by funext i j; exact (canonical_weight_split (W i j)).1
  obtain ⟨g,h,_,he⟩ := affine_network_tropical_representation (canonicalize net)
    (canonicalize_nonnegative net) wp wn b 0 (fun _ _ => le_max_right _ _) (fun _ _ => le_max_right _ _)
  have hf : (fun x => W.mulVec (net.eval x)+b) =
      fun x i => (restrictInput (g i)).eval x-(restrictInput (h i)).eval x := by
    funext x i
    rw [restrictInput_eval,restrictInput_eval]
    have hh := he x 0 i
    rw [canonicalize_eval,hw] at hh
    simpa only [sub_zero] using hh.symm
  rw [hf]
  exact polynomial_difference_cpwl _ _

end Thesis.PiecewiseLinear
