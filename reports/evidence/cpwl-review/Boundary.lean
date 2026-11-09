import Thesis.CPWLLattice
import Thesis.SignedMaxReduction

noncomputable section
open Set Filter Matrix Finset Thesis.Tropical Thesis.PiecewiseLinear
open Thesis.AffineMaxPartition Thesis.SignedMaxIdentities Thesis.SignedMaxReduction
open scoped Topology Classical

-- The primitive CPWL property has a genuine affine-cover hypothesis only.
example (f : (Unit → ℝ) → Unit → ℝ) :
    CPWL f ↔ Continuous f ∧ Nonempty (AffineCover f) := Iff.rfl

def cap (x : Unit → ℝ) : ℝ := 3-|x ()|

-- A direct closed-halfspace cover of a nonconvex function, without using any
-- max-affine or DC representation theorem to establish the hypothesis.
def capCell (positive : Bool) : Polyhedron Unit where
  Constraints := Unit
  finite := inferInstance
  normal := fun _ _ => if positive then -1 else 1
  bound := fun _ => 0

def capCover : AffineCover (fun x (_ : Unit) => cap x) where
  Pieces := Bool
  finite := inferInstance
  cell := capCell
  slope := fun positive _ _ => if positive then -1 else 1
  bias := fun _ _ => 3
  covers := by
    intro x
    by_cases hx : 0 ≤ x ()
    · refine ⟨true,?_⟩
      intro i
      simpa [capCell,dotProduct] using neg_nonpos.mpr hx
    · refine ⟨false,?_⟩
      intro i
      simpa [capCell,dotProduct] using (le_of_not_ge hx)
  affine_on := by
    intro a x hx i
    have h := hx ()
    cases a
    · have hn : x () ≤ 0 := by simpa [capCell,dotProduct] using h
      simp [cap,abs_of_nonpos hn,dotProduct]
      ring
    · have hp : 0 ≤ x () := by
        have hn : -x () ≤ 0 := by simpa [capCell,dotProduct] using h
        linarith
      simp [cap,abs_of_nonneg hp,dotProduct]
      ring

theorem cap_cpwl : CPWL (fun x (_ : Unit) => cap x) := by
  refine ⟨?_,⟨capCover⟩⟩
  apply continuous_pi
  intro i
  exact continuous_const.sub ((continuous_apply ()).abs)

example : ¬ ConvexOn ℝ univ cap := by
  intro hc
  have h := hc.2 (show (fun _ : Unit => (-1 : ℝ)) ∈ univ from trivial)
    (show (fun _ : Unit => (1 : ℝ)) ∈ univ from trivial)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ)+1/2=1 by norm_num)
  norm_num [cap,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h

example : ∃ g h : Thesis.Tropical.Polynomial Unit, ∀ x, cap x=g.eval x-h.eval x :=
  cpwl_polynomial_difference cap cap_cpwl

-- The two audited bridges compose directly for arbitrary CPWL f, with no
-- network representability premise and no hidden extra dimension.
example {I : Type} [Fintype I] (f : (I → ℝ) → ℝ)
    (hf : CPWL (fun x (_ : Unit) => f x)) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Thesis.Tropical.Polynomial I),
      (∀ j, Fintype.card (q j).Terms ≤ Fintype.card I+1) ∧
      ∀ x, f x=∑ j, c j*(q j).eval x := by
  obtain ⟨g,h,he⟩ := cpwl_polynomial_difference f hf
  obtain ⟨N,c,q,hcard,hrep⟩ := difference_signed_small_max g h
  exact ⟨N,c,q,hcard,fun x => (he x).trans (hrep x)⟩

-- Dimension zero is inhabited; all affine terms become constants, and the
-- dimension+1 bound says exactly one term per indexed maximum.
def zeroDimPolynomial : Thesis.Tropical.Polynomial (Fin 0) where
  Terms := Fin 3
  finite := inferInstance
  inhabited := inferInstance
  slope := fun _ i => Fin.elim0 i
  intercept := fun i => if i=0 then -3 else if i=1 then 2 else 7

example : ∃ (N : ℕ) (c : Fin N → ℝ) (q : Fin N → Thesis.Tropical.Polynomial (Fin 0)),
    (∀ j, Fintype.card (q j).Terms=1) ∧
    ∀ x, zeroDimPolynomial.eval x=∑ j, c j*(q j).eval x := by
  obtain ⟨N,c,q,hcard,hrep⟩ := polynomial_signed_small_max zeroDimPolynomial
  refine ⟨N,c,q,?_,hrep⟩
  intro j
  have hpos := Fintype.card_pos (α := (q j).Terms)
  have hj := hcard j
  simp only [Fintype.card_fin] at hj
  omega

-- Dependence uses only slopes. Ignoring intercept orientation would be wrong:
-- slopes 0,1,2 admit c=(1,-2,1), but intercepts 10,0,10 give a positive constant.
def biasedPolynomial : Thesis.Tropical.Polynomial Unit where
  Terms := Fin 3
  finite := inferInstance
  inhabited := inferInstance
  slope := fun i _ => i.val
  intercept := fun i => if i=1 then 0 else 10

def badOrientation (i : Fin 3) : ℝ := if i=1 then -2 else 1

example : (∑ i, badOrientation i)=0 := by
  norm_num [badOrientation,Fin.sum_univ_succ]
example : (∑ i, badOrientation i • biasedPolynomial.slope i)=0 := by
  funext j
  norm_num [badOrientation,biasedPolynomial,Fin.sum_univ_succ]
  delta biasedPolynomial
  norm_num
example : (∑ i, badOrientation i * biasedPolynomial.intercept i)=20 := by
  norm_num [badOrientation,biasedPolynomial,Fin.sum_univ_succ]
  change (10 : ℝ) + (-(2*0)+10) = 20
  norm_num

-- Nontrivial cardinal premise: dim=1 and three terms. The actual theorem
-- derives a correctly oriented global partition despite those arbitrary biases.
example : ∃ (A B : Finset biasedPolynomial.Terms) (_ : A.Nonempty) (hB : B.Nonempty),
    Disjoint A B ∧ A ∪ B=Finset.univ ∧
    ∀ x : Unit → ℝ, ∃ a ∈ A,
      biasedPolynomial.slope a ⬝ᵥ x+biasedPolynomial.intercept a ≤
        B.sup' hB (fun b => biasedPolynomial.slope b ⬝ᵥ x+biasedPolynomial.intercept b) := by
  apply global_partition
  change Fintype.card Unit + 1 < Fintype.card (Fin 3)
  norm_num

-- Cancellation survives equality, and the dominated member may be one of two.
example : (∑ S ∈ ({0,1} : Finset (Fin 3)).powerset,
    (-1 : ℝ)^S.card * baseMax (fun _ => (5 : ℝ)) {2} (by simp) S)=0 := by
  apply alternating_max_zero
  refine ⟨0,by simp,?_⟩
  simp

end
