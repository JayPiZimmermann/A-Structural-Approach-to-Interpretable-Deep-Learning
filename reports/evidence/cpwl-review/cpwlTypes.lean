import Thesis.CPWLLattice
set_option pp.explicit true
set_option pp.universes true

noncomputable section
open Set Filter Matrix Finset Thesis.Tropical Thesis.PiecewiseLinear
open scoped Topology
example : ∀ {A : Type} [Fintype A] (f : ℝ → ℝ) (a b : A → ℝ)
(hf : Continuous f) (hsel : ∀ t, ∃ i, f t=(1-t)*a i+t*b i),
∃ i, f 0≤a i ∧ b i≤f 1 := @Thesis.PiecewiseLinear.affine_selection_separation
#check @Thesis.PiecewiseLinear.affine_selection_separation
#print axioms Thesis.PiecewiseLinear.affine_selection_separation
end

noncomputable section
open Set Filter Matrix Finset Thesis.Tropical Thesis.PiecewiseLinear
open scoped Topology
example : ∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ)
(hf : CPWL (fun x (_ : Unit) => f x)),
∃ p : MaxMinPolynomial I, ∀ x, f x=p.eval x := @Thesis.PiecewiseLinear.cpwl_lattice_representation
#check @Thesis.PiecewiseLinear.cpwl_lattice_representation
#print axioms Thesis.PiecewiseLinear.cpwl_lattice_representation
end

noncomputable section
open Set Filter Matrix Finset Thesis.Tropical Thesis.PiecewiseLinear
open scoped Topology
example : ∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ)
(hf : CPWL (fun x (_ : Unit) => f x)),
∃ g h : Thesis.Tropical.Polynomial I, ∀ x, f x=g.eval x-h.eval x := @Thesis.PiecewiseLinear.cpwl_polynomial_difference
#check @Thesis.PiecewiseLinear.cpwl_polynomial_difference
#print axioms Thesis.PiecewiseLinear.cpwl_polynomial_difference
end

noncomputable section
open Set Filter Matrix Finset Thesis.Tropical Thesis.PiecewiseLinear
open scoped Topology
example : ∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ),
CPWL (fun x (_ : Unit) => f x) ↔
∃ g h : Thesis.Tropical.Polynomial I, ∀ x, f x=g.eval x-h.eval x := @Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference
#check @Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference
#print axioms Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference
end
