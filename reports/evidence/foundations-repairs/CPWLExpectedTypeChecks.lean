import Thesis.CPWLLattice
import Thesis.CPWLReLUEquivalence
import Thesis.ReLUCompiler
open Set Filter Matrix Finset HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis.ReLURepresentation
open scoped Topology

example : ∀ {A : Type} [Fintype A] (f : ℝ → ℝ) (a b : A → ℝ)
(hf : Continuous f) (hsel : ∀ t, ∃ i, f t=(1-t)*a i+t*b i),
∃ i, f 0≤a i ∧ b i≤f 1 := @Thesis.PiecewiseLinear.affine_selection_separation
#print axioms Thesis.PiecewiseLinear.affine_selection_separation

example : ∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ)
(hf : CPWL (fun x (_ : Unit) => f x)),
∃ p : MaxMinPolynomial I, ∀ x, f x=p.eval x := @Thesis.PiecewiseLinear.cpwl_lattice_representation
#print axioms Thesis.PiecewiseLinear.cpwl_lattice_representation

example : ∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ)
(hf : CPWL (fun x (_ : Unit) => f x)),
∃ g h : Thesis.Tropical.Polynomial I, ∀ x, f x=g.eval x-h.eval x := @Thesis.PiecewiseLinear.cpwl_polynomial_difference
#print axioms Thesis.PiecewiseLinear.cpwl_polynomial_difference

example : ∀ {I : Type} [Fintype I] (f : (I → ℝ) → ℝ),
CPWL (fun x (_ : Unit) => f x) ↔
∃ g h : Thesis.Tropical.Polynomial I, ∀ x, f x=g.eval x-h.eval x := @Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference
#print axioms Thesis.PiecewiseLinear.cpwl_iff_polynomial_difference

example : ∀ {n : ℕ} (k : ℕ) (O : Type) [Fintype O]
(w : O → (Fin k → Bool) → Fin n → ℝ) (b : O → (Fin k → Bool) → ℝ),
∃ H : AffineHead n O, H.depth=k ∧
∀ x i, H.eval x i=finiteMax (fun t => w i t ⬝ᵥ x+b i t) := @Thesis.ReLURepresentation.affine_max_forest
#print axioms Thesis.ReLURepresentation.affine_max_forest

example : ∀ {n k : ℕ} (O : Type) [Fintype O]
(p : O → Thesis.Tropical.Polynomial (Fin n))
(hcard : ∀ i, Fintype.card (p i).Terms≤2^k),
∃ H : AffineHead n O, H.depth=k ∧ ∀ x i, H.eval x i=(p i).eval x := @Thesis.ReLURepresentation.polynomial_forest
#print axioms Thesis.ReLURepresentation.polynomial_forest

example : ∀ {n k : ℕ} (O : Type) [Fintype O]
(p : O → Thesis.Tropical.Polynomial (Fin n)) (c : O → ℝ)
(hcard : ∀ i, Fintype.card (p i).Terms≤2^k),
∃ H : AffineHead n Unit, H.depth=k ∧
∀ x, H.eval x ()=∑ i, c i*(p i).eval x := @Thesis.ReLURepresentation.signed_polynomial_compiler
#print axioms Thesis.ReLURepresentation.signed_polynomial_compiler

example : ∀ {n : ℕ} (f : (Fin n → ℝ) → ℝ)
(hf : CPWL (fun x (_ : Unit) => f x)),
∃ (m : ℕ) (net : Network n m) (w : Fin m → ℝ) (b : ℝ),
hiddenDepth net+1≤⌈Real.logb 2 (n+1)⌉₊+1 ∧
∀ x, f x=w ⬝ᵥ net.eval x+b := @Thesis.PiecewiseLinear.cpwl_relu_bounded_depth
#print axioms Thesis.PiecewiseLinear.cpwl_relu_bounded_depth

example : ∀ {n : ℕ} (f : (Fin n → ℝ) → ℝ),
(CPWL (fun x (_ : Unit) => f x) ↔
  ∃ (m : ℕ) (net : Network n m) (w : Fin m → ℝ) (b : ℝ),
    ∀ x, f x=w ⬝ᵥ net.eval x+b) ∧
(CPWL (fun x (_ : Unit) => f x) →
  ∃ (m : ℕ) (net : Network n m) (w : Fin m → ℝ) (b : ℝ),
    hiddenDepth net+1≤⌈Real.logb 2 (n+1)⌉₊+1 ∧
    ∀ x, f x=w ⬝ᵥ net.eval x+b) := @Thesis.PiecewiseLinear.cpwl_relu_equivalence
#print axioms Thesis.PiecewiseLinear.cpwl_relu_equivalence
