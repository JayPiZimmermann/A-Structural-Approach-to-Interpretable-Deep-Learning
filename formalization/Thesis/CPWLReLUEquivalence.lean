import Thesis.ReLUCompiler
import Thesis.SignedMaxReduction
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Full CPWL–ReLU equivalence and the dimension-only depth bound, assembled
from independent finite-cover, signed-max and actual shared-network constructions. -/
noncomputable section
namespace Thesis.PiecewiseLinear
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.ReLURepresentation

/-- Taking a scalar coordinate preserves the actual finite-polyhedral cover. -/
theorem CPWL.scalar_component {I O : Type} [Fintype I]
    {f : (I → ℝ) → O → ℝ} (hf : CPWL f) (i : O) :
    CPWL (fun x (_ : Unit) => f x i) := by
  obtain ⟨hc,⟨C⟩⟩ := hf
  refine ⟨continuous_pi (fun _ => (continuous_apply i).comp hc),?_⟩
  exact ⟨{ Pieces := C.Pieces
           finite := C.finite
           cell := C.cell
           slope := fun a _ => C.slope a i
           bias := fun a _ => C.bias a i
           covers := C.covers
           affine_on := fun a x hx _ => C.affine_on a x hx i }⟩

/-- Arbitrary scalar affine readouts of the shared network are CPWL in the same
scalar convention used by the representation theorem. -/
theorem scalar_affine_network_cpwl {n m : ℕ} (net : Network n m)
    (w : Fin m → ℝ) (b : ℝ) :
    CPWL (fun x (_ : Unit) => w ⬝ᵥ net.eval x+b) := by
  have h := affine_network_cpwl net (fun (_ : Fin 1) j => w j) (fun _ => b)
  exact h.scalar_component 0

/-- Genuine dimension-only representation, with a shared Network and explicit
signed affine readout. The final affine output counts as one layer. -/
theorem cpwl_relu_bounded_depth {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : CPWL (fun x (_ : Unit) => f x)) :
    ∃ (m : ℕ) (net : Network n m) (w : Fin m → ℝ) (b : ℝ),
      hiddenDepth net+1≤⌈Real.logb 2 (n+1)⌉₊+1 ∧
      ∀ x, f x=w ⬝ᵥ net.eval x+b := by
  obtain ⟨g,h,he⟩ := cpwl_polynomial_difference f hf
  obtain ⟨N,c,q,hq,hrep⟩ := Thesis.SignedMaxReduction.difference_signed_small_max g h
  have hcard : ∀ j, Fintype.card (q j).Terms≤2^(Nat.clog 2 (n+1)) := by
    intro j
    have hj : Fintype.card (q j).Terms≤n+1 := by simpa using hq j
    exact hj.trans (Nat.le_pow_clog (by norm_num) (n+1))
  obtain ⟨H,hd,hH⟩ := signed_polynomial_compiler (Fin N) q c hcard
  refine ⟨H.width,H.network,H.weights (),H.bias (),?_,?_⟩
  · have hlog : ⌈Real.logb 2 (n+1)⌉₊=Nat.clog 2 (n+1) := by
      simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 (n+1)
    rw [hlog]
    exact Nat.add_le_add_right hd.le 1
  · intro x
    exact (he x).trans ((hrep x).trans (hH x).symm)

/-- thm:cpwl_relu_equivalence, including both directions and the full stated
ceil(log₂(d+1))+1 bound. No DC representation, lattice formula or network
realizability is assumed for the input CPWL function. -/
theorem cpwl_relu_equivalence {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    (CPWL (fun x (_ : Unit) => f x) ↔
      ∃ (m : ℕ) (net : Network n m) (w : Fin m → ℝ) (b : ℝ),
        ∀ x, f x=w ⬝ᵥ net.eval x+b) ∧
    (CPWL (fun x (_ : Unit) => f x) →
      ∃ (m : ℕ) (net : Network n m) (w : Fin m → ℝ) (b : ℝ),
        hiddenDepth net+1≤⌈Real.logb 2 (n+1)⌉₊+1 ∧
        ∀ x, f x=w ⬝ᵥ net.eval x+b) := by
  refine ⟨⟨?_,?_⟩,cpwl_relu_bounded_depth f⟩
  · intro hf
    obtain ⟨m,net,w,b,_,he⟩ := cpwl_relu_bounded_depth f hf
    exact ⟨m,net,w,b,he⟩
  · rintro ⟨m,net,w,b,he⟩
    have hfun : f=(fun x => w ⬝ᵥ net.eval x+b) := funext he
    rw [hfun]
    exact scalar_affine_network_cpwl net w b

end Thesis.PiecewiseLinear
