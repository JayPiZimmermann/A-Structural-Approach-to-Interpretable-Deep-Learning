import Thesis.CPWLReLUEquivalence

noncomputable section
open HiddenMonotonicity Thesis.Tropical Thesis.ReLURepresentation Thesis.PiecewiseLinear
open Matrix Finset

-- Actual affine input pairs: u=-2*x+1 and v=-5. The selected maximum can be negative.
def signedPair : AffineHead 1 (Unit × Bool) :=
  affineHead (Matrix.of (fun i _ => if i.2 then 0 else -2))
    (fun i => if i.2 then -5 else 1)

theorem signedPair_eval (x : Fin 1 → ℝ) (i : Unit × Bool) :
    signedPair.eval x i=(if i.2 then 0 else -2)*x 0+(if i.2 then -5 else 1) := by
  change ((Matrix.of (fun (j : Unit × Bool) (_ : Fin 1) => if j.2 then (0 : ℝ) else -2) :
    Matrix (Unit × Bool) (Fin 1) ℝ).mulVec x) i + (if i.2 then -5 else 1) = _
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_one]

example : signedPair.pairwiseMax.eval (fun _ => 2) () = -3 := by
  rw [AffineHead.pairwiseMax_eval]
  norm_num [signedPair_eval]

-- An exact negative tie must not be replaced by a final ReLU.
example : signedPair.pairwiseMax.eval (fun _ => 3) () = -5 := by
  rw [AffineHead.pairwiseMax_eval]
  norm_num [signedPair_eval]

example : signedPair.pairwiseMax.depth=1 := by
  rw [AffineHead.pairwiseMax_depth]
  rfl

-- Negative outer coefficients remain in the real affine readout without a layer.
example : (signedPair.pairwiseMax.linearCombination (fun _ => -2)).depth=1 := by
  rw [AffineHead.linearCombination_depth,AffineHead.pairwiseMax_depth]
  rfl
example : (signedPair.pairwiseMax.linearCombination (fun _ => -2)).eval (fun _ => 2) ()=6 := by
  rw [AffineHead.linearCombination_eval]
  simp only [Fintype.sum_unique,AffineHead.pairwiseMax_eval]
  norm_num [signedPair_eval]

-- A three-term polynomial requires padding to four leaves at k=2.
def threeTerms : Thesis.Tropical.Polynomial (Fin 1) where
  Terms := Fin 3
  finite := inferInstance
  inhabited := inferInstance
  slope := fun i _ => (i.val : ℝ)-1
  intercept := fun _ => -3

example : ∃ H : AffineHead 1 Unit, H.depth=2 ∧
    ∀ x i, H.eval x i=threeTerms.eval x := by
  apply polynomial_forest Unit (fun _ => threeTerms)
  intro i
  change Fintype.card (Fin 3)≤2^2
  norm_num

-- The empty outer sum produces a scalar zero head, rather than an empty conclusion.
example : ∃ H : AffineHead 2 Unit, H.depth=3 ∧ ∀ x, H.eval x ()=0 := by
  obtain ⟨H,hd,he⟩ := signed_polynomial_compiler (n:=2) (k:=3) (Fin 0)
    (fun i => Fin.elim0 i) (fun _ => 0) (fun i => Fin.elim0 i)
  refine ⟨H,hd,?_⟩
  intro x
  simpa using he x

-- Dimension zero and a negative constant: the literal theorem forces no hidden layers.
theorem negative_constant_cpwl : CPWL (fun (_ : Fin 0 → ℝ) (_ : Unit) => (-7 : ℝ)) := by
  simpa only [zero_dotProduct,zero_add] using
    scalar_affine_network_cpwl (.output 0) (0 : Fin 0 → ℝ) (-7)

example : ∃ (m : ℕ) (net : Network 0 m) (w : Fin m → ℝ) (b : ℝ),
    hiddenDepth net=0 ∧ ∀ x, (-7 : ℝ)=w ⬝ᵥ net.eval x+b := by
  obtain ⟨m,net,w,b,hd,he⟩ := cpwl_relu_bounded_depth (fun _ : Fin 0 → ℝ => (-7 : ℝ))
    negative_constant_cpwl
  refine ⟨m,net,w,b,?_,he⟩
  have hlog : ⌈Real.logb 2 ((0 : ℕ)+1)⌉₊=0 := by norm_num
  rw [hlog] at hd
  omega

-- A signed affine function on R has a literal zero-hidden-layer witness.
example : ∃ (m : ℕ) (net : Network 1 m) (w : Fin m → ℝ) (b : ℝ),
    hiddenDepth net=0 ∧ ∀ x, -2*x 0-5=w ⬝ᵥ net.eval x+b := by
  refine ⟨1,.output 1,(fun _ => -2),-5,rfl,?_⟩
  intro x
  simp [Network.eval,dotProduct,Fin.sum_univ_one]
  ring

-- Literal real-log ceiling agrees at the small dimensions most vulnerable to
-- off-by-one errors: total layer bounds are 1,2,3,3 for n=0,1,2,3.
example : ⌈Real.logb 2 ((0 : ℕ)+1)⌉₊+1=1 := by norm_num
example : ⌈Real.logb 2 ((1 : ℕ)+1)⌉₊+1=2 := by norm_num
example : ⌈Real.logb 2 ((2 : ℕ)+1)⌉₊+1=3 := by
  have h := Real.natCeil_logb_natCast 2 3
  norm_num at h ⊢
  exact h
example : ⌈Real.logb 2 ((3 : ℕ)+1)⌉₊+1=3 := by
  have h := Real.natCeil_logb_natCast 2 4
  norm_num at h ⊢
  exact h

end
