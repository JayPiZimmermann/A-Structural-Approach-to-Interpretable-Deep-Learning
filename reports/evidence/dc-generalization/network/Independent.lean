import HiddenMonotonicity.ConvexMonotoneNetwork

noncomputable section
set_option autoImplicit false
open Set HiddenMonotonicity

private def reviewedReLUPair (z : ℝ × ℝ) : ℝ × ℝ := (max z.1 z.2,z.2)

private theorem reviewedReLUPair_monotone : Monotone reviewedReLUPair := by
  intro x y hxy
  exact ⟨max_le_max hxy.1 hxy.2,hxy.2⟩

private theorem reviewedReLUPair_convex : ConvexPairActivation reviewedReLUPair := by
  constructor
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have h : 1-a=b := by linarith
    simpa [reviewedReLUPair,h] using
      max_jensen x.1 x.2 y.1 y.2 a ha (by linarith)
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    exact le_rfl

private theorem reviewedReLUPair_valid : ValidPairActivation relu reviewedReLUPair := by
  intro p q
  exact HiddenMonotonicity.max_sub p q

/-- Independently instantiated full-network consumer of the user-requested
max/identity ReLU case, with all widths and arbitrary split biases retained. -/
example {n m : ℕ} (net : Network n m) (weights : net.Nonnegative) :
    Monotone (net.decomposeWith reviewedReLUPair) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n =>
      (net.decomposeWith reviewedReLUPair x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n =>
      (net.decomposeWith reviewedReLUPair x).2 i)) ∧
    ∀ x : PairVec n,
      (net.decomposeWith reviewedReLUPair x).1 -
        (net.decomposeWith reviewedReLUPair x).2 = net.eval (x.1-x.2) := by
  obtain ⟨hmono,hp,hq,hrecover⟩ := net.convex_monotone_decomposition weights
    relu reviewedReLUPair reviewedReLUPair_valid reviewedReLUPair_monotone
    reviewedReLUPair_convex
  refine ⟨hmono,hp,hq,?_⟩
  intro x
  rw [hrecover,net.forwardWith_relu]

#print axioms HiddenMonotonicity.Network.convex_monotone_decomposition
