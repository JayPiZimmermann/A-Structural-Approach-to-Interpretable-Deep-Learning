import HiddenMonotonicity.ConvexMonotoneNetwork

noncomputable section
set_option autoImplicit false
open Set HiddenMonotonicity

private theorem identity_pair_convex : ConvexPairActivation (id : (ℝ × ℝ) → ℝ × ℝ) := by
  constructor
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    exact le_rfl
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    exact le_rfl

/-- Independent all-width consumer, including arbitrary layer biases. -/
example {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) :
    Monotone (net.decomposeWith id) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n => (net.decomposeWith id x).1 i)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : PairVec n => (net.decomposeWith id x).2 i)) ∧
    ∀ x : PairVec n, (net.decomposeWith id x).1-(net.decomposeWith id x).2 =
      net.forwardWith id (x.1-x.2) := by
  exact net.convex_monotone_decomposition hw id id
    (fun _ _ => rfl) monotone_id identity_pair_convex

private def signedBiasNetwork : Network 1 1 :=
  .layer (fun _ _ => 2) (fun _ _ => 3) (fun _ => -7) (fun _ => -11) (.output 1)

/-- Negative stream values and negative effective weights are admissible. -/
example :
    (signedBiasNetwork.decomposeWith id ((fun _ => 3),(fun _ => 0))).1 0 = -1 ∧
    (signedBiasNetwork.decomposeWith id ((fun _ => 3),(fun _ => 0))).2 0 = -2 := by
  change (∑ _i : Fin 1, (2 : ℝ)*3)+(∑ _i : Fin 1, (3 : ℝ)*0)+(-7) = -1 ∧
    (∑ _i : Fin 1, (3 : ℝ)*3)+(∑ _i : Fin 1, (2 : ℝ)*0)+(-11) = -2
  norm_num

example : signedBiasNetwork.Nonnegative := by
  simp [signedBiasNetwork, Network.Nonnegative]

/-- The empty-input base network has exact recovery; widths need not be positive. -/
example (x : PairVec 0) :
    ((Network.output 0).decomposeWith id x).1-
      ((Network.output 0).decomposeWith id x).2 =
      (Network.output 0).forwardWith id (x.1-x.2) := by
  rfl

#print axioms HiddenMonotonicity.Network.convex_monotone_decomposition
#print axioms HiddenMonotonicity.Network.decomposeWith_convex_input
#print axioms HiddenMonotonicity.convex_monotone_pair_input
