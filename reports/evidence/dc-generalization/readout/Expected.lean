import HiddenMonotonicity.ConvexMonotoneReadout

/-! Independently specified consumer contracts for the generic signed affine
readout. Quantifiers and hypotheses are written here rather than inferred from
the theorem declarations being checked. -/
noncomputable section
set_option autoImplicit false
open HiddenMonotonicity

example : ∀ (n m k : ℕ) (backbone : Network n m)
    (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ)
      (positiveBias negativeBias : Vec k) (input : PairVec n),
      (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).1 -
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).2 =
        affineLayer positive negative positiveBias negativeBias
          (backbone.forwardWith activation (input.1 - input.2)) := by
  intro n m k backbone activation lift valid positive negative positiveBias negativeBias input
  exact backbone.affineDecomposeWith_recovery activation lift valid
    positive negative positiveBias negativeBias input

example : ∀ (n m k : ℕ) (backbone : Network n m), backbone.Nonnegative →
    ∀ (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift → Monotone lift →
    (ConvexOn ℝ Set.univ (fun z => (lift z).1) ∧
      ConvexOn ℝ Set.univ (fun z => (lift z).2)) →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ),
      (∀ i j, 0 ≤ positive i j) → (∀ i j, 0 ≤ negative i j) →
    ∀ (positiveBias negativeBias : Vec k),
      Monotone (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : PairVec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).1 j)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : PairVec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).2 j)) ∧
      ∀ input : PairVec n,
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).1 -
          (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).2 =
          affineLayer positive negative positiveBias negativeBias
            (backbone.forwardWith activation (input.1 - input.2)) := by
  intro n m k backbone nonnegative activation lift valid monotone convex
    positive negative positiveNonnegative negativeNonnegative positiveBias negativeBias
  exact backbone.affine_convex_monotone_decomposition nonnegative activation lift
    valid monotone convex positive negative positiveNonnegative negativeNonnegative
    positiveBias negativeBias

example : ∀ (n m k : ℕ) (backbone : Network n m), backbone.Nonnegative →
    ∀ (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift → Monotone lift →
    (ConvexOn ℝ Set.univ (fun z => (lift z).1) ∧
      ConvexOn ℝ Set.univ (fun z => (lift z).2)) →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ),
      (∀ i j, 0 ≤ positive i j) → (∀ i j, 0 ≤ negative i j) →
    ∀ (positiveBias negativeBias : Vec k),
      Monotone (fun input : Vec n =>
        backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).1 j)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).2 j)) ∧
      ∀ input : Vec n,
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).1 -
          (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).2 =
          affineLayer positive negative positiveBias negativeBias
            (backbone.forwardWith activation input) := by
  intro n m k backbone nonnegative activation lift valid monotone convex
    positive negative positiveNonnegative negativeNonnegative positiveBias negativeBias
  exact backbone.affine_dc_decomposition nonnegative activation lift
    valid monotone convex positive negative positiveNonnegative negativeNonnegative
    positiveBias negativeBias

example : ∀ (n m k : ℕ) (backbone : Network n m), backbone.Nonnegative →
    ∀ (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift → Monotone lift →
    (ConvexOn ℝ Set.univ (fun z => (lift z).1) ∧
      ConvexOn ℝ Set.univ (fun z => (lift z).2)) →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ),
      (∀ i j, 0 ≤ positive i j) → (∀ i j, 0 ≤ negative i j) →
    ∀ (positiveBias negativeBias : Vec k),
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
          ((fun i => max (input i) 0), (fun i => max (-input i) 0))).1 j)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
          ((fun i => max (input i) 0), (fun i => max (-input i) 0))).2 j)) ∧
      ∀ input : Vec n,
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
          ((fun i => max (input i) 0), (fun i => max (-input i) 0))).1 -
          (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
            ((fun i => max (input i) 0), (fun i => max (-input i) 0))).2 =
          affineLayer positive negative positiveBias negativeBias
            (backbone.forwardWith activation input) := by
  intro n m k backbone nonnegative activation lift valid monotone convex
    positive negative positiveNonnegative negativeNonnegative positiveBias negativeBias
  exact backbone.affine_signed_input_dc_decomposition nonnegative activation lift
    valid monotone convex positive negative positiveNonnegative negativeNonnegative
    positiveBias negativeBias

#print axioms Network.affineDecomposeWith_recovery
#print axioms Network.affineDecomposeWith_monotone_of_monotone
#print axioms matrix_convex_pair_input
#print axioms Network.affineDecomposeWith_convex_of_convex
#print axioms Network.affineDecomposeWith_monotone
#print axioms Network.affineDecomposeWith_convex
#print axioms Network.affine_convex_monotone_decomposition
#print axioms convex_pair_zero_input
#print axioms Network.affine_dc_decomposition
#print axioms Network.affineDecomposeWith_convex_input
#print axioms signedInput_difference
#print axioms signedInput_nonnegative
#print axioms signedInput_convex
#print axioms Network.affine_signed_input_dc_decomposition
