import HiddenMonotonicity.ExplicitSigmoidSoftplus
import Lean

set_option autoImplicit false

open HiddenMonotonicity HiddenMonotonicity.SmoothDC
open Lean Elab Command

/- Expected propositions are independently elaborated before the proof terms.
These consumer checks are handwritten, not extracted from inferred types. -/
def expectedSigmoidSplit : Prop :=
  ConvexOn ℝ Set.univ (fun z => (sigmoidExplicitPair z).1) ∧
  ConvexOn ℝ Set.univ (fun z => (sigmoidExplicitPair z).2) ∧
  Monotone sigmoidExplicitPair ∧
  ValidPairActivation Real.sigmoid sigmoidExplicitPair ∧
  NonnegativePairActivation sigmoidExplicitPair

theorem checkedSigmoidSplit : expectedSigmoidSplit := sigmoid_explicit_split

def expectedSigmoidClosedForm : Prop :=
  ∀ x y : ℝ, sigmoidExplicitPair (x, y) =
    (if x ≤ y then Real.sigmoid (x-y) + y/4 else 1/2 + x/4,
     if x ≤ y then y/4 else 1/2 + x/4 - Real.sigmoid (x-y))

theorem checkedSigmoidClosedForm : expectedSigmoidClosedForm :=
  sigmoidExplicitPair_closed_form

run_cmd do
  for (targetName, expectedName) in
      [(``sigmoid_explicit_split, ``checkedSigmoidSplit),
       (``sigmoidExplicitPair_closed_form, ``checkedSigmoidClosedForm)] do
    let target ← getConstInfo targetName
    let expected ← getConstInfo expectedName
    unless target.levelParams.isEmpty && expected.levelParams.isEmpty do
      throwError "Unexpected universe parameters: {targetName}"
    let env ← getEnv
    let some index := env.getModuleIdxFor? targetName
      | throwError "Target was not imported: {targetName}"
    unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSigmoidSoftplus do
      throwError "Wrong defining module: {targetName}"
    for axiomName in (← Lean.collectAxioms targetName) do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unapproved axiom: {targetName}: {axiomName}"
    liftTermElabM do
      unless ← Meta.isDefEq target.type expected.type do
        throwError "Exact type mismatch: {targetName}"

/-- Consumer at the inflection point checks that the two pieces meet smoothly. -/
example : HasDerivAt sigmoidPositiveProfile (1/4) 0 :=
  sigmoidPositiveProfile_derivative_zero

example : HasDerivAt sigmoidNegativeProfile 0 0 := by
  convert sigmoidNegativeProfile_derivative 0 using 1
  norm_num [sigmoidNegativeSlope, sigmoidPositiveSlope, sigmoidFirst]

/-- All diagonal values, including negative coordinates, use the same formulas. -/
example (r : ℝ) : sigmoidExplicitPair (r, r) = (1/2 + r/4, r/4) := by
  rw [sigmoidExplicitPair_closed_form]
  norm_num

/-- Nonnegativity is deliberately restricted to the nonnegative quadrant. -/
example : sigmoidExplicitPair (-4, -4) = (-1/2, -1) := by
  rw [sigmoidExplicitPair_closed_form]
  norm_num

example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (sigmoidExplicitPair (x,y)).1 ∧ 0 ≤ (sigmoidExplicitPair (x,y)).2 :=
  sigmoid_explicit_split.2.2.2.2 x y hx hy

example (x y : ℝ) :
    (sigmoidExplicitPair (x,y)).1 - (sigmoidExplicitPair (x,y)).2 =
      Real.sigmoid (x-y) := sigmoid_explicit_split.2.2.2.1 x y

#print axioms sigmoidFirst_le_quarter
#print axioms sigmoidFirst_monotoneOn_nonpositive
#print axioms sigmoidFirst_antitoneOn_nonnegative
#print axioms sigmoidPositiveSlope_bounds
#print axioms sigmoidNegativeSlope_bounds
#print axioms sigmoidPositiveSlope_monotone
#print axioms sigmoidNegativeSlope_monotone
#print axioms sigmoidPositiveProfile_derivative_zero
#print axioms sigmoidPositiveProfile_derivative
#print axioms sigmoidNegativeProfile_derivative
#print axioms sigmoidPositiveProfile_convex
#print axioms sigmoidNegativeProfile_convex
#print axioms sigmoidExplicitPair_closed_form
#print axioms sigmoid_explicit_split
