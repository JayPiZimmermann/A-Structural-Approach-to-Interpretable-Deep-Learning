import HiddenMonotonicity.ExplicitSigmoidSmooth
import Lean

set_option autoImplicit false
open Lean Elab Command
open HiddenMonotonicity HiddenMonotonicity.SmoothDC

def SigmoidSmoothSplitContract : Prop :=
  ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (explicitSigmoidSmoothPair z).1) ∧
  ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (explicitSigmoidSmoothPair z).2) ∧
  Monotone (fun z : ℝ × ℝ => (explicitSigmoidSmoothPair z).1) ∧
  Monotone (fun z : ℝ × ℝ => (explicitSigmoidSmoothPair z).2) ∧
  ValidPairActivation Real.sigmoid explicitSigmoidSmoothPair ∧
  NonnegativePairActivation explicitSigmoidSmoothPair

theorem sigmoidSmoothSplitContractChecked : SigmoidSmoothSplitContract :=
  @sigmoid_smooth_explicit_split

def SigmoidSmoothClosedContract : Prop :=
  ∀ x y : ℝ, explicitSigmoidSmoothPair (x,y) =
    ((Real.log (Real.exp x + Real.exp y) + Real.sigmoid (x-y)) / 2,
     (Real.log (Real.exp x + Real.exp y) - Real.sigmoid (x-y)) / 2)

theorem sigmoidSmoothClosedContractChecked : SigmoidSmoothClosedContract :=
  @explicitSigmoidSmoothPair_logsumexp

def SigmoidSmoothRegularityContract : Prop :=
  ContDiff ℝ ⊤ explicitSigmoidSmoothPair

theorem sigmoidSmoothRegularityContractChecked : SigmoidSmoothRegularityContract :=
  @explicitSigmoidSmoothPair_contDiff

run_cmd do
  for (targetName, expectedName) in
      [( ``sigmoid_smooth_explicit_split, ``sigmoidSmoothSplitContractChecked),
       ( ``explicitSigmoidSmoothPair_logsumexp, ``sigmoidSmoothClosedContractChecked),
       ( ``explicitSigmoidSmoothPair_contDiff, ``sigmoidSmoothRegularityContractChecked)] do
    let target ← getConstInfo targetName
    let expected ← getConstInfo expectedName
    unless target.levelParams.isEmpty && expected.levelParams.isEmpty do
      throwError "Unexpected universe parameters in {targetName}"
    let env ← getEnv
    let some index := env.getModuleIdxFor? targetName | throwError "Target not imported"
    unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSigmoidSmooth do
      throwError "Wrong defining module for {targetName}"
    liftTermElabM do
      unless ← Meta.isDefEq target.type expected.type do
        throwError "Exact type mismatch for {targetName}"
    for axiomName in (← Lean.collectAxioms targetName) do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unapproved axiom {axiomName} in {targetName}"

#check @sigmoid_smooth_explicit_split
#check @explicitSigmoidSmoothPair_logsumexp
#check @explicitSigmoidSmoothPair_contDiff
#print axioms sigmoid_smooth_explicit_split
#print axioms explicitSigmoidSmoothPair_logsumexp
#print axioms explicitSigmoidSmoothPair_contDiff

-- The exact origin values test the normalization used for quadrant preservation.
example : explicitSigmoidSmoothPair (0,0) =
    ((Real.log 2 + 1/2) / 2, (Real.log 2 - 1/2) / 2) := by
  norm_num [explicitSigmoidSmoothPair, asymmetricLift, sigmoidSmoothP,
    sigmoidSmoothQ, Thesis.Regularization.softplus]

-- The four coordinate derivatives distinguish this smooth construction from
-- the piecewise minimal-width split, including exactly on the diagonal.
example : HasDerivAt (fun t => (explicitSigmoidSmoothPair (t,0)).1) (3/8) 0 := by
  have h := asymmetricLift_derivative_first sigmoidSmoothP sigmoidSmoothPFirst
    sigmoidSmoothP_derivative (1/2) 0 0
  norm_num [sigmoidSmoothPFirst] at h
  exact h

example : HasDerivAt (fun t => (explicitSigmoidSmoothPair (0,t)).1) (1/8) 0 := by
  have h := asymmetricLift_derivative_second sigmoidSmoothP sigmoidSmoothPFirst
    sigmoidSmoothP_derivative (1/2) 0 0
  norm_num [sigmoidSmoothPFirst] at h
  exact h

example : HasDerivAt (fun t => (explicitSigmoidSmoothPair (t,0)).2) (1/8) 0 := by
  have h := asymmetricLift_derivative_first sigmoidSmoothQ sigmoidSmoothQFirst
    sigmoidSmoothQ_derivative (1/2) 0 0
  norm_num [sigmoidSmoothQFirst] at h
  exact h

example : HasDerivAt (fun t => (explicitSigmoidSmoothPair (0,t)).2) (3/8) 0 := by
  have h := asymmetricLift_derivative_second sigmoidSmoothQ sigmoidSmoothQFirst
    sigmoidSmoothQ_derivative (1/2) 0 0
  norm_num [sigmoidSmoothQFirst] at h
  exact h

example : (explicitSigmoidSmoothPair (-2,3)).1 -
    (explicitSigmoidSmoothPair (-2,3)).2 = Real.sigmoid ((-2)-3) :=
  explicitSigmoidSmoothPair_valid (-2) 3

example : (explicitSigmoidSmoothPair (-2,3)).1 ≤ (explicitSigmoidSmoothPair (1,4)).1 :=
  explicitSigmoidSmoothPair_first_monotone (by constructor <;> norm_num)

example : (explicitSigmoidSmoothPair (-2,3)).2 ≤ (explicitSigmoidSmoothPair (1,4)).2 :=
  explicitSigmoidSmoothPair_second_monotone (by constructor <;> norm_num)
