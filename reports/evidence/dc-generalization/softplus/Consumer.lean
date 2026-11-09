import HiddenMonotonicity.ExplicitSoftplus
import Lean

set_option autoImplicit false
open Lean Elab Command
open HiddenMonotonicity HiddenMonotonicity.SmoothDC

-- Written independently as the intended all-real-domain contract.
def SoftplusExplicitContract : Prop :=
  ∀ θ : ℝ, 0 < θ →
    ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).1) ∧
    ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).2) ∧
    Monotone (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).1) ∧
    Monotone (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).2) ∧
    ValidPairActivation (Thesis.Regularization.softplus θ) (explicitSoftplusPair θ) ∧
    NonnegativePairActivation (explicitSoftplusPair θ)

theorem softplusExplicitContractChecked : SoftplusExplicitContract :=
  @softplus_explicit_split

def SoftplusLogsumexpContract : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ x y : ℝ,
    explicitSoftplusFirst θ (x,y) =
      θ * Real.log (Real.exp (x / θ) + Real.exp (y / θ))

theorem softplusLogsumexpContractChecked : SoftplusLogsumexpContract :=
  @explicitSoftplusFirst_logsumexp

run_cmd do
  for (targetName, expectedName) in
      [( ``softplus_explicit_split, ``softplusExplicitContractChecked),
       ( ``explicitSoftplusFirst_logsumexp, ``softplusLogsumexpContractChecked)] do
    let target ← getConstInfo targetName
    let expected ← getConstInfo expectedName
    unless target.levelParams.isEmpty && expected.levelParams.isEmpty do
      throwError "Unexpected universe parameters in {targetName}"
    let env ← getEnv
    let some index := env.getModuleIdxFor? targetName | throwError "Target not imported"
    unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftplus do
      throwError "Wrong defining module for {targetName}"
    liftTermElabM do
      unless ← Meta.isDefEq target.type expected.type do
        throwError "Exact type mismatch for {targetName}"
    for axiomName in (← Lean.collectAxioms targetName) do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unapproved axiom {axiomName} in {targetName}"

#check @softplus_explicit_split
#check @explicitSoftplusFirst_logsumexp
#print axioms softplus_explicit_split
#print axioms explicitSoftplusFirst_logsumexp

-- Nonvacuity at two positive temperatures and the coordinate boundary.
example : (explicitSoftplusPair 1 (0,0)) = (Real.log 2,0) := by
  norm_num [explicitSoftplusPair,explicitSoftplusFirst,Thesis.Regularization.softplus]

example : (explicitSoftplusPair 2 (0,0)) = (2 * Real.log 2,0) := by
  norm_num [explicitSoftplusPair,explicitSoftplusFirst,Thesis.Regularization.softplus]

example : NonnegativePairActivation (explicitSoftplusPair 2) :=
  explicitSoftplusPair_nonnegative 2 (by norm_num)

-- Recovery has no sign restriction on either input coordinate.
example : (explicitSoftplusPair 1 (-2,-3)).1 - (explicitSoftplusPair 1 (-2,-3)).2 =
    Thesis.Regularization.softplus 1 ((-2)-(-3)) :=
  explicitSoftplusPair_valid 1 (-2) (-3)

example : explicitSoftplusFirst 2 (-2,3) ≤ explicitSoftplusFirst 2 (1,4) :=
  explicitSoftplusFirst_monotone 2 (by norm_num) (by constructor <;> norm_num)
