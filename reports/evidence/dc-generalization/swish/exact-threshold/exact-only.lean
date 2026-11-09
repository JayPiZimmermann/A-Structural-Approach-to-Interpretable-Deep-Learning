import HiddenMonotonicity.SwishThreshold
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_0 : Prop := (∀ β : ℝ, 0 < β → ∀ x : ℝ, (0 < curvature (swish β) x ↔ |β * x| < swishTurningPoint) ∧ (curvature (swish β) x < 0 ↔ swishTurningPoint < |β * x|) ∧ (curvature (swish β) x = 0 ↔ |β * x| = swishTurningPoint))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SwishThreshold do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign"
#check @HiddenMonotonicity.SmoothDC.swish_curvature_turning_sign
#print axioms _ThesisExactChecks.target_0

