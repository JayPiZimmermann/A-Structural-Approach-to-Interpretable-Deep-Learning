import HiddenMonotonicity.ExplicitSwish
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_0 : Prop := (∀ β : ℝ, 0 < β → ConvexOn ℝ Set.univ (explicitSwishFirst β) ∧ ConvexOn ℝ Set.univ (explicitSwishSecond β) ∧ Monotone (explicitSwishFirst β) ∧ Monotone (explicitSwishSecond β) ∧ ∀ z : ℝ × ℝ, explicitSwishFirst β z - explicitSwishSecond β z = (z.1 - z.2) * Real.sigmoid (β * (z.1 - z.2)))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.SmoothDC.explicitSwish_lift
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitSwish_lift
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_lift"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitSwish_lift | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSwish do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_lift"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitSwish_lift: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_lift"
#check @HiddenMonotonicity.SmoothDC.explicitSwish_lift
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_1 : Prop := (∀ β : ℝ, ∀ z : ℝ × ℝ, explicitSwishFirst β z = 2 / β * Real.log (1 + Real.exp (β * (z.1 - z.2))) + 2 * z.2 ∧ explicitSwishSecond β z = 2 / β * Real.log (1 + Real.exp (β * (z.1 - z.2))) - (z.1 - z.2) * Real.sigmoid (β * (z.1 - z.2)) + 2 * z.2)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.SmoothDC.explicitSwish_closed
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitSwish_closed
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_closed"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitSwish_closed | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSwish do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_closed"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitSwish_closed: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitSwish_closed"
#check @HiddenMonotonicity.SmoothDC.explicitSwish_closed
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_2 : Prop := (∀ β : ℝ, 0 < β → NonnegativePairActivation (explicitSwishPair β))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSwish do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative"
#check @HiddenMonotonicity.SmoothDC.explicitSwishPair_nonnegative
#print axioms _ThesisExactChecks.target_2

set_option maxHeartbeats 0
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut records : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[index.toNat]!
    unless modName.toString.startsWith "HiddenMonotonicity" || modName.toString.startsWith "Thesis" do continue
    let .thmInfo _ := info | continue
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unapproved axiom {axiomName} in {name}"
    let typeText ← liftTermElabM do return (← Lean.Meta.ppExpr info.type).pretty
    records := records.push <| Json.mkObj [
      ("declaration", toJson name.toString), ("module", toJson modName.toString),
      ("type", toJson typeText), ("universes", toJson (info.levelParams.map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/dc-generalization/swish/exact-elementary/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

