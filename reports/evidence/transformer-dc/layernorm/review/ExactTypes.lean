import HiddenMonotonicity.LayerNormDCLift
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
def _ThesisExpectedTypes.type_0 : Prop := (∀ ε : ℝ, 0 < ε → ∀ z : ℝ, HasDerivAt (HiddenMonotonicity.SmoothDC.inverseSqrtExtension ε) (HiddenMonotonicity.SmoothDC.inverseSqrtExtensionDeriv ε z) z)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtExtension_hasDerivAt
#print axioms _ThesisExactChecks.target_0

section
def _ThesisExpectedTypes.type_1 : Prop := (∀ ε : ℝ, 0 < ε → ConvexOn ℝ Set.univ (HiddenMonotonicity.SmoothDC.inverseSqrtExtension ε))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtExtension_convex
#print axioms _ThesisExactChecks.target_1

section
def _ThesisExpectedTypes.type_2 : Prop := (∀ ε : ℝ, 0 < ε → ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).1) ∧ ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).2))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtPair_convex
#print axioms _ThesisExactChecks.target_2

section
def _ThesisExpectedTypes.type_3 : Prop := (∀ ε : ℝ, 0 < ε → Monotone (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtPair_monotone
#print axioms _ThesisExactChecks.target_3

section
def _ThesisExpectedTypes.type_4 : Prop := (∀ ε : ℝ, 0 < ε → ∀ z : ℝ × ℝ, 0 ≤ z → 0 ≤ HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtPair_nonneg
#print axioms _ThesisExactChecks.target_4

section
def _ThesisExpectedTypes.type_5 : Prop := (∀ ε : ℝ, 0 < ε → ∀ z : ℝ × ℝ, 0 ≤ z.1 - z.2 → (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).1 - (HiddenMonotonicity.SmoothDC.inverseSqrtPair ε z).2 = (Real.sqrt (ε + (z.1 - z.2)))⁻¹)
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5 := by exact @HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference"
#check @HiddenMonotonicity.SmoothDC.inverseSqrtPair_difference
#print axioms _ThesisExactChecks.target_5

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/transformer-dc/layernorm/review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

