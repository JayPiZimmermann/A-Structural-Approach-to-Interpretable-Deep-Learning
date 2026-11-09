import Thesis.SoftplusLimits
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open Filter Thesis.Regularization
open scoped Topology
def _ThesisExpectedTypes.type_0 : Prop := (∀ (z : ℝ) (hz : 0 < z), Tendsto (fun θ : ℝ => gate θ z) (𝓝[>] 0) (𝓝 1))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @Thesis.SoftplusLimits.gate_limit_positive
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusLimits.gate_limit_positive
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusLimits.gate_limit_positive"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusLimits.gate_limit_positive | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusLimits do
    throwError "Defining module mismatch: Thesis.SoftplusLimits.gate_limit_positive"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusLimits.gate_limit_positive: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusLimits.gate_limit_positive"
#check @Thesis.SoftplusLimits.gate_limit_positive
#print axioms _ThesisExactChecks.target_0

section
open Filter Thesis.Regularization
open scoped Topology
def _ThesisExpectedTypes.type_1 : Prop := (∀ (z : ℝ) (hz : z < 0), Tendsto (fun θ : ℝ => gate θ z) (𝓝[>] 0) (𝓝 0))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @Thesis.SoftplusLimits.gate_limit_negative
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusLimits.gate_limit_negative
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusLimits.gate_limit_negative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusLimits.gate_limit_negative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusLimits do
    throwError "Defining module mismatch: Thesis.SoftplusLimits.gate_limit_negative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusLimits.gate_limit_negative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusLimits.gate_limit_negative"
#check @Thesis.SoftplusLimits.gate_limit_negative
#print axioms _ThesisExactChecks.target_1

section
open Filter Thesis.Regularization
open scoped Topology
def _ThesisExpectedTypes.type_2 : Prop := (∀ (u v : ℝ) (hne : u ≠ v), Tendsto (fun θ : ℝ => softSplit θ u v) (𝓝[>] 0) (𝓝 (Thesis.StoppingDecomposition.stopPair (u,v))))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @Thesis.SoftplusLimits.softSplit_tendsto_stopping
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusLimits.softSplit_tendsto_stopping
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusLimits.softSplit_tendsto_stopping"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusLimits.softSplit_tendsto_stopping | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusLimits do
    throwError "Defining module mismatch: Thesis.SoftplusLimits.softSplit_tendsto_stopping"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusLimits.softSplit_tendsto_stopping: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusLimits.softSplit_tendsto_stopping"
#check @Thesis.SoftplusLimits.softSplit_tendsto_stopping
#print axioms _ThesisExactChecks.target_2

section
open Filter Thesis.Regularization
open scoped Topology
def _ThesisExpectedTypes.type_3 : Prop := (∀ u : ℝ, Tendsto (fun θ : ℝ => softSplit θ u u) (𝓝[>] 0) (𝓝 (u/2,u/2)))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @Thesis.SoftplusLimits.softSplit_tendsto_tie
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusLimits.softSplit_tendsto_tie
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusLimits.softSplit_tendsto_tie"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusLimits.softSplit_tendsto_tie | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusLimits do
    throwError "Defining module mismatch: Thesis.SoftplusLimits.softSplit_tendsto_tie"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusLimits.softSplit_tendsto_tie: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusLimits.softSplit_tendsto_tie"
#check @Thesis.SoftplusLimits.softSplit_tendsto_tie
#print axioms _ThesisExactChecks.target_3

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/dc_decompose/master_thesis/reports/evidence/softplus-limits-review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

