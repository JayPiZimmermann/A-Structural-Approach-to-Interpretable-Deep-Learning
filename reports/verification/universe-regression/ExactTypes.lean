import HiddenMonotonicity.MaxPool
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
universe u
open HiddenMonotonicity
open scoped BigOperators
def _ThesisExpectedTypes.type_0 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι],
 (∀ x, (finitePool (ι := ι) x).1-(finitePool x).2 = Finset.univ.sup' Finset.univ_nonempty (fun j => x.1 j-x.2 j)) ∧
 (∀ x, 0≤x → 0≤finitePool (ι := ι) x) ∧ Monotone (finitePool (ι := ι)) ∧
 ConvexOn ℝ Set.univ (fun x => (finitePool (ι := ι) x).1) ∧ ConvexOn ℝ Set.univ (fun x => (finitePool (ι := ι) x).2))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0.{u} := by exact @HiddenMonotonicity.maxpool_properties.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.maxpool_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.maxpool_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.maxpool_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MaxPool do
    throwError "Defining module mismatch: HiddenMonotonicity.maxpool_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.maxpool_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.maxpool_properties"
#check @HiddenMonotonicity.maxpool_properties
#print axioms _ThesisExactChecks.target_0

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/dc_decompose/master_thesis/reports/verification/universe-regression/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

