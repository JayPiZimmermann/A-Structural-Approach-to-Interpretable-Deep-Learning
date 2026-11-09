import HiddenMonotonicity.SoftmaxLineCalculus
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
universe u
open HiddenMonotonicity.SoftmaxDC
def _ThesisExpectedTypes.type_0 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (a v : ι → ℝ) (t : ℝ), HasDerivAt (fun r => logSumExp (affineLine a v r)) (mean (affineLine a v t) v) t)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0.{u} := by exact @HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative"
#check @HiddenMonotonicity.SoftmaxDC.logSumExp_line_derivative
#print axioms _ThesisExactChecks.target_0

section
universe u
open HiddenMonotonicity.SoftmaxDC
def _ThesisExpectedTypes.type_1 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (a v : ι → ℝ) (t : ℝ), HasDerivAt (fun r => mean (affineLine a v r) v) (variance (affineLine a v t) v) t)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1.{u} := by exact @HiddenMonotonicity.SoftmaxDC.mean_line_derivative.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.mean_line_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.mean_line_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.mean_line_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.mean_line_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.mean_line_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.mean_line_derivative"
#check @HiddenMonotonicity.SoftmaxDC.mean_line_derivative
#print axioms _ThesisExactChecks.target_1

section
universe u
open HiddenMonotonicity.SoftmaxDC
def _ThesisExpectedTypes.type_2 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (a v : ι → ℝ) (t : ℝ) (i : ι), HasDerivAt (fun r => softmax (affineLine a v r) i) (softmax (affineLine a v t) i * (v i - mean (affineLine a v t) v)) t)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmax_line_derivative.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmax_line_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmax_line_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmax_line_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmax_line_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmax_line_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmax_line_derivative"
#check @HiddenMonotonicity.SoftmaxDC.softmax_line_derivative
#print axioms _ThesisExactChecks.target_2

section
universe u
open HiddenMonotonicity.SoftmaxDC
def _ThesisExpectedTypes.type_3 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (a v : ι → ℝ) (t : ℝ) (i : ι), HasDerivAt (fun r => softmax (affineLine a v r) i * (v i - mean (affineLine a v r) v)) (softmax (affineLine a v t) i * ((v i - mean (affineLine a v t) v) ^ 2 - variance (affineLine a v t) v)) t)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative"
#check @HiddenMonotonicity.SoftmaxDC.softmaxFirst_line_derivative
#print axioms _ThesisExactChecks.target_3

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (z : ι → ℝ), (∑ j, softmax z j) = 1)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmax_sum_one.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmax_sum_one
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmax_sum_one"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmax_sum_one | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmax_sum_one"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmax_sum_one: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmax_sum_one"
#check @HiddenMonotonicity.SoftmaxDC.softmax_sum_one
#print axioms _ThesisExactChecks.target_4

section
universe u
open HiddenMonotonicity.SoftmaxDC
def _ThesisExpectedTypes.type_5 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (z : ι → ℝ), 0 < expSum z)
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5.{u} := by exact @HiddenMonotonicity.SoftmaxDC.expSum_pos.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.expSum_pos
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.expSum_pos"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.expSum_pos | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxLineCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.expSum_pos"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.expSum_pos: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.expSum_pos"
#check @HiddenMonotonicity.SoftmaxDC.expSum_pos
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/softmax-dc/calculus-review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

