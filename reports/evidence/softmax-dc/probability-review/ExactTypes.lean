import HiddenMonotonicity.SoftmaxProbability
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_0 : Prop := (∀ {ι : Type u} [Fintype ι] (p : ι → ℝ), (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 → ∀ (w : ι → ℝ), (∀ j, 0 ≤ w j) → ∀ i, -(∑ j, p j * w j) ≤ p i * (w i - ∑ j, p j * w j) ∧ p i * (w i - ∑ j, p j * w j) ≤ ∑ j, p j * w j)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0.{u} := by exact @HiddenMonotonicity.SoftmaxDC.probability_second_bounds.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.probability_second_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.probability_second_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.probability_second_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.probability_second_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.probability_second_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.probability_second_bounds"
#check @HiddenMonotonicity.SoftmaxDC.probability_second_bounds
#print axioms _ThesisExactChecks.target_0

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_1 : Prop := (∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (p : ι → ℝ), (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 → ∀ i j, 0 ≤ (p j + p i * ((if i = j then 1 else 0) - p j)) / 2 ∧ (p j + p i * ((if i = j then 1 else 0) - p j)) / 2 ≤ (1 : ℝ) / 2)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1.{u} := by exact @HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds"
#check @HiddenMonotonicity.SoftmaxDC.plusCoeff_bounds
#print axioms _ThesisExactChecks.target_1

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_2 : Prop := (∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (p : ι → ℝ), (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 → ∀ i j, 0 ≤ (p j - p i * ((if i = j then 1 else 0) - p j)) / 2 ∧ (p j - p i * ((if i = j then 1 else 0) - p j)) / 2 ≤ (1 : ℝ) / 2)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2.{u} := by exact @HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds"
#check @HiddenMonotonicity.SoftmaxDC.minusCoeff_bounds
#print axioms _ThesisExactChecks.target_2

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_3 : Prop := (∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (p v : ι → ℝ) (i : ι), (∑ j, ((p j + p i * ((if i = j then 1 else 0) - p j)) / 2) * v j) = ((∑ j, p j * v j) + p i * (v i - ∑ j, p j * v j)) / 2)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3.{u} := by exact @HiddenMonotonicity.SoftmaxDC.plusCoeff_sum.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.plusCoeff_sum
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_sum"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.plusCoeff_sum | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_sum"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.plusCoeff_sum: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.plusCoeff_sum"
#check @HiddenMonotonicity.SoftmaxDC.plusCoeff_sum
#print axioms _ThesisExactChecks.target_3

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (p v : ι → ℝ) (i : ι), (∑ j, ((p j - p i * ((if i = j then 1 else 0) - p j)) / 2) * v j) = ((∑ j, p j * v j) - p i * (v i - ∑ j, p j * v j)) / 2)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4.{u} := by exact @HiddenMonotonicity.SoftmaxDC.minusCoeff_sum.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.minusCoeff_sum
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_sum"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.minusCoeff_sum | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_sum"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.minusCoeff_sum: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.minusCoeff_sum"
#check @HiddenMonotonicity.SoftmaxDC.minusCoeff_sum
#print axioms _ThesisExactChecks.target_4

section
universe u
open scoped BigOperators
def _ThesisExpectedTypes.type_5 : Prop := (∀ {ι : Type u} [Fintype ι] (c v : ι → ℝ), (∀ j, 0 ≤ c j ∧ c j ≤ (1 : ℝ) / 2) → (∀ j, 0 ≤ v j) → 0 ≤ ∑ j, c j * v j ∧ (∑ j, c j * v j) ≤ (∑ j, v j) / 2)
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5.{u} := by exact @HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.SoftmaxProbability do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds"
#check @HiddenMonotonicity.SoftmaxDC.coeff_direction_bounds
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/softmax-dc/probability-review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

