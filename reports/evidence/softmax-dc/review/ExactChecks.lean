import HiddenMonotonicity.ExplicitSoftmax
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_0 : Prop := (∀ {ι : Type u} [Fintype ι] [Nonempty ι] (i : ι),
ConvexOn ℝ Set.univ (softmaxSplitFirst i) ∧
ConvexOn ℝ Set.univ (softmaxSplitSecond i) ∧
Monotone (softmaxSplitFirst i) ∧ Monotone (softmaxSplitSecond i) ∧
(∀ z : (ι → ℝ) × (ι → ℝ), softmaxSplitFirst i z - softmaxSplitSecond i z = softmax (z.1-z.2) i) ∧
(∀ z : (ι → ℝ) × (ι → ℝ), 0 ≤ z → 0 ≤ softmaxSplitFirst i z ∧ 0 ≤ softmaxSplitSecond i z))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmax_split_properties.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmax_split_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmax_split_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmax_split_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmax_split_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmax_split_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmax_split_properties"
#check @HiddenMonotonicity.SoftmaxDC.softmax_split_properties
#print axioms _ThesisExactChecks.target_0

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_1 : Prop := (∀ {ι : Type u} [Fintype ι] (i : ι) (x y : ι → ℝ),
softmaxSplitFirst i (x,y) =
(Real.log (∑ j, Real.exp (x j-y j)) + Real.exp (x i-y i)/(∑ j, Real.exp (x j-y j)) + ∑ j, y j)/2 -
(Real.log (Fintype.card ι)-1/Fintype.card ι)/2)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula"
#check @HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_formula
#print axioms _ThesisExactChecks.target_1

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_2 : Prop := (∀ {ι : Type u} [Fintype ι] (i : ι) (x y : ι → ℝ),
softmaxSplitSecond i (x,y) =
(Real.log (∑ j, Real.exp (x j-y j)) - Real.exp (x i-y i)/(∑ j, Real.exp (x j-y j)) + ∑ j, y j)/2 -
(Real.log (Fintype.card ι)-1/Fintype.card ι)/2)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula"
#check @HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_formula
#print axioms _ThesisExactChecks.target_2

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_3 : Prop := (∀ {ι : Type u} [Fintype ι] (i : ι) (z : (ι → ℝ) × (ι → ℝ)),
softmaxSplitFirst i z-softmaxSplitSecond i z=softmax (z.1-z.2) i)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference"
#check @HiddenMonotonicity.SoftmaxDC.softmaxSplit_difference
#print axioms _ThesisExactChecks.target_3

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {ι : Type u} [Fintype ι] (i : ι), softmaxSplitFirst i 0=1/Fintype.card ι)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero"
#check @HiddenMonotonicity.SoftmaxDC.softmaxSplitFirst_zero
#print axioms _ThesisExactChecks.target_4

section
universe u
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
def _ThesisExpectedTypes.type_5 : Prop := (∀ {ι : Type u} [Fintype ι] (i : ι), softmaxSplitSecond i 0=0)
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5.{u} := by exact @HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitSoftmax do
    throwError "Defining module mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero"
#check @HiddenMonotonicity.SoftmaxDC.softmaxSplitSecond_zero
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/softmax-dc/review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

