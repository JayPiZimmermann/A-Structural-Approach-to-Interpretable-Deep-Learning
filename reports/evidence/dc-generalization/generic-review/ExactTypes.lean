import HiddenMonotonicity.MonotoneDCLift
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_0 : Prop := (∀ (C : ℝ → ℝ) (L : ℝ), ConvexOn ℝ Set.univ (asymmetricLift C L) ↔ ConvexOn ℝ Set.univ C)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff"
#check @HiddenMonotonicity.SmoothDC.asymmetricLift_convex_iff
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_1 : Prop := (∀ (C : ℝ → ℝ) (L : ℝ), Monotone (asymmetricLift C L) ↔ ∀ a b : ℝ, a ≤ b → 0 ≤ C b - C a ∧ C b - C a ≤ L * (b - a))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments"
#check @HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff_increments
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_2 : Prop := (∀ (C D : ℝ → ℝ) (hC : ∀ x : ℝ, HasDerivAt C (D x) x) (L : ℝ), Monotone (asymmetricLift C L) ↔ ∀ x : ℝ, 0 ≤ D x ∧ D x ≤ L)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff"
#check @HiddenMonotonicity.SmoothDC.asymmetricLift_monotone_iff
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_3 : Prop := (∀ (P Q f : ℝ → ℝ) (L : ℝ) (hP : ConvexOn ℝ Set.univ P) (hQ : ConvexOn ℝ Set.univ Q) (hPd : ∀ a b : ℝ, a ≤ b → 0 ≤ P b - P a ∧ P b - P a ≤ L * (b - a)) (hQd : ∀ a b : ℝ, a ≤ b → 0 ≤ Q b - Q a ∧ Q b - Q a ≤ L * (b - a)) (hdiff : ∀ t : ℝ, P t - Q t = f t), ConvexOn ℝ Set.univ (asymmetricLift P L) ∧ ConvexOn ℝ Set.univ (asymmetricLift Q L) ∧ Monotone (asymmetricLift P L) ∧ Monotone (asymmetricLift Q L) ∧ ∀ z : ℝ × ℝ, asymmetricLift P L z - asymmetricLift Q L z = f (z.1 - z.2))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.SmoothDC.asymmetric_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetric_split
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetric_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetric_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetric_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetric_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetric_split"
#check @HiddenMonotonicity.SmoothDC.asymmetric_split
#print axioms _ThesisExactChecks.target_3

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_4 : Prop := (∀ (C : ℝ → ℝ) (L x y c : ℝ), asymmetricLift C L (x + c, y + c) = asymmetricLift C L (x, y) + L * c)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift"
#check @HiddenMonotonicity.SmoothDC.asymmetricLift_common_shift
#print axioms _ThesisExactChecks.target_4

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_5 : Prop := (∀ z : ℝ × ℝ, asymmetricLift relu 1 z = max z.1 z.2 ∧ asymmetricLift (fun _ : ℝ => 0) 1 z = z.2)
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5 := by exact @HiddenMonotonicity.SmoothDC.asymmetricLift_relu
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.asymmetricLift_relu
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_relu"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.asymmetricLift_relu | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_relu"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.asymmetricLift_relu: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.asymmetricLift_relu"
#check @HiddenMonotonicity.SmoothDC.asymmetricLift_relu
#print axioms _ThesisExactChecks.target_5

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_6 : Prop := (ConvexOn ℝ Set.univ (asymmetricLift relu 1) ∧ ConvexOn ℝ Set.univ (asymmetricLift (fun _ : ℝ => 0) 1) ∧ Monotone (asymmetricLift relu 1) ∧ Monotone (asymmetricLift (fun _ : ℝ => 0) 1) ∧ ∀ z : ℝ × ℝ, asymmetricLift relu 1 z - asymmetricLift (fun _ : ℝ => 0) 1 z = relu (z.1 - z.2))
theorem _ThesisExactChecks.target_6 : _ThesisExpectedTypes.type_6 := by exact @HiddenMonotonicity.SmoothDC.relu_asymmetric_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.relu_asymmetric_split
  let expected ← getConstInfo `_ThesisExactChecks.target_6
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.relu_asymmetric_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.relu_asymmetric_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.MonotoneDCLift do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.relu_asymmetric_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_6) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.relu_asymmetric_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.relu_asymmetric_split"
#check @HiddenMonotonicity.SmoothDC.relu_asymmetric_split
#print axioms _ThesisExactChecks.target_6

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/dc-generalization/generic-review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

