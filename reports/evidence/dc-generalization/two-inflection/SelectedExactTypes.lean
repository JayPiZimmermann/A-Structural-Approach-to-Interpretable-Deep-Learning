import HiddenMonotonicity.TwoInflectionDC
import HiddenMonotonicity.ExplicitGELU
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_0 : Prop := (∀ (f d : ℝ → ℝ) (a b : ℝ), a < b → (∀ x, HasDerivAt f (d x) x) → AntitoneOn d (Set.Iic a) → MonotoneOn d (Set.Icc a b) → AntitoneOn d (Set.Ici b) → (∀ x, x ≤ a → d x ≤ 0) → (∀ x, b ≤ x → 0 ≤ d x) → ConvexOn ℝ Set.univ (asymmetricLift (centralConvexP f d a b) (d b - d a)) ∧ ConvexOn ℝ Set.univ (asymmetricLift (centralConvexQ f d a b) (d b - d a)) ∧ Monotone (asymmetricLift (centralConvexP f d a b) (d b - d a)) ∧ Monotone (asymmetricLift (centralConvexQ f d a b) (d b - d a)) ∧ ∀ z : ℝ × ℝ, asymmetricLift (centralConvexP f d a b) (d b - d a) z - asymmetricLift (centralConvexQ f d a b) (d b - d a) z = f (z.1 - z.2))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TwoInflectionDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split"
#check @HiddenMonotonicity.SmoothDC.centralConvex_asymmetric_split
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_1 : Prop := (ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).1) ∧ ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).2) ∧ Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).1) ∧ Monotone (fun z : ℝ × ℝ => (explicitGaussianGeluPair z).2) ∧ ValidPairActivation gaussianGelu explicitGaussianGeluPair ∧ NonnegativePairActivation explicitGaussianGeluPair)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitGELU do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split"
#check @HiddenMonotonicity.SmoothDC.gaussianGelu_explicit_split
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_2 : Prop := (∀ x y : ℝ, explicitGaussianGeluPair (x, y) = (2 * (gaussianGelu (x - y) + standardGaussianDensity (x - y)) + 2 * y, gaussianGelu (x - y) + 2 * standardGaussianDensity (x - y) + 2 * y))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ExplicitGELU do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula"
#check @HiddenMonotonicity.SmoothDC.explicitGaussianGeluPair_formula
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_3 : Prop := (∀ {x : ℝ}, -Real.sqrt 2 ≤ x ∧ x ≤ Real.sqrt 2 → gaussianGeluFirst (-Real.sqrt 2) ≤ gaussianGeluFirst x ∧ gaussianGeluFirst x ≤ gaussianGeluFirst (Real.sqrt 2))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.GELUInflectionBounds do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds"
#check @HiddenMonotonicity.SmoothDC.gaussianGeluFirst_middle_bounds
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/dc-generalization/two-inflection/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

