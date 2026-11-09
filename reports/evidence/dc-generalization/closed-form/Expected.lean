import HiddenMonotonicity.ClosedFormMonotoneDC
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_0 : Prop := (∀ x y : ℝ, ClosedFormActivation.relu.pair (x,y) = (max x y,y))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ClosedFormMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair"
#check @HiddenMonotonicity.SmoothDC.ClosedFormActivation.relu_pair
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_1 : Prop := (∀ a : ClosedFormActivation, ConvexPairActivation a.pair ∧ Monotone a.pair ∧ ValidPairActivation a.eval a.pair ∧ NonnegativePairActivation a.pair)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.SmoothDC.closed_form_activation_properties
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.closed_form_activation_properties
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.closed_form_activation_properties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.closed_form_activation_properties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ClosedFormMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.closed_form_activation_properties"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.closed_form_activation_properties: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.closed_form_activation_properties"
#check @HiddenMonotonicity.SmoothDC.closed_form_activation_properties
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_2 : Prop := (∀ {n m k : ℕ} (net : Network n m), net.Nonnegative → ∀ (a : ClosedFormActivation) (wp wn : Matrix (Fin k) (Fin m) ℝ), (∀ i j, 0 ≤ wp i j) → (∀ i j, 0 ≤ wn i j) → ∀ bp bn : Vec k, Monotone (net.affineDecomposeWith a.pair wp wn bp bn) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : PairVec n => (net.affineDecomposeWith a.pair wp wn bp bn x).1 i)) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : PairVec n => (net.affineDecomposeWith a.pair wp wn bp bn x).2 i)) ∧ ∀ x : PairVec n, (net.affineDecomposeWith a.pair wp wn bp bn x).1 - (net.affineDecomposeWith a.pair wp wn bp bn x).2 = affineLayer wp wn bp bn (net.forwardWith a.eval (x.1 - x.2)))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.SmoothDC.closed_form_affine_network
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.closed_form_affine_network
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_network"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.closed_form_affine_network | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ClosedFormMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_network"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.closed_form_affine_network: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_network"
#check @HiddenMonotonicity.SmoothDC.closed_form_affine_network
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
def _ThesisExpectedTypes.type_3 : Prop := (∀ {n m k : ℕ} (net : Network n m), net.Nonnegative → ∀ (a : ClosedFormActivation) (wp wn : Matrix (Fin k) (Fin m) ℝ), (∀ i j, 0 ≤ wp i j) → (∀ i j, 0 ≤ wn i j) → ∀ bp bn : Vec k, Monotone (fun x : Vec n => net.affineDecomposeWith a.pair wp wn bp bn (x,0)) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : Vec n => (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).1 i)) ∧ (∀ i, ConvexOn ℝ Set.univ (fun x : Vec n => (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).2 i)) ∧ ∀ x : Vec n, (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).1 - (net.affineDecomposeWith a.pair wp wn bp bn (x,0)).2 = affineLayer wp wn bp bn (net.forwardWith a.eval x))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.SmoothDC.closed_form_affine_dc
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.SmoothDC.closed_form_affine_dc
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_dc"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.SmoothDC.closed_form_affine_dc | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ClosedFormMonotoneDC do
    throwError "Defining module mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_dc"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.SmoothDC.closed_form_affine_dc: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.SmoothDC.closed_form_affine_dc"
#check @HiddenMonotonicity.SmoothDC.closed_form_affine_dc
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/dc-generalization/closed-form/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

