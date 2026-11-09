import HiddenMonotonicity.LayerNormDC
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
def _ThesisExpectedTypes.type_0 : Prop := (∀ {d : ℕ} (v : Fin d → ℝ), 0 ≤ HiddenMonotonicity.TransformerDC.layerVariance v)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.TransformerDC.layerVariance_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.layerVariance_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.layerVariance_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.layerVariance_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.layerVariance_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.layerVariance_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.layerVariance_nonnegative"
#check @HiddenMonotonicity.TransformerDC.layerVariance_nonnegative
#print axioms _ThesisExactChecks.target_0

section
def _ThesisExpectedTypes.type_1 : Prop := (∀ {d : ℕ} (xs : Fin d → ℝ × ℝ), HiddenMonotonicity.TransformerDC.value (HiddenMonotonicity.TransformerDC.variancePair xs) = HiddenMonotonicity.TransformerDC.layerVariance (fun i => HiddenMonotonicity.TransformerDC.value (xs i)))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.TransformerDC.value_variancePair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.value_variancePair
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.value_variancePair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.value_variancePair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.value_variancePair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.value_variancePair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.value_variancePair"
#check @HiddenMonotonicity.TransformerDC.value_variancePair
#print axioms _ThesisExactChecks.target_1

section
def _ThesisExpectedTypes.type_2 : Prop := (∀ {d : ℕ} (ε : ℝ), 0 < ε → ∀ (γ β : Fin d → ℝ) (xs : Fin d → ℝ × ℝ) (i : Fin d), HiddenMonotonicity.TransformerDC.value (HiddenMonotonicity.TransformerDC.layerNormPair ε γ β xs i) = HiddenMonotonicity.TransformerDC.layerNorm ε γ β (fun j => HiddenMonotonicity.TransformerDC.value (xs j)) i)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.TransformerDC.layerNormPair_exact
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.layerNormPair_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.layerNormPair_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.layerNormPair_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_exact"
#check @HiddenMonotonicity.TransformerDC.layerNormPair_exact
#print axioms _ThesisExactChecks.target_2

section
universe u
def _ThesisExpectedTypes.type_3 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {d : ℕ} (s : Set E), Convex ℝ s → ∀ ε : ℝ, 0 < ε → ∀ (γ β : Fin d → ℝ) (f : Fin d → E → ℝ × ℝ), (∀ i, HiddenMonotonicity.TransformerDC.Regular s (f i)) → ∀ i : Fin d, HiddenMonotonicity.TransformerDC.Regular s (fun x => HiddenMonotonicity.TransformerDC.layerNormPair ε γ β (fun j => f j x) i))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3.{u} := by exact @HiddenMonotonicity.TransformerDC.layerNormPair_regular.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.layerNormPair_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.layerNormPair_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.LayerNormDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.layerNormPair_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.layerNormPair_regular"
#check @HiddenMonotonicity.TransformerDC.layerNormPair_regular
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/transformer-dc/layernorm-assembly/review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

