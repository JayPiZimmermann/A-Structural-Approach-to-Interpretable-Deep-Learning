import HiddenMonotonicity.TransformerConvexInput
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
universe u v
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_0 : Prop := (∀ {E : Type u} {ι : Type v} [AddCommGroup E] [Module ℝ E] (s : Set E), Convex ℝ s → ∀ φ : ((ι → ℝ) × (ι → ℝ)) → ℝ, ConvexOn ℝ (Set.Ici (0 : (ι → ℝ) × (ι → ℝ))) φ → MonotoneOn φ (Set.Ici (0 : (ι → ℝ) × (ι → ℝ))) → ∀ p q : E → ι → ℝ, (∀ i, ConvexOn ℝ s (fun x => p x i)) → (∀ i, ConvexOn ℝ s (fun x => q x i)) → (∀ x ∈ s, 0 ≤ p x) → (∀ x ∈ s, 0 ≤ q x) → ConvexOn ℝ s (fun x => φ (p x, q x)))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0.{u, v} := by exact @HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on.{u, v}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerConvexInput do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on"
#check @HiddenMonotonicity.TransformerDC.convex_monotone_vector_comp_on
#print axioms _ThesisExactChecks.target_0

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_1 : Prop := (∀ {ι : Type u} (φ : ((ι → ℝ) × (ι → ℝ)) → ℝ), ConvexOn ℝ (Set.Ici (0 : (ι → ℝ) × (ι → ℝ))) φ → MonotoneOn φ (Set.Ici (0 : (ι → ℝ) × (ι → ℝ))) → ConvexOn ℝ Set.univ (fun x : ι → ℝ => φ ((fun i => max (x i) 0), (fun i => max (-x i) 0))))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1.{u} := by exact @HiddenMonotonicity.TransformerDC.convex_signed_input_lift.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.convex_signed_input_lift
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.convex_signed_input_lift"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.convex_signed_input_lift | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerConvexInput do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.convex_signed_input_lift"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.convex_signed_input_lift: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.convex_signed_input_lift"
#check @HiddenMonotonicity.TransformerDC.convex_signed_input_lift
#print axioms _ThesisExactChecks.target_1

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/transformer-dc/convex-input/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

