import HiddenMonotonicity.PolarizedProductDC
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
def _ThesisExpectedTypes.type_0 : Prop := (∀ z : HiddenMonotonicity.TransformerDC.FourStreams, (HiddenMonotonicity.TransformerDC.productSplit z).1 - (HiddenMonotonicity.TransformerDC.productSplit z).2 = (z.1.1 - z.1.2) * (z.2.1 - z.2.2))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.TransformerDC.productSplit_exact
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_exact"
#check @HiddenMonotonicity.TransformerDC.productSplit_exact
#print axioms _ThesisExactChecks.target_0

section
def _ThesisExpectedTypes.type_1 : Prop := (∀ z : HiddenMonotonicity.TransformerDC.FourStreams, 0 ≤ HiddenMonotonicity.TransformerDC.productSplit z)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.TransformerDC.productSplit_nonnegative
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_nonnegative"
#check @HiddenMonotonicity.TransformerDC.productSplit_nonnegative
#print axioms _ThesisExactChecks.target_1

section
def _ThesisExpectedTypes.type_2 : Prop := (ConvexOn ℝ Set.univ (fun z : HiddenMonotonicity.TransformerDC.FourStreams => (HiddenMonotonicity.TransformerDC.productSplit z).1) ∧ ConvexOn ℝ Set.univ (fun z : HiddenMonotonicity.TransformerDC.FourStreams => (HiddenMonotonicity.TransformerDC.productSplit z).2))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.TransformerDC.productSplit_convex
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex"
#check @HiddenMonotonicity.TransformerDC.productSplit_convex
#print axioms _ThesisExactChecks.target_2

section
def _ThesisExpectedTypes.type_3 : Prop := (MonotoneOn HiddenMonotonicity.TransformerDC.productSplit (Set.Ici (0 : HiddenMonotonicity.TransformerDC.FourStreams)))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.TransformerDC.productSplit_monotoneOn
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_monotoneOn
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotoneOn"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_monotoneOn | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotoneOn"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_monotoneOn: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotoneOn"
#check @HiddenMonotonicity.TransformerDC.productSplit_monotoneOn
#print axioms _ThesisExactChecks.target_3

section
universe u
def _ThesisExpectedTypes.type_4 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (s : Set E) (A B C D : E → ℝ), ConvexOn ℝ s A → ConvexOn ℝ s B → ConvexOn ℝ s C → ConvexOn ℝ s D → (∀ x ∈ s, 0 ≤ A x) → (∀ x ∈ s, 0 ≤ B x) → (∀ x ∈ s, 0 ≤ C x) → (∀ x ∈ s, 0 ≤ D x) → ConvexOn ℝ s (fun x => (HiddenMonotonicity.TransformerDC.productSplit ((A x, B x), (C x, D x))).1) ∧ ConvexOn ℝ s (fun x => (HiddenMonotonicity.TransformerDC.productSplit ((A x, B x), (C x, D x))).2))
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4.{u} := by exact @HiddenMonotonicity.TransformerDC.productSplit_convex_composition.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_convex_composition
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex_composition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_convex_composition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex_composition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_convex_composition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_convex_composition"
#check @HiddenMonotonicity.TransformerDC.productSplit_convex_composition
#print axioms _ThesisExactChecks.target_4

section
universe u
def _ThesisExpectedTypes.type_5 : Prop := (∀ {E : Type u} [Preorder E] (s : Set E) (A B C D : E → ℝ), MonotoneOn A s → MonotoneOn B s → MonotoneOn C s → MonotoneOn D s → (∀ x ∈ s, 0 ≤ A x) → (∀ x ∈ s, 0 ≤ B x) → (∀ x ∈ s, 0 ≤ C x) → (∀ x ∈ s, 0 ≤ D x) → MonotoneOn (fun x => HiddenMonotonicity.TransformerDC.productSplit ((A x, B x), (C x, D x))) s)
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5.{u} := by exact @HiddenMonotonicity.TransformerDC.productSplit_monotone_composition.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.productSplit_monotone_composition
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotone_composition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.productSplit_monotone_composition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.PolarizedProductDC do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotone_composition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.productSplit_monotone_composition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.productSplit_monotone_composition"
#check @HiddenMonotonicity.TransformerDC.productSplit_monotone_composition
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/transformer-dc/product/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

