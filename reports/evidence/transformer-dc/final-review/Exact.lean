import HiddenMonotonicity.TransformerCorrectness
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_0 : Prop := (∀ {t d o : ℕ} (net : Transformer t d o) (x : DoubledInput (Fin t × Fin d)) (i : Fin o),
  (net.decompose x i).1 - (net.decompose x i).2 = net.eval (x.1 - x.2) i)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.TransformerDC.Transformer.decompose_exact
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.decompose_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.decompose_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerCorrectness do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.decompose_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_exact"
#check @HiddenMonotonicity.TransformerDC.Transformer.decompose_exact
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_1 : Prop := (∀ {t d o : ℕ} (net : Transformer t d o) (i : Fin o),
  Regular (Set.Ici (0 : DoubledInput (Fin t × Fin d))) (fun x => net.decompose x i))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.TransformerDC.Transformer.decompose_regular
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.decompose_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.decompose_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerCorrectness do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.decompose_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.decompose_regular"
#check @HiddenMonotonicity.TransformerDC.Transformer.decompose_regular
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_2 : Prop := (∀ {t d o : ℕ} (net : Transformer t d o),
  MonotoneOn net.decompose (Set.Ici (0 : DoubledInput (Fin t × Fin d))) ∧
  (∀ i, ConvexOn ℝ (Set.Ici (0 : DoubledInput (Fin t × Fin d))) (fun x => (net.decompose x i).1)) ∧
  (∀ i, ConvexOn ℝ (Set.Ici (0 : DoubledInput (Fin t × Fin d))) (fun x => (net.decompose x i).2)) ∧
  (∀ x, 0 ≤ x → 0 ≤ net.decompose x) ∧
  ∀ x i, (net.decompose x i).1 - (net.decompose x i).2 = net.eval (x.1 - x.2) i)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerCorrectness do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition"
#check @HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_3 : Prop := (∀ {t d o : ℕ} (net : Transformer t d o),
  (∀ i, ConvexOn ℝ Set.univ (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).1)) ∧
  (∀ i, ConvexOn ℝ Set.univ (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).2)) ∧
  (∀ x, 0 ≤ net.rawDecompose x) ∧
  ∀ x i, (net.rawDecompose x i).1 - (net.rawDecompose x i).2 = net.eval x i)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerCorrectness do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition"
#check @HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition
#print axioms _ThesisExactChecks.target_3

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_4 : Prop := (∀ {ι : Type u} (e : Expr ι), Regular (Set.Ici (0 : DoubledInput ι)) e.decompose)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4.{u} := by exact @HiddenMonotonicity.TransformerDC.Expr.decompose_regular.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.decompose_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.decompose_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExprProperties do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.decompose_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_regular"
#check @HiddenMonotonicity.TransformerDC.Expr.decompose_regular
#print axioms _ThesisExactChecks.target_4

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_5 : Prop := (∀ {ι : Type u} (e : Expr ι) (x : DoubledInput ι), value (e.decompose x) = e.eval (x.1 - x.2))
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5.{u} := by exact @HiddenMonotonicity.TransformerDC.Expr.decompose_exact.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.decompose_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.decompose_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExprProperties do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.decompose_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.decompose_exact"
#check @HiddenMonotonicity.TransformerDC.Expr.decompose_exact
#print axioms _ThesisExactChecks.target_5

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_6 : Prop := (∀ {ι : Type u} (e : Expr ι),
  ConvexOn ℝ Set.univ (fun x : ι → ℝ => (e.rawDecompose x).1) ∧
  ConvexOn ℝ Set.univ (fun x : ι → ℝ => (e.rawDecompose x).2))
theorem _ThesisExactChecks.target_6 : _ThesisExpectedTypes.type_6.{u} := by exact @HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex
  let expected ← getConstInfo `_ThesisExactChecks.target_6
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExprProperties do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_6) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex"
#check @HiddenMonotonicity.TransformerDC.Expr.rawDecompose_convex
#print axioms _ThesisExactChecks.target_6

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_7 : Prop := (∀ {ι : Type u} (e : Expr ι) (x : ι → ℝ), value (e.rawDecompose x) = e.eval x)
theorem _ThesisExactChecks.target_7 : _ThesisExpectedTypes.type_7.{u} := by exact @HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_7
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExprProperties do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_7) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact"
#check @HiddenMonotonicity.TransformerDC.Expr.rawDecompose_exact
#print axioms _ThesisExactChecks.target_7

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/transformer-dc/final-review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

