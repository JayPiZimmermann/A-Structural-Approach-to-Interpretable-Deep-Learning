import HiddenMonotonicity.TransformerExpr
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
universe u
def _ThesisExpectedTypes.type_0 : Prop := (∀ {ι : Type u} (e : HiddenMonotonicity.TransformerDC.Expr ι) (x : ι → ℝ × ℝ), HiddenMonotonicity.TransformerDC.value (e.splitEval x) = e.eval (fun i => HiddenMonotonicity.TransformerDC.value (x i)))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0.{u} := by exact @HiddenMonotonicity.TransformerDC.Expr.splitEval_exact.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.splitEval_exact
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_exact"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.splitEval_exact | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExpr do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_exact"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.splitEval_exact: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_exact"
#check @HiddenMonotonicity.TransformerDC.Expr.splitEval_exact
#print axioms _ThesisExactChecks.target_0

section
universe u v
def _ThesisExpectedTypes.type_1 : Prop := (∀ {ι : Type u} {E : Type v} [AddCommGroup E] [Module ℝ E] [Preorder E] (e : HiddenMonotonicity.TransformerDC.Expr ι) (s : Set E), Convex ℝ s → ∀ (f : ι → E → ℝ × ℝ), (∀ i, HiddenMonotonicity.TransformerDC.Regular s (f i)) → HiddenMonotonicity.TransformerDC.Regular s (fun x => e.splitEval (fun i => f i x)))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1.{u, v} := by exact @HiddenMonotonicity.TransformerDC.Expr.splitEval_regular.{u, v}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Expr.splitEval_regular
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_regular"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Expr.splitEval_regular | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerExpr do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_regular"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Expr.splitEval_regular: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Expr.splitEval_regular"
#check @HiddenMonotonicity.TransformerDC.Expr.splitEval_regular
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/transformer-dc/expr-review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

