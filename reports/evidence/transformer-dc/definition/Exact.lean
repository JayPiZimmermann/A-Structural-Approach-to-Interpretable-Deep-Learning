import HiddenMonotonicity.TransformerDefinition
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_0 : Prop := (∀ {t d : ℕ} {ι : Type u} (h : TransformerHead t d) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (q : Fin t) (i : Fin d), (h.compile x q i).eval v = h.eval (fun a b => (x a b).eval v) q i)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0.{u} := by exact @HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile"
#check @HiddenMonotonicity.TransformerDC.TransformerHead.eval_compile
#print axioms _ThesisExactChecks.target_0

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_1 : Prop := (∀ {t d : ℕ} {ι : Type u} (b : TransformerBlock t d) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (q : Fin t) (i : Fin d), (b.compile x q i).eval v = b.eval (fun a c => (x a c).eval v) q i)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1.{u} := by exact @HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile"
#check @HiddenMonotonicity.TransformerDC.TransformerBlock.eval_compile
#print axioms _ThesisExactChecks.target_1

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_2 : Prop := (∀ {t d : ℕ} {ι : Type u} (bs : List (TransformerBlock t d)) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (q : Fin t) (i : Fin d), (compileTransformerBlocks bs x q i).eval v = evalTransformerBlocks bs (fun a c => (x a c).eval v) q i)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2.{u} := by exact @HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks"
#check @HiddenMonotonicity.TransformerDC.eval_compileTransformerBlocks
#print axioms _ThesisExactChecks.target_2

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_3 : Prop := (∀ {t d : ℕ} {ι : Type u} (p : Option (TransformerNorm d)) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (q : Fin t) (i : Fin d), (compileOptionalTransformerNorm p x q i).eval v = evalOptionalTransformerNorm p (fun a c => (x a c).eval v) q i)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3.{u} := by exact @HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm"
#check @HiddenMonotonicity.TransformerDC.eval_compileOptionalTransformerNorm
#print axioms _ThesisExactChecks.target_3

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_4 : Prop := (∀ {t d o : ℕ} {ι : Type u} (net : Transformer t d o) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (i : Fin o), (net.compile x i).eval v = net.eval (fun p => (x p.1 p.2).eval v) i)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4.{u} := by exact @HiddenMonotonicity.TransformerDC.Transformer.eval_compile.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.eval_compile
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_compile"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.eval_compile | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_compile"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.eval_compile: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_compile"
#check @HiddenMonotonicity.TransformerDC.Transformer.eval_compile
#print axioms _ThesisExactChecks.target_4

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_5 : Prop := (∀ {t d o : ℕ} (net : Transformer t d o) (x : Fin t × Fin d → ℝ) (i : Fin o), (net.syntax i).eval x = net.eval x i)
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5 := by exact @HiddenMonotonicity.TransformerDC.Transformer.eval_syntax
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.eval_syntax
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_syntax"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.eval_syntax | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_syntax"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.eval_syntax: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval_syntax"
#check @HiddenMonotonicity.TransformerDC.Transformer.eval_syntax
#print axioms _ThesisExactChecks.target_5

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_6 := (∀ {t d : ℕ} (h : TransformerHead t d), (Fin t → Fin d → ℝ) → Fin t → Fin d → ℝ)
noncomputable def _ThesisExactChecks.target_6 : _ThesisExpectedTypes.type_6 := by exact @HiddenMonotonicity.TransformerDC.TransformerHead.eval
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.TransformerHead.eval
  let expected ← getConstInfo `_ThesisExactChecks.target_6
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.TransformerHead.eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_6) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.TransformerHead.eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.TransformerHead.eval"
#check @HiddenMonotonicity.TransformerDC.TransformerHead.eval
#print axioms _ThesisExactChecks.target_6

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_7 := (∀ {t d : ℕ} (b : TransformerBlock t d), (Fin t → Fin d → ℝ) → Fin t → Fin d → ℝ)
noncomputable def _ThesisExactChecks.target_7 : _ThesisExpectedTypes.type_7 := by exact @HiddenMonotonicity.TransformerDC.TransformerBlock.eval
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.TransformerBlock.eval
  let expected ← getConstInfo `_ThesisExactChecks.target_7
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.TransformerBlock.eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_7) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.TransformerBlock.eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.TransformerBlock.eval"
#check @HiddenMonotonicity.TransformerDC.TransformerBlock.eval
#print axioms _ThesisExactChecks.target_7

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_8 := (∀ {t d o : ℕ} (net : Transformer t d o), (Fin t × Fin d → ℝ) → Fin o → ℝ)
noncomputable def _ThesisExactChecks.target_8 : _ThesisExpectedTypes.type_8 := by exact @HiddenMonotonicity.TransformerDC.Transformer.eval
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.eval
  let expected ← getConstInfo `_ThesisExactChecks.target_8
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.eval | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_8) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.eval: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.eval"
#check @HiddenMonotonicity.TransformerDC.Transformer.eval
#print axioms _ThesisExactChecks.target_8

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_9 := (∀ {t d o : ℕ} (net : Transformer t d o), Fin o → Expr (Fin t × Fin d))
noncomputable def _ThesisExactChecks.target_9 : _ThesisExpectedTypes.type_9 := by exact @HiddenMonotonicity.TransformerDC.Transformer.syntax
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Transformer.syntax
  let expected ← getConstInfo `_ThesisExactChecks.target_9
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Transformer.syntax"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Transformer.syntax | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerDefinition do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Transformer.syntax"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_9) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Transformer.syntax: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Transformer.syntax"
#check @HiddenMonotonicity.TransformerDC.Transformer.syntax
#print axioms _ThesisExactChecks.target_9

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/transformer-dc/definition/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

