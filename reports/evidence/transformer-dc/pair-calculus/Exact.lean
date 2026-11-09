import HiddenMonotonicity.TransformerPairCalculus
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_0 : Prop := (∀ c : ℝ, value (constPair c) = c)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.TransformerDC.value_constPair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.value_constPair
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.value_constPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.value_constPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.value_constPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.value_constPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.value_constPair"
#check @HiddenMonotonicity.TransformerDC.value_constPair
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_1 : Prop := (∀ p q : ℝ × ℝ, value (addPair p q) = value p + value q)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.TransformerDC.value_addPair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.value_addPair
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.value_addPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.value_addPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.value_addPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.value_addPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.value_addPair"
#check @HiddenMonotonicity.TransformerDC.value_addPair
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_2 : Prop := (∀ (c : ℝ) (p : ℝ × ℝ), value (scalePair c p) = c * value p)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.TransformerDC.value_scalePair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.value_scalePair
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.value_scalePair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.value_scalePair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.value_scalePair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.value_scalePair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.value_scalePair"
#check @HiddenMonotonicity.TransformerDC.value_scalePair
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_3 : Prop := (∀ p q : ℝ × ℝ, value (mulPair p q) = value p * value q)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.TransformerDC.value_mulPair
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.value_mulPair
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.value_mulPair"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.value_mulPair | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.value_mulPair"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.value_mulPair: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.value_mulPair"
#check @HiddenMonotonicity.TransformerDC.value_mulPair
#print axioms _ThesisExactChecks.target_3

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_4 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, Convex ℝ s → ∀ c : ℝ, Regular s (fun _ : E => constPair c))
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4.{u} := by exact @HiddenMonotonicity.TransformerDC.Regular.const.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.const
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.const"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.const | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.const"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.const: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.const"
#check @HiddenMonotonicity.TransformerDC.Regular.const
#print axioms _ThesisExactChecks.target_4

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_5 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, ∀ {f : E → ℝ × ℝ}, Regular s f → ∀ c : ℝ, Regular s (fun x => scalePair c (f x)))
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5.{u} := by exact @HiddenMonotonicity.TransformerDC.Regular.scale.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.scale
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.scale"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.scale | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.scale"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.scale: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.scale"
#check @HiddenMonotonicity.TransformerDC.Regular.scale
#print axioms _ThesisExactChecks.target_5

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_6 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, ∀ {f g : E → ℝ × ℝ}, Regular s f → Regular s g → Regular s (fun x => mulPair (f x) (g x)))
theorem _ThesisExactChecks.target_6 : _ThesisExpectedTypes.type_6.{u} := by exact @HiddenMonotonicity.TransformerDC.Regular.mul.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.mul
  let expected ← getConstInfo `_ThesisExactChecks.target_6
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.mul"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.mul | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.mul"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_6) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.mul: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.mul"
#check @HiddenMonotonicity.TransformerDC.Regular.mul
#print axioms _ThesisExactChecks.target_6

section
universe u v
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_7 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, ∀ {ι : Type v} (t : Finset ι) (f : ι → E → ℝ × ℝ), Convex ℝ s → (∀ i ∈ t, Regular s (f i)) → Regular s (fun x => ∑ i ∈ t, f i x))
theorem _ThesisExactChecks.target_7 : _ThesisExpectedTypes.type_7.{u, v} := by exact @HiddenMonotonicity.TransformerDC.Regular.finset_sum.{u, v}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.finset_sum
  let expected ← getConstInfo `_ThesisExactChecks.target_7
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.finset_sum"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.finset_sum | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.finset_sum"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_7) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.finset_sum: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.finset_sum"
#check @HiddenMonotonicity.TransformerDC.Regular.finset_sum
#print axioms _ThesisExactChecks.target_7

section
universe u
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_8 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, ∀ {f : E → ℝ × ℝ}, Regular s f → ∀ φ : (ℝ × ℝ) → ℝ × ℝ, ConvexOn ℝ Set.univ (fun z => (φ z).1) → ConvexOn ℝ Set.univ (fun z => (φ z).2) → Monotone φ → (∀ z, 0 ≤ z → 0 ≤ φ z) → Regular s (fun x => φ (f x)))
theorem _ThesisExactChecks.target_8 : _ThesisExpectedTypes.type_8.{u} := by exact @HiddenMonotonicity.TransformerDC.Regular.scalar_comp.{u}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.scalar_comp
  let expected ← getConstInfo `_ThesisExactChecks.target_8
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.scalar_comp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.scalar_comp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.scalar_comp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_8) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.scalar_comp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.scalar_comp"
#check @HiddenMonotonicity.TransformerDC.Regular.scalar_comp
#print axioms _ThesisExactChecks.target_8

section
universe u v
open HiddenMonotonicity.TransformerDC
def _ThesisExpectedTypes.type_9 : Prop := (∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E] {s : Set E}, ∀ {ι : Type v} (φ : ((ι → ℝ) × (ι → ℝ)) → ℝ × ℝ), ConvexOn ℝ Set.univ (fun z => (φ z).1) → ConvexOn ℝ Set.univ (fun z => (φ z).2) → Monotone φ → (∀ z, 0 ≤ z → 0 ≤ φ z) → Convex ℝ s → ∀ f : ι → E → ℝ × ℝ, (∀ i, Regular s (f i)) → Regular s (fun x => φ ((fun i => (f i x).1), (fun i => (f i x).2))))
theorem _ThesisExactChecks.target_9 : _ThesisExpectedTypes.type_9.{u, v} := by exact @HiddenMonotonicity.TransformerDC.Regular.vector_comp.{u, v}
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.TransformerDC.Regular.vector_comp
  let expected ← getConstInfo `_ThesisExactChecks.target_9
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: HiddenMonotonicity.TransformerDC.Regular.vector_comp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.TransformerDC.Regular.vector_comp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.TransformerPairCalculus do
    throwError "Defining module mismatch: HiddenMonotonicity.TransformerDC.Regular.vector_comp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_9) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.TransformerDC.Regular.vector_comp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.TransformerDC.Regular.vector_comp"
#check @HiddenMonotonicity.TransformerDC.Regular.vector_comp
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/transformer-dc/pair-calculus/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

