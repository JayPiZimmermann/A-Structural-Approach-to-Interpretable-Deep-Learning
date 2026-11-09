import Thesis.AttentionReference
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
def _ThesisExpectedTypes.type_0 : Prop := (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (p : Policy A) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i),
objective reference contribution p = sourceValue 1 (mass reference contribution) p)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0.{u} := by exact @Thesis.AttentionReference.objective_eq_sourceValue.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionReference.objective_eq_sourceValue
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.AttentionReference.objective_eq_sourceValue"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionReference.objective_eq_sourceValue | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionReference do
    throwError "Defining module mismatch: Thesis.AttentionReference.objective_eq_sourceValue"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionReference.objective_eq_sourceValue: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionReference.objective_eq_sourceValue"
#check @Thesis.AttentionReference.objective_eq_sourceValue
#print axioms _ThesisExactChecks.target_0

section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
def _ThesisExpectedTypes.type_1 : Prop := (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) (hz : 0 < ∑ i, mass reference contribution i),
objective reference contribution (valuePolicy reference contribution hr hc hz) = (Real.log (∑ i, reference i * contribution i) : WithBot ℝ))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1.{u} := by exact @Thesis.AttentionReference.valuePolicy_value.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionReference.valuePolicy_value
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.AttentionReference.valuePolicy_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionReference.valuePolicy_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionReference do
    throwError "Defining module mismatch: Thesis.AttentionReference.valuePolicy_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionReference.valuePolicy_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionReference.valuePolicy_value"
#check @Thesis.AttentionReference.valuePolicy_value
#print axioms _ThesisExactChecks.target_1

section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
def _ThesisExpectedTypes.type_2 : Prop := (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (p : Policy A) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) (hz : 0 < ∑ i, mass reference contribution i),
objective reference contribution p = (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ↔ p.prob = (valuePolicy reference contribution hr hc hz).prob)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2.{u} := by exact @Thesis.AttentionReference.valuePolicy_unique.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionReference.valuePolicy_unique
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.AttentionReference.valuePolicy_unique"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionReference.valuePolicy_unique | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionReference do
    throwError "Defining module mismatch: Thesis.AttentionReference.valuePolicy_unique"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionReference.valuePolicy_unique: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionReference.valuePolicy_unique"
#check @Thesis.AttentionReference.valuePolicy_unique
#print axioms _ThesisExactChecks.target_2

section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
def _ThesisExpectedTypes.type_3 : Prop := (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (p : Policy A) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i)
(hz : (∑ i, reference i * contribution i) = 0),
objective reference contribution p = ⊥)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3.{u} := by exact @Thesis.AttentionReference.zero_mass_value.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionReference.zero_mass_value
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.AttentionReference.zero_mass_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionReference.zero_mass_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionReference do
    throwError "Defining module mismatch: Thesis.AttentionReference.zero_mass_value"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionReference.zero_mass_value: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionReference.zero_mass_value"
#check @Thesis.AttentionReference.zero_mass_value
#print axioms _ThesisExactChecks.target_3

section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
def _ThesisExpectedTypes.type_4 : Prop := (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) (hz : 0 < ∑ i, mass reference contribution i),
IsGreatest (Set.range (objective reference contribution)) (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ∧
(∀ p : Policy A, objective reference contribution p = (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ↔ p.prob = (valuePolicy reference contribution hr hc hz).prob) ∧
(∀ i, (valuePolicy reference contribution hr hc hz).prob i = reference i * contribution i / ∑ j, reference j * contribution j))
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4.{u} := by exact @Thesis.AttentionReference.attention_value_routing.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionReference.attention_value_routing
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.AttentionReference.attention_value_routing"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionReference.attention_value_routing | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionReference do
    throwError "Defining module mismatch: Thesis.AttentionReference.attention_value_routing"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.AttentionReference.attention_value_routing: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionReference.attention_value_routing"
#check @Thesis.AttentionReference.attention_value_routing
#print axioms _ThesisExactChecks.target_4

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/dc_decompose/master_thesis/reports/evidence/attention-reference/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

