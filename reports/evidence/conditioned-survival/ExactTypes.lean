import Thesis.ConditionedSurvival
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_0 : Prop := (∀ {S : Type} [Fintype S] (n : ℕ) (K : ℕ → S → S → ℝ)
(h : ℕ → S → ℝ) (hK : ∀ i s t, 0 ≤ K i s t)
(hh : ∀ i s, 0 ≤ h i s)
(hrec : ∀ i < n, ∀ s, h i s = ∑ t, K i s t * h (i+1) t)
(s : S) (path : Paths S n),
pathLaw n (kernel K h) s path * h 0 s =
pathLaw n K s path * h n (endpoint n s path))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @Thesis.ConditionedSurvival.weighted_path_identity
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.weighted_path_identity
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.weighted_path_identity"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.weighted_path_identity | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.weighted_path_identity"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.weighted_path_identity: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.weighted_path_identity"
#check @Thesis.ConditionedSurvival.weighted_path_identity
#print axioms _ThesisExactChecks.target_0

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_1 : Prop := (∀ {S : Type} (n : ℕ) (K : ℕ → S → S → ℝ)
(h : ℕ → S → ℝ) (hh : ∀ i s, 0 ≤ h i s)
(s : S) (hs : 0 < h 0 s) (path : Paths S n) (i : ℕ) (hi : i ≤ n)
(hz : h i (stateAt n s path i) = 0),
pathLaw n (kernel K h) s path = 0)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @Thesis.ConditionedSurvival.path_zero_at_zero_potential
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.path_zero_at_zero_potential
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.path_zero_at_zero_potential"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.path_zero_at_zero_potential | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.path_zero_at_zero_potential"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.path_zero_at_zero_potential: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.path_zero_at_zero_potential"
#check @Thesis.ConditionedSurvival.path_zero_at_zero_potential
#print axioms _ThesisExactChecks.target_1

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_2 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ)
(i : ℕ) (hi : i < N) (s : S),
survival N K i s = ∑ t, K i s t * survival N K (i+1) t)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @Thesis.ConditionedSurvival.survival_recurrence
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.survival_recurrence
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.survival_recurrence"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.survival_recurrence | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.survival_recurrence"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.survival_recurrence: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.survival_recurrence"
#check @Thesis.ConditionedSurvival.survival_recurrence
#print axioms _ThesisExactChecks.target_2

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_3 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ) (s : S),
survival N K 0 s = ∑ path : Paths S N, pathLaw N K s path)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @Thesis.ConditionedSurvival.survival_eq_path_mass
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.survival_eq_path_mass
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.survival_eq_path_mass"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.survival_eq_path_mass | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.survival_eq_path_mass"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.survival_eq_path_mass: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.survival_eq_path_mass"
#check @Thesis.ConditionedSurvival.survival_eq_path_mass
#print axioms _ThesisExactChecks.target_3

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ)
(hK : ∀ i s t, 0 ≤ K i s t) (s : S) (hs : survival N K 0 s = 0)
(path : Paths S N), pathLaw N K s path = 0)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @Thesis.ConditionedSurvival.survival_zero_path
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.survival_zero_path
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.survival_zero_path"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.survival_zero_path | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.survival_zero_path"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.survival_zero_path: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.survival_zero_path"
#check @Thesis.ConditionedSurvival.survival_zero_path
#print axioms _ThesisExactChecks.target_4

section
open Thesis.Games Thesis.ConditionedSurvival
open scoped BigOperators
def _ThesisExpectedTypes.type_5 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ)
(hK : ∀ i s t, 0 ≤ K i s t) (hrow : ∀ i s, ∑ t, K i s t ≤ 1)
(s : S) (hs : 0 < survival N K 0 s),
(∀ i t, 0 ≤ survival N K i t ∧ survival N K i t ≤ 1) ∧
(∀ t, survival N K N t = 1) ∧
(∀ i < N, ∀ u, survival N K i u = ∑ t, K i u t * survival N K (i+1) t) ∧
(survival N K 0 s = ∑ path : Paths S N, pathLaw N K s path) ∧
(∀ i < N, ∀ u, (∑ t, kernel K (survival N K) i u t) =
if 0 < survival N K i u then 1 else 0) ∧
(∀ i u t, survival N K (i+1) t = 0 → kernel K (survival N K) i u t = 0) ∧
(∀ path : Paths S N, pathLaw N (kernel K (survival N K)) s path =
pathLaw N K s path / survival N K 0 s) ∧
((∑ path : Paths S N, pathLaw N (kernel K (survival N K)) s path) = 1) ∧
(∀ (path : Paths S N) (i : ℕ), i ≤ N →
survival N K i (stateAt N s path i) = 0 →
pathLaw N (kernel K (survival N K)) s path = 0))
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5 := by exact @Thesis.ConditionedSurvival.conditioned_survival
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.conditioned_survival
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.conditioned_survival"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.conditioned_survival | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedSurvival do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.conditioned_survival"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.conditioned_survival: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.conditioned_survival"
#check @Thesis.ConditionedSurvival.conditioned_survival
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/dc_decompose/master_thesis/reports/evidence/conditioned-survival/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

