import Thesis.ConditionedTrajectory
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
def _ThesisExpectedTypes.type_0 : Prop := (∀ {S : Type} [Fintype S] (N i : ℕ) (hi : i ≤ N)
(K : ℕ → S → S → ℝ) (s t : S),
timeMass N i K s t = prefixMass i K s t * survival N K i t)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @Thesis.ConditionedSurvival.timeMass_factorization
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.timeMass_factorization
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.timeMass_factorization"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.timeMass_factorization | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedTrajectory do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.timeMass_factorization"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.timeMass_factorization: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.timeMass_factorization"
#check @Thesis.ConditionedSurvival.timeMass_factorization
#print axioms _ThesisExactChecks.target_0

section
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
def _ThesisExpectedTypes.type_1 : Prop := (∀ {S : Type} [Fintype S] (N i : ℕ) (hi : i ≤ N)
(K : ℕ → S → S → ℝ) (hK : ∀ j s t, 0 ≤ K j s t)
(s : S) (hs : 0 < survival N K 0 s) (t : S),
timeMass N i (kernel K (survival N K)) s t =
prefixMass i K s t * survival N K i t / survival N K 0 s)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @Thesis.ConditionedSurvival.conditioned_time_marginal
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.conditioned_time_marginal
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.conditioned_time_marginal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.conditioned_time_marginal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedTrajectory do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.conditioned_time_marginal"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.conditioned_time_marginal: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.conditioned_time_marginal"
#check @Thesis.ConditionedSurvival.conditioned_time_marginal
#print axioms _ThesisExactChecks.target_1

section
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
def _ThesisExpectedTypes.type_2 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (A B : ℕ → S → S → ℝ)
(hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
(i : ℕ) (s t : S),
Real.sqrt (kernel A (survival N A) i s t * kernel B (survival N B) i s t) =
Real.sqrt (A i s t * B i s t) *
Real.sqrt (survival N A (i+1) t * survival N B (i+1) t) /
Real.sqrt (survival N A i s * survival N B i s))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @Thesis.ConditionedSurvival.conditioned_geometric_kernel
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.conditioned_geometric_kernel
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.conditioned_geometric_kernel"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.conditioned_geometric_kernel | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedTrajectory do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.conditioned_geometric_kernel"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.conditioned_geometric_kernel: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.conditioned_geometric_kernel"
#check @Thesis.ConditionedSurvival.conditioned_geometric_kernel
#print axioms _ThesisExactChecks.target_2

section
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
def _ThesisExpectedTypes.type_3 : Prop := (∀ {S : Type} [Fintype S] (N : ℕ) (A B : ℕ → S → S → ℝ)
(hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
(hArow : ∀ i s, ∑ t, A i s t ≤ 1) (hBrow : ∀ i s, ∑ t, B i s t ≤ 1)
(s : S) (hsA : 0 < survival N A 0 s) (hsB : 0 < survival N B 0 s),
(survival N A 0 s ≤ 1 ∧ survival N B 0 s ≤ 1) ∧
(∀ i ≤ N, ∀ t,
timeMass N i (kernel A (survival N A)) s t =
prefixMass i A s t * survival N A i t / survival N A 0 s ∧
timeMass N i (kernel B (survival N B)) s t =
prefixMass i B s t * survival N B i t / survival N B 0 s) ∧
(∀ i u v,
Real.sqrt (kernel A (survival N A) i u v * kernel B (survival N B) i u v) =
Real.sqrt (A i u v * B i u v) *
Real.sqrt (survival N A (i+1) v * survival N B (i+1) v) /
Real.sqrt (survival N A i u * survival N B i u)) ∧
(overlap (pathLaw N (kernel A (survival N A)) s)
(pathLaw N (kernel B (survival N B)) s) =
∑ path : Paths S N, pathLaw N (fun i u v => Real.sqrt
(kernel A (survival N A) i u v * kernel B (survival N B) i u v)) s path) ∧
(overlap (pathLaw N (kernel A (survival N A)) s)
(pathLaw N (kernel B (survival N B)) s) =
backwardDP N (fun i u v => Real.sqrt
(kernel A (survival N A) i u v * kernel B (survival N B) i u v)) (fun _ => 1) s) ∧
(overlap (pathLaw N (kernel A (survival N A)) s)
(pathLaw N (kernel B (survival N B)) s) =
ordinaryOverlap N A B s / Real.sqrt (survival N A 0 s * survival N B 0 s)) ∧
((1/2 : ℝ) * (∑ path : Paths S N,
(Real.sqrt (pathLaw N (kernel A (survival N A)) s path) -
Real.sqrt (pathLaw N (kernel B (survival N B)) s path))^2) =
1 - ordinaryOverlap N A B s / Real.sqrt (survival N A 0 s * survival N B 0 s)))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @Thesis.ConditionedSurvival.conditioned_survival_statistics
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.conditioned_survival_statistics
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.conditioned_survival_statistics"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.conditioned_survival_statistics | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedTrajectory do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.conditioned_survival_statistics"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.conditioned_survival_statistics: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.conditioned_survival_statistics"
#check @Thesis.ConditionedSurvival.conditioned_survival_statistics
#print axioms _ThesisExactChecks.target_3

section
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {S : Type} [Fintype S] (A B : ℕ → S → S → ℝ)
(hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
(hArow : ∀ i s, ∑ t, A i s t = 1) (hBrow : ∀ i s, ∑ t, B i s t = 1) (s : S),
overlap (pathLaw 0 A s) (pathLaw 0 B s) = 1 ∧
(∀ n, 0 ≤ overlap (pathLaw n A s) (pathLaw n B s) ∧
overlap (pathLaw n A s) (pathLaw n B s) ≤ 1) ∧
Antitone (fun n => overlap (pathLaw n A s) (pathLaw n B s)) ∧
Monotone (fun n => (1/2 : ℝ) * ∑ path : Paths S n,
(Real.sqrt (pathLaw n A s path) - Real.sqrt (pathLaw n B s path))^2) ∧
(∀ n, (1/2 : ℝ) * (∑ path : Paths S n,
(Real.sqrt (pathLaw n A s path) - Real.sqrt (pathLaw n B s path))^2) =
1 - overlap (pathLaw n A s) (pathLaw n B s)) ∧
(∀ n, overlap (pathLaw n A s) (pathLaw n B s) =
backwardDP n (fun i u v => Real.sqrt (A i u v * B i u v)) (fun _ => 1) s))
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @Thesis.ConditionedSurvival.trajectory_bc_monotone
end
run_cmd do
  let target ← getConstInfo `Thesis.ConditionedSurvival.trajectory_bc_monotone
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.ConditionedSurvival.trajectory_bc_monotone"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ConditionedSurvival.trajectory_bc_monotone | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ConditionedTrajectory do
    throwError "Defining module mismatch: Thesis.ConditionedSurvival.trajectory_bc_monotone"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.ConditionedSurvival.trajectory_bc_monotone: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ConditionedSurvival.trajectory_bc_monotone"
#check @Thesis.ConditionedSurvival.trajectory_bc_monotone
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/dc_decompose/master_thesis/reports/evidence/conditioned-trajectory-review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

