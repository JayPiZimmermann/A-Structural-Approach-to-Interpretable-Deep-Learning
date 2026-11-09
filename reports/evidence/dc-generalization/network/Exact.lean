import HiddenMonotonicity.ConvexMonotoneNetwork
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open Set HiddenMonotonicity
def _ThesisExpectedTypes.type_0 : Prop := (∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ) (hv : ValidPairActivation σ φ) (hm : Monotone φ) (hc : ConvexPairActivation φ), Monotone (net.decomposeWith φ) ∧ (∀ i, ConvexOn ℝ univ (fun x : PairVec n => (net.decomposeWith φ x).1 i)) ∧ (∀ i, ConvexOn ℝ univ (fun x : PairVec n => (net.decomposeWith φ x).2 i)) ∧ ∀ x : PairVec n, (net.decomposeWith φ x).1 - (net.decomposeWith φ x).2 = net.forwardWith σ (x.1 - x.2))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.Network.convex_monotone_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.convex_monotone_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.convex_monotone_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.convex_monotone_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneNetwork do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.convex_monotone_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.convex_monotone_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.convex_monotone_decomposition"
#check @HiddenMonotonicity.Network.convex_monotone_decomposition
#print axioms _ThesisExactChecks.target_0

section
open Set HiddenMonotonicity
def _ThesisExpectedTypes.type_1 : Prop := (∀ {d n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (φ : (ℝ × ℝ) → ℝ × ℝ) (hm : Monotone φ) (hc : ConvexPairActivation φ) (p q : Vec d → Vec n) (hp : ∀ i, ConvexOn ℝ univ (fun x => p x i)) (hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)), (∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith φ (p x,q x)).1 i)) ∧ (∀ i, ConvexOn ℝ univ (fun x => (net.decomposeWith φ (p x,q x)).2 i)))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.Network.decomposeWith_convex_input
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.decomposeWith_convex_input
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.decomposeWith_convex_input"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.decomposeWith_convex_input | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneNetwork do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.decomposeWith_convex_input"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.decomposeWith_convex_input: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.decomposeWith_convex_input"
#check @HiddenMonotonicity.Network.decomposeWith_convex_input
#print axioms _ThesisExactChecks.target_1

section
open Set HiddenMonotonicity
def _ThesisExpectedTypes.type_2 : Prop := (∀ {d n : ℕ} (f : PairVec n → ℝ) (hm : Monotone f) (hf : ConvexOn ℝ univ f) (p q : Vec d → Vec n) (hp : ∀ i, ConvexOn ℝ univ (fun x => p x i)) (hq : ∀ i, ConvexOn ℝ univ (fun x => q x i)), ConvexOn ℝ univ (fun x => f (p x,q x)))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.convex_monotone_pair_input
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.convex_monotone_pair_input
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.convex_monotone_pair_input"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.convex_monotone_pair_input | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneNetwork do
    throwError "Defining module mismatch: HiddenMonotonicity.convex_monotone_pair_input"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.convex_monotone_pair_input: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.convex_monotone_pair_input"
#check @HiddenMonotonicity.convex_monotone_pair_input
#print axioms _ThesisExactChecks.target_2

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/dc-generalization/network/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

