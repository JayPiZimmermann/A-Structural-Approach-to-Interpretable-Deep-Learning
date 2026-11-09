import HiddenMonotonicity.ConvexMonotoneReadout
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_0 : Prop := (∀ (n m k : ℕ) (backbone : Network n m)
    (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ)
      (positiveBias negativeBias : Vec k) (input : PairVec n),
      (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).1 -
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).2 =
        affineLayer positive negative positiveBias negativeBias
          (backbone.forwardWith activation (input.1 - input.2)))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @HiddenMonotonicity.Network.affineDecomposeWith_recovery
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affineDecomposeWith_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affineDecomposeWith_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affineDecomposeWith_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affineDecomposeWith_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affineDecomposeWith_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affineDecomposeWith_recovery"
#check @HiddenMonotonicity.Network.affineDecomposeWith_recovery
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_1 : Prop := (∀ (n m k : ℕ) (backbone : Network n m), backbone.Nonnegative →
    ∀ (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift → Monotone lift →
    (ConvexOn ℝ Set.univ (fun z => (lift z).1) ∧
      ConvexOn ℝ Set.univ (fun z => (lift z).2)) →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ),
      (∀ i j, 0 ≤ positive i j) → (∀ i j, 0 ≤ negative i j) →
    ∀ (positiveBias negativeBias : Vec k),
      Monotone (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : PairVec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).1 j)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : PairVec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).2 j)) ∧
      ∀ input : PairVec n,
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).1 -
          (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias input).2 =
          affineLayer positive negative positiveBias negativeBias
            (backbone.forwardWith activation (input.1 - input.2)))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @HiddenMonotonicity.Network.affine_convex_monotone_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_convex_monotone_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_convex_monotone_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_convex_monotone_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_convex_monotone_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_convex_monotone_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_convex_monotone_decomposition"
#check @HiddenMonotonicity.Network.affine_convex_monotone_decomposition
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_2 : Prop := (∀ (n m k : ℕ) (backbone : Network n m), backbone.Nonnegative →
    ∀ (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift → Monotone lift →
    (ConvexOn ℝ Set.univ (fun z => (lift z).1) ∧
      ConvexOn ℝ Set.univ (fun z => (lift z).2)) →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ),
      (∀ i j, 0 ≤ positive i j) → (∀ i j, 0 ≤ negative i j) →
    ∀ (positiveBias negativeBias : Vec k),
      Monotone (fun input : Vec n =>
        backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).1 j)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).2 j)) ∧
      ∀ input : Vec n,
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).1 -
          (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias (input,0)).2 =
          affineLayer positive negative positiveBias negativeBias
            (backbone.forwardWith activation input))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @HiddenMonotonicity.Network.affine_dc_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_dc_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_dc_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_dc_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_dc_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_dc_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_dc_decomposition"
#check @HiddenMonotonicity.Network.affine_dc_decomposition
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity
def _ThesisExpectedTypes.type_3 : Prop := (∀ (n m k : ℕ) (backbone : Network n m), backbone.Nonnegative →
    ∀ (activation : ℝ → ℝ) (lift : (ℝ × ℝ) → ℝ × ℝ),
    ValidPairActivation activation lift → Monotone lift →
    (ConvexOn ℝ Set.univ (fun z => (lift z).1) ∧
      ConvexOn ℝ Set.univ (fun z => (lift z).2)) →
    ∀ (positive negative : Matrix (Fin k) (Fin m) ℝ),
      (∀ i j, 0 ≤ positive i j) → (∀ i j, 0 ≤ negative i j) →
    ∀ (positiveBias negativeBias : Vec k),
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
          ((fun i => max (input i) 0), (fun i => max (-input i) 0))).1 j)) ∧
      (∀ j, ConvexOn ℝ Set.univ (fun input : Vec n =>
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
          ((fun i => max (input i) 0), (fun i => max (-input i) 0))).2 j)) ∧
      ∀ input : Vec n,
        (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
          ((fun i => max (input i) 0), (fun i => max (-input i) 0))).1 -
          (backbone.affineDecomposeWith lift positive negative positiveBias negativeBias
            ((fun i => max (input i) 0), (fun i => max (-input i) 0))).2 =
          affineLayer positive negative positiveBias negativeBias
            (backbone.forwardWith activation input))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @HiddenMonotonicity.Network.affine_signed_input_dc_decomposition
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_signed_input_dc_decomposition
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_signed_input_dc_decomposition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_signed_input_dc_decomposition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.ConvexMonotoneReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_signed_input_dc_decomposition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target HiddenMonotonicity.Network.affine_signed_input_dc_decomposition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_signed_input_dc_decomposition"
#check @HiddenMonotonicity.Network.affine_signed_input_dc_decomposition
#print axioms _ThesisExactChecks.target_3

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/dc-generalization/readout/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

