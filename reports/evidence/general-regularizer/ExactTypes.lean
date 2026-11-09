import Thesis.GeneralRegularization
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_0 : Prop := (∀ (R : Regularizer) (z : ℝ), ∃ p ∈ Icc (0 : ℝ) 1, IsMaxOn (objective R z) (Icc 0 1) p)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @Thesis.GeneralRegularization.exists_optimizer
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.exists_optimizer
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.exists_optimizer"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.exists_optimizer | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.exists_optimizer"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.exists_optimizer: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.exists_optimizer"
#check @Thesis.GeneralRegularization.exists_optimizer
#print axioms _ThesisExactChecks.target_0

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_1 : Prop := (∀ (R : Regularizer) (z : ℝ), IsGreatest ((objective R z) '' Icc (0 : ℝ) 1) (activation R z))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @Thesis.GeneralRegularization.activation_isGreatest
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.activation_isGreatest
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.activation_isGreatest"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.activation_isGreatest | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.activation_isGreatest"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.activation_isGreatest: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.activation_isGreatest"
#check @Thesis.GeneralRegularization.activation_isGreatest
#print axioms _ThesisExactChecks.target_1

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_2 : Prop := (∀ (R : Regularizer) (π : ℝ → ℝ)
(hπ : ∀ z, π z ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (objective R z) (Icc 0 1) (π z))
{n m k : ℕ} (net : Network n m) (x : PairVec n)
(wp wn : Matrix (Fin k) (Fin m) ℝ) (bp bn : Vec k),
ValidPairActivation (activation R) (pairWith R π) ∧
NonnegativePairActivation (pairWith R π) ∧
ConvexOn ℝ univ (activation R) ∧ Monotone (activation R) ∧
LipschitzWith 1 (activation R) ∧
(∀ z, DifferentiableAt ℝ (activation R) z → π z = deriv (activation R) z) ∧
(preP wp wn (net.decomposeWith (pairWith R π) x)+bp -
(preN wp wn (net.decomposeWith (pairWith R π) x)+bn) =
affineLayer wp wn bp bn (net.forwardWith (activation R) (x.1-x.2))))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @Thesis.GeneralRegularization.regularized_decomposition_validity
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.regularized_decomposition_validity
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.regularized_decomposition_validity"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.regularized_decomposition_validity | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.regularized_decomposition_validity"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.regularized_decomposition_validity: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.regularized_decomposition_validity"
#check @Thesis.GeneralRegularization.regularized_decomposition_validity
#print axioms _ThesisExactChecks.target_2

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_3 : Prop := (∀ z : ℝ, activation zeroRegularizer z = relu z)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @Thesis.GeneralRegularization.zero_activation
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.zero_activation
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.zero_activation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.zero_activation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.zero_activation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.zero_activation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.zero_activation"
#check @Thesis.GeneralRegularization.zero_activation
#print axioms _ThesisExactChecks.target_3

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_4 : Prop := (pairWith zeroRegularizer hardGate = Thesis.StoppingDecomposition.stopPair)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @Thesis.GeneralRegularization.zero_pair_is_stopping
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.zero_pair_is_stopping
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.zero_pair_is_stopping"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.zero_pair_is_stopping | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.zero_pair_is_stopping"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.zero_pair_is_stopping: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.zero_pair_is_stopping"
#check @Thesis.GeneralRegularization.zero_pair_is_stopping
#print axioms _ThesisExactChecks.target_4

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_5 : Prop := (∀ (θ : ℝ) (hθ : 0 < θ) (z : ℝ),
Thesis.Regularization.gate θ z ∈ Icc (0 : ℝ) 1 ∧
IsMaxOn (objective (entropyRegularizer θ hθ) z) (Icc 0 1)
(Thesis.Regularization.gate θ z))
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5 := by exact @Thesis.GeneralRegularization.sigmoid_optimal
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.sigmoid_optimal
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.sigmoid_optimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.sigmoid_optimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.sigmoid_optimal"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.sigmoid_optimal: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.sigmoid_optimal"
#check @Thesis.GeneralRegularization.sigmoid_optimal
#print axioms _ThesisExactChecks.target_5

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_6 : Prop := (∀ (θ : ℝ) (hθ : 0 < θ) (z : ℝ), activation (entropyRegularizer θ hθ) z = Thesis.Regularization.softplus θ z)
theorem _ThesisExactChecks.target_6 : _ThesisExpectedTypes.type_6 := by exact @Thesis.GeneralRegularization.entropy_activation
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.entropy_activation
  let expected ← getConstInfo `_ThesisExactChecks.target_6
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.entropy_activation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.entropy_activation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.entropy_activation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_6) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.entropy_activation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.entropy_activation"
#check @Thesis.GeneralRegularization.entropy_activation
#print axioms _ThesisExactChecks.target_6

section
open Set HiddenMonotonicity Matrix Thesis.GeneralRegularization
def _ThesisExpectedTypes.type_7 : Prop := (∀ (θ : ℝ) (hθ : 0 < θ) (z : ℝ × ℝ),
pairWith (entropyRegularizer θ hθ) (Thesis.Regularization.gate θ) z =
Thesis.Regularization.softSplit θ z.1 z.2)
theorem _ThesisExactChecks.target_7 : _ThesisExpectedTypes.type_7 := by exact @Thesis.GeneralRegularization.entropy_pair_is_softSplit
end
run_cmd do
  let target ← getConstInfo `Thesis.GeneralRegularization.entropy_pair_is_softSplit
  let expected ← getConstInfo `_ThesisExactChecks.target_7
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.GeneralRegularization.entropy_pair_is_softSplit"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.GeneralRegularization.entropy_pair_is_softSplit | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.GeneralRegularization do
    throwError "Defining module mismatch: Thesis.GeneralRegularization.entropy_pair_is_softSplit"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_7) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.GeneralRegularization.entropy_pair_is_softSplit: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.GeneralRegularization.entropy_pair_is_softSplit"
#check @Thesis.GeneralRegularization.entropy_pair_is_softSplit
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/dc_decompose/master_thesis/reports/evidence/general-regularizer/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

