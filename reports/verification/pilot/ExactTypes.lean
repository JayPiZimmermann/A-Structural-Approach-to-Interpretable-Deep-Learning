import HiddenMonotonicity.BackwardStatements
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity
theorem _ThesisExactChecks.target_0 : (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ) (r : Row m),
    (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).stabilized α r true) =
      (1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x α) r).sum) ∧
    unified ((net.originalTrace x).stabilized α r false) =
      (-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x α) r).sum)) := by exact @HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.QSources do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form"
#check @HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity
theorem _ThesisExactChecks.target_1 : (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (hx : net.Strict x) (r : Row m),
    HasFDerivAt (fun y : Vec n => r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).1)
      ((1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac-
        (sourceRows (net.absoluteQSources x (fun _ => 0)) r).sum)) x ∧
    HasFDerivAt (fun y : Vec n => r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).2)
      ((-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac+
        (sourceRows (net.absoluteQSources x (fun _ => 0)) r).sum)) x) := by exact @HiddenMonotonicity.Network.plain_head_gradient_formulas
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.plain_head_gradient_formulas
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.plain_head_gradient_formulas"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.plain_head_gradient_formulas | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.BackwardStatements do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.plain_head_gradient_formulas"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.plain_head_gradient_formulas"
#check @HiddenMonotonicity.Network.plain_head_gradient_formulas
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity
theorem _ThesisExactChecks.target_2 : (∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x)
    (α : ℕ → ℝ) (r : Row m),
    HasFDerivAt (fun y => r (net.eval y)) (r.comp (net.originalTrace x).originalJac) x ∧
    ((net.originalTrace x).stabilized α r true).1-
      ((net.originalTrace x).stabilized α r false).1 = r.comp (net.originalTrace x).originalJac ∧
    ((net.originalTrace x).stabilized α r true).2-
      ((net.originalTrace x).stabilized α r false).2 = -(r.comp (net.originalTrace x).originalJac)) := by exact @HiddenMonotonicity.Network.backward_partial_invariants
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.backward_partial_invariants
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.backward_partial_invariants"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.backward_partial_invariants | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.BackwardStatements do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.backward_partial_invariants"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.backward_partial_invariants"
#check @HiddenMonotonicity.Network.backward_partial_invariants
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity
theorem _ThesisExactChecks.target_3 : (∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x)
    (α : ℕ → ℝ) (r : Row m),
    HasFDerivAt (fun y => r (net.eval y))
      (unified ((net.originalTrace x).stabilized α r true) -
       unified ((net.originalTrace x).stabilized α r false)) x) := by exact @HiddenMonotonicity.Network.stabilized_backward_invariant
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.stabilized_backward_invariant
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.stabilized_backward_invariant"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.stabilized_backward_invariant | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.QSources do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.stabilized_backward_invariant"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.stabilized_backward_invariant"
#check @HiddenMonotonicity.Network.stabilized_backward_invariant
#print axioms _ThesisExactChecks.target_3

section
open HiddenMonotonicity
theorem _ThesisExactChecks.target_4 : (∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ)
    (rPlus rMinus : Row m) (β : ℝ),
    (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β true)) =
      (1/2 : ℝ) • ((rPlus-rMinus).comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rPlus+rMinus))).sum) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β false)) =
      (-1/2 : ℝ) • ((rPlus-rMinus).comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rPlus+rMinus))).sum)) := by exact @HiddenMonotonicity.Network.affine_readout_closed_form
end
run_cmd do
  let target ← getConstInfo `HiddenMonotonicity.Network.affine_readout_closed_form
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: HiddenMonotonicity.Network.affine_readout_closed_form"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `HiddenMonotonicity.Network.affine_readout_closed_form | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `HiddenMonotonicity.AffineReadout do
    throwError "Defining module mismatch: HiddenMonotonicity.Network.affine_readout_closed_form"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: HiddenMonotonicity.Network.affine_readout_closed_form"
#check @HiddenMonotonicity.Network.affine_readout_closed_form
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/dc_decompose/master_thesis/reports/verification/pilot/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

