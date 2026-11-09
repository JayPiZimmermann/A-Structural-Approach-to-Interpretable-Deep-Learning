import Thesis.RoutingReadoutHistory
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingReadoutHistory Thesis.AffineOutputBackward
open scoped BigOperators
def _ThesisExpectedTypes.type_0 : Prop := (∀ {n m r : ℕ} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (hx : ∀ j, 0 ≤ net.eval x j) (u : Fin r) (q : Bool), value 1 (positiveReadout net C b ε hε x u q) + value 1 (negativeReadout net C b ε hε x u q) = signed q (affineOutput net C b x u))
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @Thesis.RoutingReadoutHistory.readout_forward
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.readout_forward
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.readout_forward"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.readout_forward | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.readout_forward"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.readout_forward: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.readout_forward"
#check @Thesis.RoutingReadoutHistory.readout_forward
#print axioms _ThesisExactChecks.target_0

section
open Thesis.RoutingProfiles Thesis.RoutingReadoutHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_1 : Prop := (∀ (θ : ℝ) (positive negative : Tree), (∑ h : ForcedHistories positive negative, forcedProbability θ positive negative h) = 1)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @Thesis.RoutingReadoutHistory.forcedProbability_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.forcedProbability_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.forcedProbability_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.forcedProbability_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.forcedProbability_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.forcedProbability_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.forcedProbability_normalized"
#check @Thesis.RoutingReadoutHistory.forcedProbability_normalized
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity Thesis.RoutingReadoutHistory Thesis.AffineOutputBackward
open scoped BigOperators
def _ThesisExpectedTypes.type_2 : Prop := (∀ {n m r : ℕ} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (hx : ∀ j, 0 ≤ net.eval x j) (u : Fin r) (q : Bool) (i : Fin n) (owner : Bool), readoutHistoryOccupation net C b α β ε hε x u q i owner = readoutOccupation net C b α β ε x u i (Bool.xor q owner))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation"
#check @Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity Thesis.RoutingReadoutHistory Thesis.AffineOutputBackward
open scoped BigOperators
def _ThesisExpectedTypes.type_3 : Prop := (∀ {n k m r : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (tail : Network k m) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (R : Vec r) (i : Fin n), affineOutputLRP (Network.layer wp wn bp bn tail) C b α β ε x R i = ∑ u, R u * (readoutHistoryOccupation (Network.layer wp wn bp bn tail) C b α β ε hε x u true i true - readoutHistoryOccupation (Network.layer wp wn bp bn tail) C b α β ε hε x u true i false))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp"
#check @Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp
#print axioms _ThesisExactChecks.target_3

section
open HiddenMonotonicity Thesis.RoutingReadoutHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {n m r : ℕ} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 ≤ ε) (x : Vec n) (hx : ∀ j, 0 ≤ net.eval x j) (u : Fin r) (q : Bool) (i : Fin n) (owner : Bool), 0 ≤ readoutHistoryOccupation net C b α β ε hε x u q i owner)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative"
#check @Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/routing-bridge/readout-check/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

