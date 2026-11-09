import Thesis.RoutingObservations
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork Thesis.RoutingHistory Thesis.RoutingBackward Thesis.RoutingObservations
open scoped BigOperators
def _ThesisExpectedTypes.type_0 : Prop := (∀ {n m : ℕ} (net : Network n m) (α β ε : ℝ) (hε : 0≤ε)
 (x : Vec n) (mark : Fin n → Bool → ℝ) (j : Fin m) (q : Bool),
 canonicalIntegral 1 α β (networkGame net ε hε x j q)
   (networkObservation net ε hε x mark j q) =
 traceObservation (routingTrace α β ε net x) mark j q)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @Thesis.RoutingObservations.network_integral
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingObservations.network_integral
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingObservations.network_integral"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingObservations.network_integral | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingObservations do
    throwError "Defining module mismatch: Thesis.RoutingObservations.network_integral"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingObservations.network_integral: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingObservations.network_integral"
#check @Thesis.RoutingObservations.network_integral
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork Thesis.RoutingHistory Thesis.RoutingBackward Thesis.RoutingObservations
open scoped BigOperators
def _ThesisExpectedTypes.type_1 : Prop := (∀ {n m : ℕ} (net : Network n m) (α β ε : ℝ) (hε : 0≤ε)
 (x : Vec n) (j : Fin m) (q : Bool) (i : Fin n) (r : Bool),
 networkOccupation net α β ε hε x j q i r =
 rgOccupation net α β ε x j i (Bool.xor q r))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @Thesis.RoutingObservations.networkOccupation_eq_rgOccupation
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingObservations.networkOccupation_eq_rgOccupation
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingObservations.networkOccupation_eq_rgOccupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingObservations.networkOccupation_eq_rgOccupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingObservations do
    throwError "Defining module mismatch: Thesis.RoutingObservations.networkOccupation_eq_rgOccupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingObservations.networkOccupation_eq_rgOccupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingObservations.networkOccupation_eq_rgOccupation"
#check @Thesis.RoutingObservations.networkOccupation_eq_rgOccupation
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork Thesis.RoutingHistory Thesis.RoutingBackward Thesis.RoutingObservations
open scoped BigOperators
def _ThesisExpectedTypes.type_2 : Prop := (∀ {n m : ℕ} (net : Network n m) (α β ε : ℝ)
 (hα : 0≤α) (hβ : 0≤β) (hε : 0≤ε) (x : Vec n)
 (j : Fin m) (q : Bool) (i : Fin n) (r : Bool),
 0 ≤ networkOccupation net α β ε hε x j q i r)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @Thesis.RoutingObservations.networkOccupation_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingObservations.networkOccupation_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingObservations.networkOccupation_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingObservations.networkOccupation_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingObservations do
    throwError "Defining module mismatch: Thesis.RoutingObservations.networkOccupation_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingObservations.networkOccupation_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingObservations.networkOccupation_nonnegative"
#check @Thesis.RoutingObservations.networkOccupation_nonnegative
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork Thesis.RoutingHistory Thesis.RoutingBackward Thesis.RoutingObservations
open scoped BigOperators
def _ThesisExpectedTypes.type_3 : Prop := (∀ {n m : ℕ} (net : Network n m) (α β ε : ℝ) (hε : 0≤ε)
 (x : Vec n) (R : Vec m) (i : Fin n),
 lrp α β ε net x R i = ∑ j, R j *
 (networkOccupation net α β ε hε x j true i true -
  networkOccupation net α β ε hε x j true i false))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @Thesis.RoutingObservations.network_alpha_beta_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingObservations.network_alpha_beta_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingObservations.network_alpha_beta_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingObservations.network_alpha_beta_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingObservations do
    throwError "Defining module mismatch: Thesis.RoutingObservations.network_alpha_beta_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingObservations.network_alpha_beta_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingObservations.network_alpha_beta_recovery"
#check @Thesis.RoutingObservations.network_alpha_beta_recovery
#print axioms _ThesisExactChecks.target_3

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork Thesis.RoutingHistory Thesis.RoutingBackward Thesis.RoutingObservations
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {d k n m : ℕ} (wp wn : Matrix (Fin k) (Fin d) ℝ) (bp bn : Vec k)
 (pre : Network k n) (suffix : Network n m) (ε : ℝ) (hε : 0≤ε) (x : Vec d),
 networkGame ((Network.layer wp wn bp bn pre).append suffix) ε hε x =
 propagate ε hε suffix (networkGame (Network.layer wp wn bp bn pre) ε hε x))
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @Thesis.RoutingObservations.networkGame_append_layer
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingObservations.networkGame_append_layer
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingObservations.networkGame_append_layer"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingObservations.networkGame_append_layer | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingObservations do
    throwError "Defining module mismatch: Thesis.RoutingObservations.networkGame_append_layer"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingObservations.networkGame_append_layer: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingObservations.networkGame_append_layer"
#check @Thesis.RoutingObservations.networkGame_append_layer
#print axioms _ThesisExactChecks.target_4

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork Thesis.RoutingHistory Thesis.RoutingBackward Thesis.RoutingObservations
open scoped BigOperators
def _ThesisExpectedTypes.type_5 : Prop := (∀ {d k n m : ℕ} (wp wn : Matrix (Fin k) (Fin d) ℝ) (bp bn : Vec k)
 (pre : Network k n) (suffix : Network n m) (α β ε : ℝ) (hε : 0≤ε) (x : Vec d)
 (j : Fin m) (q : Bool) (i : Fin n) (r : Bool),
 intermediateOccupation suffix α β ε hε
   (networkGame (Network.layer wp wn bp bn pre) ε hε x) j q i r =
 rgOccupation suffix α β ε ((Network.layer wp wn bp bn pre).eval x)
   j i (Bool.xor q r))
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5 := by exact @Thesis.RoutingObservations.network_intermediateOccupation
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingObservations.network_intermediateOccupation
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingObservations.network_intermediateOccupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingObservations.network_intermediateOccupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingObservations do
    throwError "Defining module mismatch: Thesis.RoutingObservations.network_intermediateOccupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingObservations.network_intermediateOccupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingObservations.network_intermediateOccupation"
#check @Thesis.RoutingObservations.network_intermediateOccupation
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/routing-bridge/observations-check/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

