import Thesis.RoutingHistory
import Thesis.RoutingPolicyBridge
import Thesis.RoutingPolicyPaths
import Thesis.RoutingObservations
import Thesis.RoutingHistorySteps
import Thesis.RoutingReadoutHistory
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open Thesis.RoutingProfiles Thesis.RoutingHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_0 : Prop := (∀ (t : Tree) (plus minus : Strategy t) (h : Histories t), 0 ≤ probability t plus minus h)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @Thesis.RoutingHistory.probability_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingHistory.probability_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingHistory.probability_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingHistory.probability_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingHistory do
    throwError "Defining module mismatch: Thesis.RoutingHistory.probability_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingHistory.probability_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingHistory.probability_nonnegative"
#check @Thesis.RoutingHistory.probability_nonnegative
#print axioms _ThesisExactChecks.target_0

section
open Thesis.RoutingProfiles Thesis.RoutingHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_1 : Prop := (∀ (t : Tree) (plus minus : Strategy t), (∑ h : Histories t, probability t plus minus h) = 1)
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @Thesis.RoutingHistory.probability_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingHistory.probability_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingHistory.probability_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingHistory.probability_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingHistory do
    throwError "Defining module mismatch: Thesis.RoutingHistory.probability_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingHistory.probability_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingHistory.probability_normalized"
#check @Thesis.RoutingHistory.probability_normalized
#print axioms _ThesisExactChecks.target_1

section
open Thesis.RoutingProfiles Thesis.RoutingHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_2 : Prop := (∀ (α β : ℝ) (t : Tree) (plus minus : Strategy t) (r : ℝ), integral α β t plus minus (rootObservation t r) = r)
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @Thesis.RoutingHistory.integral_root
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingHistory.integral_root
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingHistory.integral_root"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingHistory.integral_root | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingHistory do
    throwError "Defining module mismatch: Thesis.RoutingHistory.integral_root"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingHistory.integral_root: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingHistory.integral_root"
#check @Thesis.RoutingHistory.integral_root
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork Thesis.RoutingPolicyBridge
open scoped BigOperators
def _ThesisExpectedTypes.type_3 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool), collapsed (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)).1 (inputPositive wp wn bp bn ε hε x j q) (inputNegative wp wn bp bn ε hε x j q) q = Thesis.RoutingTransitions.transition wp wn bp bn ε x j q)
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @Thesis.RoutingPolicyBridge.input_collapsed_transition
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingPolicyBridge.input_collapsed_transition
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingPolicyBridge.input_collapsed_transition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingPolicyBridge.input_collapsed_transition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingPolicyBridge do
    throwError "Defining module mismatch: Thesis.RoutingPolicyBridge.input_collapsed_transition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingPolicyBridge.input_collapsed_transition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingPolicyBridge.input_collapsed_transition"
#check @Thesis.RoutingPolicyBridge.input_collapsed_transition
#print axioms _ThesisExactChecks.target_3

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork Thesis.RoutingPolicyBridge
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree) (x : Vec n) (hx : ∀ i, 0 ≤ x i) (hv : ∀ i q, value 1 (input i q) = signed q (x i)) (j : Fin k) (q : Bool), collapsed (canonical 1 (layerGames wp wn bp bn ε hε input j q)).1 (layerPositive wp wn bp bn ε hε input j q) (layerNegative wp wn bp bn ε hε input j q) q = Thesis.RoutingTransitions.transition wp wn bp bn ε x j q)
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @Thesis.RoutingPolicyBridge.layer_collapsed_transition
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingPolicyBridge.layer_collapsed_transition
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingPolicyBridge.layer_collapsed_transition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingPolicyBridge.layer_collapsed_transition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingPolicyBridge do
    throwError "Defining module mismatch: Thesis.RoutingPolicyBridge.layer_collapsed_transition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingPolicyBridge.layer_collapsed_transition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingPolicyBridge.layer_collapsed_transition"
#check @Thesis.RoutingPolicyBridge.layer_collapsed_transition
#print axioms _ThesisExactChecks.target_4

section
open HiddenMonotonicity Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingPolicyPaths
open scoped BigOperators
def _ThesisExpectedTypes.type_5 : Prop := (∀ {n m : ℕ} (net : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin m) (i : Fin n) (q r : Bool) (path : Paths (routingTrace α β ε net x)), networkProbability α β ε hε net x j i q r path = rgProbability α β ε net x j i (Bool.xor q r) path)
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5 := by exact @Thesis.RoutingPolicyPaths.networkProbability_eq
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingPolicyPaths.networkProbability_eq
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingPolicyPaths.networkProbability_eq"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingPolicyPaths.networkProbability_eq | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingPolicyPaths do
    throwError "Defining module mismatch: Thesis.RoutingPolicyPaths.networkProbability_eq"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingPolicyPaths.networkProbability_eq: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingPolicyPaths.networkProbability_eq"
#check @Thesis.RoutingPolicyPaths.networkProbability_eq
#print axioms _ThesisExactChecks.target_5

section
open HiddenMonotonicity Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingPolicyPaths
open scoped BigOperators
def _ThesisExpectedTypes.type_6 : Prop := (∀ {n m : ℕ} (net : Network n m) (α β ε : ℝ) (x : Vec n) (i : Fin n) (path : Paths (routingTrace α β ε net x)), policyDiscount α β ε net x i path = rgDiscount α β ε net x path)
theorem _ThesisExactChecks.target_6 : _ThesisExpectedTypes.type_6 := by exact @Thesis.RoutingPolicyPaths.policyDiscount_eq
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingPolicyPaths.policyDiscount_eq
  let expected ← getConstInfo `_ThesisExactChecks.target_6
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingPolicyPaths.policyDiscount_eq"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingPolicyPaths.policyDiscount_eq | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingPolicyPaths do
    throwError "Defining module mismatch: Thesis.RoutingPolicyPaths.policyDiscount_eq"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_6) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingPolicyPaths.policyDiscount_eq: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingPolicyPaths.policyDiscount_eq"
#check @Thesis.RoutingPolicyPaths.policyDiscount_eq
#print axioms _ThesisExactChecks.target_6

section
open HiddenMonotonicity Thesis.RoutingBackward Thesis.RoutingObservations
open scoped BigOperators
def _ThesisExpectedTypes.type_7 : Prop := (∀ {n m : ℕ} (net : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin m) (q : Bool) (i : Fin n) (r : Bool), networkOccupation net α β ε hε x j q i r = rgOccupation net α β ε x j i (Bool.xor q r))
theorem _ThesisExactChecks.target_7 : _ThesisExpectedTypes.type_7 := by exact @Thesis.RoutingObservations.networkOccupation_eq_rgOccupation
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingObservations.networkOccupation_eq_rgOccupation
  let expected ← getConstInfo `_ThesisExactChecks.target_7
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingObservations.networkOccupation_eq_rgOccupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingObservations.networkOccupation_eq_rgOccupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingObservations do
    throwError "Defining module mismatch: Thesis.RoutingObservations.networkOccupation_eq_rgOccupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_7) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingObservations.networkOccupation_eq_rgOccupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingObservations.networkOccupation_eq_rgOccupation"
#check @Thesis.RoutingObservations.networkOccupation_eq_rgOccupation
#print axioms _ThesisExactChecks.target_7

section
open HiddenMonotonicity Thesis.RoutingBackward Thesis.RoutingObservations
open scoped BigOperators
def _ThesisExpectedTypes.type_8 : Prop := (∀ {n m : ℕ} (net : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (R : Vec m) (i : Fin n), lrp α β ε net x R i = ∑ j, R j * (networkOccupation net α β ε hε x j true i true - networkOccupation net α β ε hε x j true i false))
theorem _ThesisExactChecks.target_8 : _ThesisExpectedTypes.type_8 := by exact @Thesis.RoutingObservations.network_alpha_beta_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingObservations.network_alpha_beta_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_8
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingObservations.network_alpha_beta_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingObservations.network_alpha_beta_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingObservations do
    throwError "Defining module mismatch: Thesis.RoutingObservations.network_alpha_beta_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_8) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingObservations.network_alpha_beta_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingObservations.network_alpha_beta_recovery"
#check @Thesis.RoutingObservations.network_alpha_beta_recovery
#print axioms _ThesisExactChecks.target_8

section
open HiddenMonotonicity Thesis.RoutingBackward Thesis.RoutingObservations
open scoped BigOperators
def _ThesisExpectedTypes.type_9 : Prop := (∀ {d k n m : ℕ} (wp wn : Matrix (Fin k) (Fin d) ℝ) (bp bn : Vec k) (pre : Network k n) (suffix : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε) (x : Vec d) (j : Fin m) (q : Bool) (i : Fin n) (r : Bool), intermediateOccupation suffix α β ε hε (Thesis.RoutingNetwork.networkGame (Network.layer wp wn bp bn pre) ε hε x) j q i r = rgOccupation suffix α β ε ((Network.layer wp wn bp bn pre).eval x) j i (Bool.xor q r))
theorem _ThesisExactChecks.target_9 : _ThesisExpectedTypes.type_9 := by exact @Thesis.RoutingObservations.network_intermediateOccupation
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingObservations.network_intermediateOccupation
  let expected ← getConstInfo `_ThesisExactChecks.target_9
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingObservations.network_intermediateOccupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingObservations.network_intermediateOccupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingObservations do
    throwError "Defining module mismatch: Thesis.RoutingObservations.network_intermediateOccupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_9) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingObservations.network_intermediateOccupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingObservations.network_intermediateOccupation"
#check @Thesis.RoutingObservations.network_intermediateOccupation
#print axioms _ThesisExactChecks.target_9

section
open HiddenMonotonicity Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingPolicyPaths
open scoped BigOperators
def _ThesisExpectedTypes.type_10 : Prop := (∀ {n m : ℕ} (net : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin m) (i : Fin n) (q r : Bool), (∑ path : Paths (routingTrace α β ε net x), policyDiscount α β ε net x i path * networkProbability α β ε hε net x j i q r path) = rgOccupation net α β ε x j i (Bool.xor q r))
theorem _ThesisExactChecks.target_10 : _ThesisExpectedTypes.type_10 := by exact @Thesis.RoutingPolicyPaths.canonical_path_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingPolicyPaths.canonical_path_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_10
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingPolicyPaths.canonical_path_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingPolicyPaths.canonical_path_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingPolicyPaths do
    throwError "Defining module mismatch: Thesis.RoutingPolicyPaths.canonical_path_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_10) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingPolicyPaths.canonical_path_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingPolicyPaths.canonical_path_occupation"
#check @Thesis.RoutingPolicyPaths.canonical_path_occupation
#print axioms _ThesisExactChecks.target_10

section
open HiddenMonotonicity Thesis.RoutingNetwork
open scoped BigOperators
def _ThesisExpectedTypes.type_11 : Prop := (∀ {d k n m : ℕ} (wp wn : Matrix (Fin k) (Fin d) ℝ) (bp bn : Vec k) (pre : Network k n) (suffix : Network n m) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec d), networkGame ((Network.layer wp wn bp bn pre).append suffix) ε hε x = propagate ε hε suffix (networkGame (Network.layer wp wn bp bn pre) ε hε x))
theorem _ThesisExactChecks.target_11 : _ThesisExpectedTypes.type_11 := by exact @Thesis.RoutingObservations.networkGame_append_layer
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingObservations.networkGame_append_layer
  let expected ← getConstInfo `_ThesisExactChecks.target_11
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingObservations.networkGame_append_layer"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingObservations.networkGame_append_layer | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingObservations do
    throwError "Defining module mismatch: Thesis.RoutingObservations.networkGame_append_layer"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_11) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingObservations.networkGame_append_layer: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingObservations.networkGame_append_layer"
#check @Thesis.RoutingObservations.networkGame_append_layer
#print axioms _ThesisExactChecks.target_11

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork Thesis.RoutingHistory Thesis.RoutingPolicyBridge Thesis.RoutingHistorySteps
open scoped BigOperators
def _ThesisExpectedTypes.type_12 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool) (target : Option (Fin n × Bool)), (∑ h : Histories (inputLayerGames wp wn bp bn ε hε x j q), if stepTarget q (inputProjection wp wn bp bn ε hε x j q h) = target then probability (inputLayerGames wp wn bp bn ε hε x j q) (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)) (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)) h else 0) = Thesis.RoutingTransitions.transition wp wn bp bn ε x j q target)
theorem _ThesisExactChecks.target_12 : _ThesisExpectedTypes.type_12 := by exact @Thesis.RoutingHistorySteps.input_history_transition
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingHistorySteps.input_history_transition
  let expected ← getConstInfo `_ThesisExactChecks.target_12
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingHistorySteps.input_history_transition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingHistorySteps.input_history_transition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingHistorySteps do
    throwError "Defining module mismatch: Thesis.RoutingHistorySteps.input_history_transition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_12) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingHistorySteps.input_history_transition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingHistorySteps.input_history_transition"
#check @Thesis.RoutingHistorySteps.input_history_transition
#print axioms _ThesisExactChecks.target_12

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork Thesis.RoutingHistory Thesis.RoutingPolicyBridge Thesis.RoutingHistorySteps
open scoped BigOperators
def _ThesisExpectedTypes.type_13 : Prop := (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree) (x : Vec n) (hx : ∀ i, 0 ≤ x i) (hv : ∀ i q, value 1 (input i q) = signed q (x i)) (j : Fin k) (q : Bool) (target : Option (Fin n × Bool)), (∑ h : Histories (layerGames wp wn bp bn ε hε input j q), if stepTarget q (layerProjection wp wn bp bn ε hε input j q h) = target then probability (layerGames wp wn bp bn ε hε input j q) (canonical 1 (layerGames wp wn bp bn ε hε input j q)) (canonical 1 (layerGames wp wn bp bn ε hε input j q)) h else 0) = Thesis.RoutingTransitions.transition wp wn bp bn ε x j q target)
theorem _ThesisExactChecks.target_13 : _ThesisExpectedTypes.type_13 := by exact @Thesis.RoutingHistorySteps.layer_history_transition
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingHistorySteps.layer_history_transition
  let expected ← getConstInfo `_ThesisExactChecks.target_13
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingHistorySteps.layer_history_transition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingHistorySteps.layer_history_transition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingHistorySteps do
    throwError "Defining module mismatch: Thesis.RoutingHistorySteps.layer_history_transition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_13) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingHistorySteps.layer_history_transition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingHistorySteps.layer_history_transition"
#check @Thesis.RoutingHistorySteps.layer_history_transition
#print axioms _ThesisExactChecks.target_13

section
open Thesis.RoutingProfiles Thesis.RoutingReadoutHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_14 : Prop := (∀ (θ : ℝ) (positive negative : Tree), (∑ h : ForcedHistories positive negative, forcedProbability θ positive negative h) = 1)
theorem _ThesisExactChecks.target_14 : _ThesisExpectedTypes.type_14 := by exact @Thesis.RoutingReadoutHistory.forcedProbability_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.forcedProbability_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_14
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.forcedProbability_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.forcedProbability_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.forcedProbability_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_14) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.forcedProbability_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.forcedProbability_normalized"
#check @Thesis.RoutingReadoutHistory.forcedProbability_normalized
#print axioms _ThesisExactChecks.target_14

section
open HiddenMonotonicity Thesis.AffineOutputBackward Thesis.RoutingReadoutHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_15 : Prop := (∀ {n m r : ℕ} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (hx : ∀ j, 0 ≤ net.eval x j) (u : Fin r) (q : Bool) (i : Fin n) (owner : Bool), readoutHistoryOccupation net C b α β ε hε x u q i owner = readoutOccupation net C b α β ε x u i (Bool.xor q owner))
theorem _ThesisExactChecks.target_15 : _ThesisExpectedTypes.type_15 := by exact @Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation
  let expected ← getConstInfo `_ThesisExactChecks.target_15
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_15) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation"
#check @Thesis.RoutingReadoutHistory.readoutHistoryOccupation_eq_readoutOccupation
#print axioms _ThesisExactChecks.target_15

section
open HiddenMonotonicity Thesis.AffineOutputBackward Thesis.RoutingReadoutHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_16 : Prop := (∀ {n m r : ℕ} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (hx : ∀ j, 0 ≤ net.eval x j) (R : Vec r) (i : Fin n), affineOutputLRP net C b α β ε x R i = ∑ u, R u * (readoutHistoryOccupation net C b α β ε hε x u true i true - readoutHistoryOccupation net C b α β ε hε x u true i false))
theorem _ThesisExactChecks.target_16 : _ThesisExpectedTypes.type_16 := by exact @Thesis.RoutingReadoutHistory.affine_output_history_lrp
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.affine_output_history_lrp
  let expected ← getConstInfo `_ThesisExactChecks.target_16
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.affine_output_history_lrp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.affine_output_history_lrp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.affine_output_history_lrp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_16) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.affine_output_history_lrp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.affine_output_history_lrp"
#check @Thesis.RoutingReadoutHistory.affine_output_history_lrp
#print axioms _ThesisExactChecks.target_16

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.AffineOutputBackward Thesis.RoutingReadoutHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_17 : Prop := (∀ {n m r : ℕ} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (hx : ∀ j, 0 ≤ net.eval x j) (u : Fin r) (q : Bool), value 1 (positiveReadout net C b ε hε x u q) + value 1 (negativeReadout net C b ε hε x u q) = signed q (affineOutput net C b x u))
theorem _ThesisExactChecks.target_17 : _ThesisExpectedTypes.type_17 := by exact @Thesis.RoutingReadoutHistory.readout_forward
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.readout_forward
  let expected ← getConstInfo `_ThesisExactChecks.target_17
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.readout_forward"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.readout_forward | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.readout_forward"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_17) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.readout_forward: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.readout_forward"
#check @Thesis.RoutingReadoutHistory.readout_forward
#print axioms _ThesisExactChecks.target_17

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.AffineOutputBackward Thesis.RoutingReadoutHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_18 : Prop := (∀ {n k m r : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (tail : Network k m) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (R : Vec r) (i : Fin n), affineOutputLRP (Network.layer wp wn bp bn tail) C b α β ε x R i = ∑ u, R u * (readoutHistoryOccupation (Network.layer wp wn bp bn tail) C b α β ε hε x u true i true - readoutHistoryOccupation (Network.layer wp wn bp bn tail) C b α β ε hε x u true i false))
theorem _ThesisExactChecks.target_18 : _ThesisExpectedTypes.type_18 := by exact @Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp
  let expected ← getConstInfo `_ThesisExactChecks.target_18
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_18) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp"
#check @Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp
#print axioms _ThesisExactChecks.target_18

section
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.AffineOutputBackward Thesis.RoutingReadoutHistory
open scoped BigOperators
def _ThesisExpectedTypes.type_19 : Prop := (∀ {n m r : ℕ} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 ≤ ε) (x : Vec n) (hx : ∀ j, 0 ≤ net.eval x j) (u : Fin r) (q : Bool) (i : Fin n) (owner : Bool), 0 ≤ readoutHistoryOccupation net C b α β ε hε x u q i owner)
theorem _ThesisExactChecks.target_19 : _ThesisExpectedTypes.type_19 := by exact @Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative
  let expected ← getConstInfo `_ThesisExactChecks.target_19
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingReadoutHistory do
    throwError "Defining module mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_19) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative"
#check @Thesis.RoutingReadoutHistory.readoutHistoryOccupation_nonnegative
#print axioms _ThesisExactChecks.target_19

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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/A-Structural-Approach-to-Interpretable-Deep-Learning/reports/evidence/routing-bridge/review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

