import Thesis.SoftplusCircuitUniqueness
import Thesis.SoftplusCircuitVisits
import Thesis.SoftplusCircuitPayoff
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_0 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (x : Vec d),
 graphWith relu c plan x = c.eval x)
theorem _ThesisExactChecks.target_0 : _ThesisExpectedTypes.type_0 := by exact @Thesis.SoftplusCircuit.graphWith_relu
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graphWith_relu
  let expected ← getConstInfo `_ThesisExactChecks.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graphWith_relu"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graphWith_relu | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitModel do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graphWith_relu"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_0) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graphWith_relu: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graphWith_relu"
#check @Thesis.SoftplusCircuit.graphWith_relu
#print axioms _ThesisExactChecks.target_0

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_1 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ) (x : PairVec d),
 (graphSplit θ c plan x).1 - (graphSplit θ c plan x).2 = graphSoft θ c plan (x.1-x.2))
theorem _ThesisExactChecks.target_1 : _ThesisExpectedTypes.type_1 := by exact @Thesis.SoftplusCircuit.graphSplit_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graphSplit_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graphSplit_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graphSplit_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitModel do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graphSplit_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_1) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graphSplit_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graphSplit_recovery"
#check @Thesis.SoftplusCircuit.graphSplit_recovery
#print axioms _ThesisExactChecks.target_1

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_2 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ)
 (x : Vec d) (plus minus : Strategy c plan),
 signedValue θ c plan plus (canonicalStrategy θ c plan x) (x,-x) ≤
   (graphSoft θ c plan x,-graphSoft θ c plan x) ∧
 signedValue θ c plan (canonicalStrategy θ c plan x) (canonicalStrategy θ c plan x) (x,-x) =
   (graphSoft θ c plan x,-graphSoft θ c plan x) ∧
 (graphSoft θ c plan x,-graphSoft θ c plan x) ≤
   signedValue θ c plan (canonicalStrategy θ c plan x) minus (x,-x))
theorem _ThesisExactChecks.target_2 : _ThesisExpectedTypes.type_2 := by exact @Thesis.SoftplusCircuit.graph_saddle
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graph_saddle
  let expected ← getConstInfo `_ThesisExactChecks.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graph_saddle"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graph_saddle | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitEquilibrium do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graph_saddle"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_2) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graph_saddle: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graph_saddle"
#check @Thesis.SoftplusCircuit.graph_saddle
#print axioms _ThesisExactChecks.target_2

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_3 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ) (x : Vec d),
 SubgamePerfect θ c plan (canonicalStrategy θ c plan x) (canonicalStrategy θ c plan x) (x,-x))
theorem _ThesisExactChecks.target_3 : _ThesisExpectedTypes.type_3 := by exact @Thesis.SoftplusCircuit.canonical_spne
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.canonical_spne
  let expected ← getConstInfo `_ThesisExactChecks.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.canonical_spne"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.canonical_spne | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitEquilibrium do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.canonical_spne"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_3) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.canonical_spne: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.canonical_spne"
#check @Thesis.SoftplusCircuit.canonical_spne
#print axioms _ThesisExactChecks.target_3

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_4 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ)
 (plus minus : Strategy c plan) (v : Thesis.SoftplusGame.PlayerValues d),
 Thesis.SoftplusGame.advantage (playerValue θ c plan plus minus v) =
 signedValue θ c plan plus minus (Thesis.SoftplusGame.advantage v))
theorem _ThesisExactChecks.target_4 : _ThesisExpectedTypes.type_4 := by exact @Thesis.SoftplusCircuit.playerValue_advantage
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.playerValue_advantage
  let expected ← getConstInfo `_ThesisExactChecks.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.playerValue_advantage"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.playerValue_advantage | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitPlayers do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.playerValue_advantage"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_4) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.playerValue_advantage: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.playerValue_advantage"
#check @Thesis.SoftplusCircuit.playerValue_advantage
#print axioms _ThesisExactChecks.target_4

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_5 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ) (x : PairVec d),
 playerValue θ c plan (canonicalStrategy θ c plan (x.1-x.2))
   (canonicalStrategy θ c plan (x.1-x.2)) (Thesis.SoftplusGame.pairValues x) =
 Thesis.SoftplusGame.pairValues (graphSplit θ c plan x))
theorem _ThesisExactChecks.target_5 : _ThesisExpectedTypes.type_5 := by exact @Thesis.SoftplusCircuit.playerValue_canonical
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.playerValue_canonical
  let expected ← getConstInfo `_ThesisExactChecks.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.playerValue_canonical"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.playerValue_canonical | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitPlayers do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.playerValue_canonical"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_5) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.playerValue_canonical: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.playerValue_canonical"
#check @Thesis.SoftplusCircuit.playerValue_canonical
#print axioms _ThesisExactChecks.target_5

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_6 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ)
 (hc : NoPools c plan) (x : Vec d) (plus minus : Strategy c plan),
 SubgamePerfect θ c plan plus minus (x,-x) ↔
 plus=canonicalStrategy θ c plan x ∧ minus=canonicalStrategy θ c plan x)
theorem _ThesisExactChecks.target_6 : _ThesisExpectedTypes.type_6 := by exact @Thesis.SoftplusCircuit.subgamePerfect_iff
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.subgamePerfect_iff
  let expected ← getConstInfo `_ThesisExactChecks.target_6
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.subgamePerfect_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.subgamePerfect_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitUniqueness do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.subgamePerfect_iff"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_6) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.subgamePerfect_iff: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.subgamePerfect_iff"
#check @Thesis.SoftplusCircuit.subgamePerfect_iff
#print axioms _ThesisExactChecks.target_6

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_7 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ) (x : PairVec d),
 SubgamePerfect θ c plan (canonicalStrategy θ c plan (x.1-x.2))
   (canonicalStrategy θ c plan (x.1-x.2)) (x.1-x.2,-(x.1-x.2)) ∧
 playerValue θ c plan (canonicalStrategy θ c plan (x.1-x.2))
   (canonicalStrategy θ c plan (x.1-x.2)) (Thesis.SoftplusGame.pairValues x) =
   Thesis.SoftplusGame.pairValues (graphSplit θ c plan x) ∧
 (graphSplit θ c plan x).1-(graphSplit θ c plan x).2=graphSoft θ c plan (x.1-x.2))
theorem _ThesisExactChecks.target_7 : _ThesisExpectedTypes.type_7 := by exact @Thesis.SoftplusCircuit.softplus_forward_spne
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.softplus_forward_spne
  let expected ← getConstInfo `_ThesisExactChecks.target_7
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.softplus_forward_spne"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.softplus_forward_spne | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitUniqueness do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.softplus_forward_spne"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_7) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.softplus_forward_spne: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.softplus_forward_spne"
#check @Thesis.SoftplusCircuit.softplus_forward_spne
#print axioms _ThesisExactChecks.target_7

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_8 : Prop := (∀ {n : ℕ} {e : SignedExpr (Fin n)} (θ : ℝ) (spec : NodeSpec e) (x : Vec n),
 (∑ target : Option (Fin n × Bool), nodeProbability θ spec x target) = 1)
theorem _ThesisExactChecks.target_8 : _ThesisExpectedTypes.type_8 := by exact @Thesis.SoftplusCircuit.nodeProbability_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.nodeProbability_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_8
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.nodeProbability_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.nodeProbability_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitRows do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.nodeProbability_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_8) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.nodeProbability_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.nodeProbability_normalized"
#check @Thesis.SoftplusCircuit.nodeProbability_normalized
#print axioms _ThesisExactChecks.target_8

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_9 : Prop := (∀ {n : ℕ} {e : SignedExpr (Fin n)} (θ : ℝ) (spec : NodeSpec e) (x : Vec n)
 (i : Fin n) (b : Bool), nodeDiscount spec x * nodeProbability θ spec x (some (i,b)) =
 if b then (selectedWeights θ spec x).2 i else (selectedWeights θ spec x).1 i)
theorem _ThesisExactChecks.target_9 : _ThesisExpectedTypes.type_9 := by exact @Thesis.SoftplusCircuit.node_discount_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.node_discount_recovery
  let expected ← getConstInfo `_ThesisExactChecks.target_9
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.node_discount_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.node_discount_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitRows do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.node_discount_recovery"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_9) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.node_discount_recovery: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.node_discount_recovery"
#check @Thesis.SoftplusCircuit.node_discount_recovery
#print axioms _ThesisExactChecks.target_9

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_10 : Prop := (∀ {n : ℕ} {e : SignedExpr (Fin n)} (θ : ℝ) (spec : NodeSpec e) (x : Vec n)
 (v : Thesis.SoftplusGame.PlayerValues n) (player turn : Bool),
 nodePlayer θ spec (canonicalNode θ spec x) (canonicalNode θ spec x) v player turn =
 nodeReward θ spec x player turn +
 ∑ i : Fin n, ∑ b : Bool, nodeDiscount spec x * nodeProbability θ spec x (some (i,b)) *
 v player (Bool.xor turn b) i)
theorem _ThesisExactChecks.target_10 : _ThesisExpectedTypes.type_10 := by exact @Thesis.SoftplusCircuit.nodePlayer_transition
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.nodePlayer_transition
  let expected ← getConstInfo `_ThesisExactChecks.target_10
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.nodePlayer_transition"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.nodePlayer_transition | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitTransition do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.nodePlayer_transition"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_10) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.nodePlayer_transition: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.nodePlayer_transition"
#check @Thesis.SoftplusCircuit.nodePlayer_transition
#print axioms _ThesisExactChecks.target_10

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_11 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ)
 (x : Vec d) (hx : Regular θ c plan x),
 HasFDerivAt (graphSoft θ c plan)
 (matrixCLM ((graphKernel θ c plan x).1-(graphKernel θ c plan x).2)) x)
theorem _ThesisExactChecks.target_11 : _ThesisExpectedTypes.type_11 := by exact @Thesis.SoftplusCircuit.graphSoft_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graphSoft_hasFDerivAt
  let expected ← getConstInfo `_ThesisExactChecks.target_11
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graphSoft_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graphSoft_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitDerivative do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graphSoft_hasFDerivAt"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_11) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graphSoft_hasFDerivAt: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graphSoft_hasFDerivAt"
#check @Thesis.SoftplusCircuit.graphSoft_hasFDerivAt
#print axioms _ThesisExactChecks.target_11

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_12 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) (j : Fin n),
 (∑ path : Thesis.StoppingDAG.DAGPaths c, pathProbability θ c plan x j path) = 1)
theorem _ThesisExactChecks.target_12 : _ThesisExpectedTypes.type_12 := by exact @Thesis.SoftplusCircuit.pathProbability_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.pathProbability_normalized
  let expected ← getConstInfo `_ThesisExactChecks.target_12
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.pathProbability_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.pathProbability_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitPaths do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.pathProbability_normalized"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_12) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.pathProbability_normalized: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.pathProbability_normalized"
#check @Thesis.SoftplusCircuit.pathProbability_normalized
#print axioms _ThesisExactChecks.target_12

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_13 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d)
 (j : Fin n) (turn : Bool) (i : Fin d) (channel : Bool),
 occupation c plan θ x j turn i channel =
 if Bool.xor channel turn then (graphKernel θ c plan x).2 j i else (graphKernel θ c plan x).1 j i)
theorem _ThesisExactChecks.target_13 : _ThesisExpectedTypes.type_13 := by exact @Thesis.SoftplusCircuit.occupation_eq_kernel
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.occupation_eq_kernel
  let expected ← getConstInfo `_ThesisExactChecks.target_13
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.occupation_eq_kernel"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.occupation_eq_kernel | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitOccupation do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.occupation_eq_kernel"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_13) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.occupation_eq_kernel: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.occupation_eq_kernel"
#check @Thesis.SoftplusCircuit.occupation_eq_kernel
#print axioms _ThesisExactChecks.target_13

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_14 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ)
 (x : Vec d) (hx : Regular θ c plan x) (j : Fin n) (i : Fin d),
 (fderiv ℝ (graphSoft θ c plan) x (Pi.single i 1)) j =
 occupation c plan θ x j false i false - occupation c plan θ x j false i true)
theorem _ThesisExactChecks.target_14 : _ThesisExpectedTypes.type_14 := by exact @Thesis.SoftplusCircuit.graph_derivative_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graph_derivative_occupation
  let expected ← getConstInfo `_ThesisExactChecks.target_14
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graph_derivative_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graph_derivative_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitOccupation do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graph_derivative_occupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_14) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graph_derivative_occupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graph_derivative_occupation"
#check @Thesis.SoftplusCircuit.graph_derivative_occupation
#print axioms _ThesisExactChecks.target_14

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_15 : Prop := (∀ {d m n : ℕ} (pre : Circuit d m) (prePlan : Plan pre)
 (suffix : Circuit m n) (suffixPlan : Plan suffix) (θ : ℝ) (x : Vec d),
 graphSoft θ (Thesis.StoppingDAG.graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) x =
 graphSoft θ suffix suffixPlan (graphSoft θ pre prePlan x))
theorem _ThesisExactChecks.target_15 : _ThesisExpectedTypes.type_15 := by exact @Thesis.SoftplusCircuit.graft_soft
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.graft_soft
  let expected ← getConstInfo `_ThesisExactChecks.target_15
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.graft_soft"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.graft_soft | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitCuts do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.graft_soft"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_15) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.graft_soft: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.graft_soft"
#check @Thesis.SoftplusCircuit.graft_soft
#print axioms _ThesisExactChecks.target_15

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_16 : Prop := (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (prePlan : Plan pre)
 (suffix : Circuit (m+1) n) (suffixPlan : Plan suffix) (θ : ℝ) (x : Vec d)
 (j : Fin n) (turn channel : Bool),
 fullOccupation (Thesis.StoppingDAG.graft pre suffix) (graftPlan pre prePlan suffix suffixPlan)
   θ x j turn m channel =
 occupation suffix suffixPlan θ (graphSoft θ pre prePlan x) j turn (Fin.last m) channel)
theorem _ThesisExactChecks.target_16 : _ThesisExpectedTypes.type_16 := by exact @Thesis.SoftplusCircuit.fullOccupation_graft_last
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.fullOccupation_graft_last
  let expected ← getConstInfo `_ThesisExactChecks.target_16
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.fullOccupation_graft_last"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.fullOccupation_graft_last | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitVisits do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.fullOccupation_graft_last"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_16) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.fullOccupation_graft_last: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.fullOccupation_graft_last"
#check @Thesis.SoftplusCircuit.fullOccupation_graft_last
#print axioms _ThesisExactChecks.target_16

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_17 : Prop := (∀ {d m n : ℕ} (pre : Circuit d (m+1)) (prePlan : Plan pre)
 (suffix : Circuit (m+1) n) (suffixPlan : Plan suffix) (θ : ℝ) (hθ : 0 < θ) (x : Vec d)
 (hx : Regular θ (Thesis.StoppingDAG.graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) x)
 (j : Fin n) (q : Bool),
 (fderiv ℝ (graphSoft θ suffix suffixPlan) (graphSoft θ pre prePlan x) (Pi.single (Fin.last m) 1)) j =
 (if q then (-1 : ℝ) else 1) *
 (fullOccupation (Thesis.StoppingDAG.graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) θ x j q m false -
  fullOccupation (Thesis.StoppingDAG.graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) θ x j q m true))
theorem _ThesisExactChecks.target_17 : _ThesisExpectedTypes.type_17 := by exact @Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation
  let expected ← getConstInfo `_ThesisExactChecks.target_17
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitVisits do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_17) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation"
#check @Thesis.SoftplusCircuit.intermediate_derivative_fullOccupation
#print axioms _ThesisExactChecks.target_17

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_18 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d)
 (v : Thesis.SoftplusGame.PlayerValues d) (player : Bool) (j : Fin n) (turn : Bool),
 expectedPayoff c plan θ x v player j turn =
 playerValue θ c plan (canonicalStrategy θ c plan x) (canonicalStrategy θ c plan x) v player turn j)
theorem _ThesisExactChecks.target_18 : _ThesisExpectedTypes.type_18 := by exact @Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue
  let expected ← getConstInfo `_ThesisExactChecks.target_18
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitPayoff do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_18) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue"
#check @Thesis.SoftplusCircuit.expectedPayoff_eq_playerValue
#print axioms _ThesisExactChecks.target_18

section
open HiddenMonotonicity Thesis.SoftplusCircuit
open scoped BigOperators
def _ThesisExpectedTypes.type_19 : Prop := (∀ {d n : ℕ} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0 < θ)
 (x : PairVec d) (player turn : Bool) (j : Fin n),
 expectedPayoff c plan θ (x.1-x.2) (Thesis.SoftplusGame.pairValues x) player j turn =
 if player=turn then (graphSplit θ c plan x).1 j else (graphSplit θ c plan x).2 j)
theorem _ThesisExactChecks.target_19 : _ThesisExpectedTypes.type_19 := by exact @Thesis.SoftplusCircuit.expectedPayoff_eq_split
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusCircuit.expectedPayoff_eq_split
  let expected ← getConstInfo `_ThesisExactChecks.target_19
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_split"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusCircuit.expectedPayoff_eq_split | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusCircuitPayoff do
    throwError "Defining module mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_split"
  for axiomName in (← Lean.collectAxioms `_ThesisExactChecks.target_19) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unapproved axiom in exact target Thesis.SoftplusCircuit.expectedPayoff_eq_split: {axiomName}"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusCircuit.expectedPayoff_eq_split"
#check @Thesis.SoftplusCircuit.expectedPayoff_eq_split
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
  liftIO <| IO.FS.writeFile "/home/jzimmermann/code/dc_decompose/master_thesis/reports/evidence/softplus-circuit-review/environment.json" (Json.pretty (toJson records))
  logInfo m!"Audited {records.size} project theorem declarations in the imported environment"

