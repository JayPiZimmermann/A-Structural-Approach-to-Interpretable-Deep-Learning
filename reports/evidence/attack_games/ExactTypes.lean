import Thesis.AffineOutputBackward
import Thesis.AttentionBackward
import Thesis.BackwardGames
import Thesis.Coarsening
import Thesis.Games
import Thesis.Randomization
import Thesis.RandomizationExpectation
import Thesis.ReferencePolicy
import Thesis.Regularization
import Thesis.RoutingBackward
import Thesis.RoutingExpectation
import Thesis.RoutingGate
import Thesis.RoutingSupport
import Thesis.RoutingTransitions
import Thesis.SoftplusBackward
import Thesis.SoftplusBoundary
import Thesis.SoftplusDecomposition
import Thesis.StoppingBoundary
import Thesis.StoppingDecomposition
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.unusedVariables false
open Lean Elab Command

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_0 : (∀ (z : ℝ),
    chosenLogAction z = decide (0 < z)) := by exact @Thesis.RoutingGate.chosenLogAction_eq_positive
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.chosenLogAction_eq_positive
  let expected ← getConstInfo `GamesExpectedTypes.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.chosenLogAction_eq_positive"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.chosenLogAction_eq_positive | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.chosenLogAction_eq_positive"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.chosenLogAction_eq_positive"
#print axioms GamesExpectedTypes.target_0

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_1 : (∀ (z : ℝ) (cont : Bool),
    logAction z cont ≤ logAction z (chosenLogAction z)) := by exact @Thesis.RoutingGate.chosenLogAction_optimal
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.chosenLogAction_optimal
  let expected ← getConstInfo `GamesExpectedTypes.target_1
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.chosenLogAction_optimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.chosenLogAction_optimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.chosenLogAction_optimal"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.chosenLogAction_optimal"
#print axioms GamesExpectedTypes.target_1

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_2 : (∀ (z : ℝ) (hz : z ≤ 0),
    chosenLogAction z = false) := by exact @Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive
  let expected ← getConstInfo `GamesExpectedTypes.target_2
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive"
#print axioms GamesExpectedTypes.target_2

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_3 : (∀ (z : ℝ),
    (if chosenLogAction z then z else 0) = max z 0) := by exact @Thesis.RoutingGate.chosenLogAction_mass
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.chosenLogAction_mass
  let expected ← getConstInfo `GamesExpectedTypes.target_3
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.chosenLogAction_mass"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.chosenLogAction_mass | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.chosenLogAction_mass"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.chosenLogAction_mass"
#print axioms GamesExpectedTypes.target_3

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_4 : (∀ (z : ℝ) (hz : z ≤ 0) (cont : Bool),
    logAction z cont = ⊥) := by exact @Thesis.RoutingGate.nonpositive_log_actions_tied
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.nonpositive_log_actions_tied
  let expected ← getConstInfo `GamesExpectedTypes.target_4
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.nonpositive_log_actions_tied"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.nonpositive_log_actions_tied | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.nonpositive_log_actions_tied"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.nonpositive_log_actions_tied"
#print axioms GamesExpectedTypes.target_4

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_5 : (∀ (z : ℝ) (hz : 0 < z),
    logAction z false < logAction z true) := by exact @Thesis.RoutingGate.positive_continue_strictly_better
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.positive_continue_strictly_better
  let expected ← getConstInfo `GamesExpectedTypes.target_5
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.positive_continue_strictly_better"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.positive_continue_strictly_better | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.positive_continue_strictly_better"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.positive_continue_strictly_better"
#print axioms GamesExpectedTypes.target_5

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_6 : (∀ (z : ℝ) (p : Set.Icc (0 : ℝ) 1),
    logPolicy z p ≤ logPolicy z (chosenLogPolicy z)) := by exact @Thesis.RoutingGate.chosenLogPolicy_optimal
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.chosenLogPolicy_optimal
  let expected ← getConstInfo `GamesExpectedTypes.target_6
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.chosenLogPolicy_optimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.chosenLogPolicy_optimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.chosenLogPolicy_optimal"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.chosenLogPolicy_optimal"
#print axioms GamesExpectedTypes.target_6

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_7 : (∀ (z : ℝ) (hz : z ≤ 0)
    (p : Set.Icc (0 : ℝ) 1),
    logPolicy z p = ⊥) := by exact @Thesis.RoutingGate.nonpositive_log_policies_tied
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.nonpositive_log_policies_tied
  let expected ← getConstInfo `GamesExpectedTypes.target_7
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.nonpositive_log_policies_tied"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.nonpositive_log_policies_tied | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.nonpositive_log_policies_tied"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.nonpositive_log_policies_tied"
#print axioms GamesExpectedTypes.target_7

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_8 : (∀ (z : ℝ) (hz : 0 < z)
    (p : Set.Icc (0 : ℝ) 1) (hp : p.val < 1),
    logPolicy z p < logPolicy z (chosenLogPolicy z)) := by exact @Thesis.RoutingGate.positive_log_policy_strict
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.positive_log_policy_strict
  let expected ← getConstInfo `GamesExpectedTypes.target_8
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.positive_log_policy_strict"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.positive_log_policy_strict | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.positive_log_policy_strict"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.positive_log_policy_strict"
#print axioms GamesExpectedTypes.target_8

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_9 : (∀ (c z : ℝ),
    HasDerivAt (frozenGate c) c z) := by exact @Thesis.RoutingGate.frozenGate_hasDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.frozenGate_hasDerivAt
  let expected ← getConstInfo `GamesExpectedTypes.target_9
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.frozenGate_hasDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.frozenGate_hasDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.frozenGate_hasDerivAt"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.frozenGate_hasDerivAt"
#print axioms GamesExpectedTypes.target_9

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_10 : (∀ (c z : ℝ) (hc : 0 ≤ c) (hz : 0 ≤ z),
    0 ≤ frozenGate c z) := by exact @Thesis.RoutingGate.frozenGate_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.frozenGate_nonnegative
  let expected ← getConstInfo `GamesExpectedTypes.target_10
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.frozenGate_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.frozenGate_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.frozenGate_nonnegative"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.frozenGate_nonnegative"
#print axioms GamesExpectedTypes.target_10

section
open Thesis.RoutingGate
theorem GamesExpectedTypes.target_11 : (∀ (g : ℝ → ℝ) (z d : ℝ) (hg : HasDerivAt g d z),
    HasDerivAt (fun y => g y * y) (g z + z*d) z) := by exact @Thesis.RoutingGate.varyingGate_hasDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingGate.varyingGate_hasDerivAt
  let expected ← getConstInfo `GamesExpectedTypes.target_11
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingGate.varyingGate_hasDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingGate.varyingGate_hasDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingGate do
    throwError "Defining module mismatch: Thesis.RoutingGate.varyingGate_hasDerivAt"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingGate.varyingGate_hasDerivAt"
#print axioms GamesExpectedTypes.target_11

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
theorem GamesExpectedTypes.target_12 : (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (g : Fin k → Bool) (j : Fin k) (turn : Bool),
    (∑ target, transition wp wn g j turn target) = 1) := by exact @Thesis.StoppingBoundary.transition_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.transition_normalized
  let expected ← getConstInfo `GamesExpectedTypes.target_12
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.transition_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.transition_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.transition_normalized"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.transition_normalized"
#print axioms GamesExpectedTypes.target_12

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
theorem GamesExpectedTypes.target_13 : (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (g : Fin k → Bool) (hw : ∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i)
    (j : Fin k) (turn : Bool) (target : Option (Fin n × Bool)),
    0 ≤ transition wp wn g j turn target) := by exact @Thesis.StoppingBoundary.transition_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.transition_nonnegative
  let expected ← getConstInfo `GamesExpectedTypes.target_13
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.transition_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.transition_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.transition_nonnegative"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.transition_nonnegative"
#print axioms GamesExpectedTypes.target_13

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
theorem GamesExpectedTypes.target_14 : (∀ {n m} (tr : MaskedTrace n m)
    (hw : NonnegativeWeights tr) (j : Fin m) (i : Fin n) (p : Bool) (path : Paths tr),
    sgDiscount tr path * sgProbability tr j i p path = rawWeight tr j i p path) := by exact @Thesis.StoppingBoundary.path_discount_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.path_discount_recovery
  let expected ← getConstInfo `GamesExpectedTypes.target_14
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.path_discount_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.path_discount_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.path_discount_recovery"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.path_discount_recovery"
#print axioms GamesExpectedTypes.target_14

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
theorem GamesExpectedTypes.target_15 : (∀ {n m} (tr : MaskedTrace n m) (hw : NonnegativeWeights tr)
    (j : Fin m) (i : Fin n),
    tr.originalJac (Pi.single i 1) j = sgOccupation tr j i false - sgOccupation tr j i true) := by exact @Thesis.StoppingBoundary.selected_operator_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.selected_operator_occupation
  let expected ← getConstInfo `GamesExpectedTypes.target_15
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.selected_operator_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.selected_operator_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.selected_operator_occupation"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.selected_operator_occupation"
#print axioms GamesExpectedTypes.target_15

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
theorem GamesExpectedTypes.target_16 : (∀ {n m} (net : Network n m) (x : Vec n)
    (hx : net.Strict x) (hw : NonnegativeWeights (net.originalTrace x))
    (j : Fin m) (i : Fin n),
    fderiv ℝ net.eval x (Pi.single i 1) j =
      sgOccupation (net.originalTrace x) j i false - sgOccupation (net.originalTrace x) j i true) := by exact @Thesis.StoppingBoundary.strict_gradient_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.strict_gradient_occupation
  let expected ← getConstInfo `GamesExpectedTypes.target_16
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.strict_gradient_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.strict_gradient_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.strict_gradient_occupation"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.strict_gradient_occupation"
#print axioms GamesExpectedTypes.target_16

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
theorem GamesExpectedTypes.target_17 : (∀ {n m} (net : Network n m)
    (x : PairVec n) (hx : net.Strict (x.1-x.2))
    (hw : NonnegativeWeights (net.originalTrace (x.1-x.2))) (j : Fin m) (i : Fin n),
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).1 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i false ∧
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).2 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i true) := by exact @Thesis.StoppingBoundary.strict_stopping_decomposition_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.strict_stopping_decomposition_gradient
  let expected ← getConstInfo `GamesExpectedTypes.target_17
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.strict_stopping_decomposition_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.strict_stopping_decomposition_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.strict_stopping_decomposition_gradient"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.strict_stopping_decomposition_gradient"
#print axioms GamesExpectedTypes.target_17

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition Thesis.StoppingBoundary
theorem GamesExpectedTypes.target_18 : (∀ {n m r} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (x : Vec n) (hx : net.Strict x)
    (hw : NonnegativeWeights (net.originalTrace x)) (u : Fin r) (i : Fin n),
    fderiv ℝ (Thesis.AffineOutputBackward.affineOutput net C b) x (Pi.single i 1) u =
      ∑ j, C u j * (sgOccupation (net.originalTrace x) j i false -
        sgOccupation (net.originalTrace x) j i true)) := by exact @Thesis.StoppingBoundary.strict_affine_output_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingBoundary.strict_affine_output_gradient
  let expected ← getConstInfo `GamesExpectedTypes.target_18
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingBoundary.strict_affine_output_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingBoundary.strict_affine_output_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingBoundary do
    throwError "Defining module mismatch: Thesis.StoppingBoundary.strict_affine_output_gradient"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingBoundary.strict_affine_output_gradient"
#print axioms GamesExpectedTypes.target_18

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.SoftplusBackward Thesis.Regularization Thesis.SoftplusBoundary
theorem GamesExpectedTypes.target_19 : (∀ {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (j : Fin k) (turn : Bool),
    (∑ target, transition θ z wp wn j turn target) = 1) := by exact @Thesis.SoftplusBoundary.transition_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusBoundary.transition_normalized
  let expected ← getConstInfo `GamesExpectedTypes.target_19
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusBoundary.transition_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusBoundary.transition_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusBoundary do
    throwError "Defining module mismatch: Thesis.SoftplusBoundary.transition_normalized"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusBoundary.transition_normalized"
#print axioms GamesExpectedTypes.target_19

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.SoftplusBackward Thesis.Regularization Thesis.SoftplusBoundary
theorem GamesExpectedTypes.target_20 : (∀ {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i)
    (j : Fin k) (turn : Bool) (target : Option (Fin n × Bool)),
    0 ≤ transition θ z wp wn j turn target) := by exact @Thesis.SoftplusBoundary.transition_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusBoundary.transition_nonnegative
  let expected ← getConstInfo `GamesExpectedTypes.target_20
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusBoundary.transition_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusBoundary.transition_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusBoundary do
    throwError "Defining module mismatch: Thesis.SoftplusBoundary.transition_nonnegative"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusBoundary.transition_nonnegative"
#print axioms GamesExpectedTypes.target_20

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.SoftplusBackward Thesis.Regularization Thesis.SoftplusBoundary
theorem GamesExpectedTypes.target_21 : (∀ {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (j : Fin k) (turn : Bool) (hz : fanIn wp wn j = 0),
    transition θ z wp wn j turn none = 1) := by exact @Thesis.SoftplusBoundary.zero_fanIn_absorbs
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusBoundary.zero_fanIn_absorbs
  let expected ← getConstInfo `GamesExpectedTypes.target_21
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusBoundary.zero_fanIn_absorbs"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusBoundary.zero_fanIn_absorbs | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusBoundary do
    throwError "Defining module mismatch: Thesis.SoftplusBoundary.zero_fanIn_absorbs"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusBoundary.zero_fanIn_absorbs"
#print axioms GamesExpectedTypes.target_21

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.SoftplusBackward Thesis.Regularization Thesis.SoftplusBoundary
theorem GamesExpectedTypes.target_22 : (∀ {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (hw : net.Nonnegative) (x : Vec n) (j : Fin m) (i : Fin n),
    fderiv ℝ (softEval θ net) x (Pi.single i 1) j =
      softOccupation net θ x j i false - softOccupation net θ x j i true) := by exact @Thesis.SoftplusBoundary.gradient_occupation
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusBoundary.gradient_occupation
  let expected ← getConstInfo `GamesExpectedTypes.target_22
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusBoundary.gradient_occupation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusBoundary.gradient_occupation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusBoundary do
    throwError "Defining module mismatch: Thesis.SoftplusBoundary.gradient_occupation"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusBoundary.gradient_occupation"
#print axioms GamesExpectedTypes.target_22

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingSupport
theorem GamesExpectedTypes.target_23 : (∀ {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (R : Vec m) (hR : ∀ j, net.eval x j = 0 → R j = 0),
    sourceLRP α β ε net x R = lrp α β ε net x R) := by exact @Thesis.RoutingSupport.sourceLRP_eq_lrp
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.sourceLRP_eq_lrp
  let expected ← getConstInfo `GamesExpectedTypes.target_23
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.sourceLRP_eq_lrp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.sourceLRP_eq_lrp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.sourceLRP_eq_lrp"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.sourceLRP_eq_lrp"
#print axioms GamesExpectedTypes.target_23

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingSupport
theorem GamesExpectedTypes.target_24 : (∀ {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (R : Vec m) (hR : ∀ j, net.eval x j = 0 → R j = 0) (i : Fin n),
    sourceLRP α β ε net x R i = ∑ j, R j *
      (rgOccupation net α β ε x j i false - rgOccupation net α β ε x j i true)) := by exact @Thesis.RoutingSupport.source_alpha_beta_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.source_alpha_beta_recovery
  let expected ← getConstInfo `GamesExpectedTypes.target_24
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.source_alpha_beta_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.source_alpha_beta_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.source_alpha_beta_recovery"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.source_alpha_beta_recovery"
#print axioms GamesExpectedTypes.target_24

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingSupport
theorem GamesExpectedTypes.target_25 : (∀ {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (i : Fin n),
    sourceLRP α β ε net x (net.eval x) i = ∑ j, net.eval x j *
      (rgOccupation net α β ε x j i false - rgOccupation net α β ε x j i true)) := by exact @Thesis.RoutingSupport.source_alpha_beta_output_seed
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.source_alpha_beta_output_seed
  let expected ← getConstInfo `GamesExpectedTypes.target_25
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.source_alpha_beta_output_seed"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.source_alpha_beta_output_seed | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.source_alpha_beta_output_seed"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.source_alpha_beta_output_seed"
#print axioms GamesExpectedTypes.target_25

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingSupport
theorem GamesExpectedTypes.target_26 : (∀ {n m r} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (x : Vec n) (R : Vec r),
    sourceAffineOutputLRP net C b α β ε x R =
      Thesis.AffineOutputBackward.affineOutputLRP net C b α β ε x R) := by exact @Thesis.RoutingSupport.sourceAffineOutputLRP_eq
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.sourceAffineOutputLRP_eq
  let expected ← getConstInfo `GamesExpectedTypes.target_26
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.sourceAffineOutputLRP_eq"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.sourceAffineOutputLRP_eq | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.sourceAffineOutputLRP_eq"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.sourceAffineOutputLRP_eq"
#print axioms GamesExpectedTypes.target_26

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingSupport
theorem GamesExpectedTypes.target_27 : (∀ {n m r} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ)
    (x : Vec n) (R : Vec r) (i : Fin n),
    sourceAffineOutputLRP net C b α β ε x R i = ∑ u, R u *
      (Thesis.AffineOutputBackward.readoutOccupation net C b α β ε x u i false -
       Thesis.AffineOutputBackward.readoutOccupation net C b α β ε x u i true)) := by exact @Thesis.RoutingSupport.source_affine_output_lrp
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingSupport.source_affine_output_lrp
  let expected ← getConstInfo `GamesExpectedTypes.target_27
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingSupport.source_affine_output_lrp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingSupport.source_affine_output_lrp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingSupport do
    throwError "Defining module mismatch: Thesis.RoutingSupport.source_affine_output_lrp"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingSupport.source_affine_output_lrp"
#print axioms GamesExpectedTypes.target_27

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingTransitions
theorem GamesExpectedTypes.target_28 : (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (x : Vec n) (j : Fin k) (turn : Bool),
    (∑ target, transition wp wn bp bn ε x j turn target) = 1) := by exact @Thesis.RoutingTransitions.transition_normalized
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingTransitions.transition_normalized
  let expected ← getConstInfo `GamesExpectedTypes.target_28
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingTransitions.transition_normalized"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingTransitions.transition_normalized | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingTransitions do
    throwError "Defining module mismatch: Thesis.RoutingTransitions.transition_normalized"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingTransitions.transition_normalized"
#print axioms GamesExpectedTypes.target_28

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingTransitions
theorem GamesExpectedTypes.target_29 : (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k)
    (turn : Bool) (target : Option (Fin n × Bool)),
    0 ≤ transition wp wn bp bn ε x j turn target) := by exact @Thesis.RoutingTransitions.transition_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingTransitions.transition_nonnegative
  let expected ← getConstInfo `GamesExpectedTypes.target_29
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingTransitions.transition_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingTransitions.transition_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingTransitions do
    throwError "Defining module mismatch: Thesis.RoutingTransitions.transition_nonnegative"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingTransitions.transition_nonnegative"
#print axioms GamesExpectedTypes.target_29

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingTransitions
theorem GamesExpectedTypes.target_30 : (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (x : Vec n) (j : Fin k) (turn p : Bool) (i : Fin n),
    transition wp wn bp bn ε x j turn (some (i,p)) =
      if 0 < preactivation wp wn bp bn x j then
        (if p = turn then posContribution wp wn x j i / posDenominator wp wn bp bn ε x j
         else negContribution wp wn x j i / negDenominator wp wn bp bn ε x j) / 2 else 0) := by exact @Thesis.RoutingTransitions.transition_ordinary
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingTransitions.transition_ordinary
  let expected ← getConstInfo `GamesExpectedTypes.target_30
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingTransitions.transition_ordinary"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingTransitions.transition_ordinary | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingTransitions do
    throwError "Defining module mismatch: Thesis.RoutingTransitions.transition_ordinary"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingTransitions.transition_ordinary"
#print axioms GamesExpectedTypes.target_30

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingTransitions
theorem GamesExpectedTypes.target_31 : (∀ {n m} (net : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (i : Fin n) (p : Bool)
    (path : Paths (routingTrace α β ε net x)),
    0 ≤ rgProbability α β ε net x j i p path) := by exact @Thesis.RoutingTransitions.probability_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingTransitions.probability_nonnegative
  let expected ← getConstInfo `GamesExpectedTypes.target_31
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingTransitions.probability_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingTransitions.probability_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingTransitions do
    throwError "Defining module mismatch: Thesis.RoutingTransitions.probability_nonnegative"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingTransitions.probability_nonnegative"
#print axioms GamesExpectedTypes.target_31

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.RoutingTransitions
theorem GamesExpectedTypes.target_32 : (∀ {n m} (net : Network n m) (α β ε : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 ≤ ε) (x : Vec n)
    (j : Fin m) (i : Fin n) (p : Bool),
    0 ≤ rgOccupation net α β ε x j i p) := by exact @Thesis.RoutingTransitions.occupation_nonnegative
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingTransitions.occupation_nonnegative
  let expected ← getConstInfo `GamesExpectedTypes.target_32
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingTransitions.occupation_nonnegative"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingTransitions.occupation_nonnegative | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingTransitions do
    throwError "Defining module mismatch: Thesis.RoutingTransitions.occupation_nonnegative"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingTransitions.occupation_nonnegative"
#print axioms GamesExpectedTypes.target_32

section
universe u
open MeasureTheory Filter Finset Thesis.Games Thesis.Randomization Thesis.RandomizationExpectation Thesis.RoutingExpectation
open scoped MeasureTheory
theorem GamesExpectedTypes.target_33 : (∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {S : Type} [Fintype S] [DecidableEq S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) (s₀ : S)
    (b : ℝ) (hb : 0 ≤ b)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (rowAffinity A B n s) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s *
      rowAffinity A B n s ω) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n]
      (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (n : ℕ) (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ, μ[rowAffinity A B l s | ℱ l] ω ≤ b),
    (∫ ω, ordinaryOverlap n A (fun l => B l ω) s₀ ∂μ) ≤ b^n) := by exact @Thesis.RoutingExpectation.conditional_affinity_contraction.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExpectation.conditional_affinity_contraction
  let expected ← getConstInfo `GamesExpectedTypes.target_33
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExpectation.conditional_affinity_contraction"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExpectation.conditional_affinity_contraction | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExpectation do
    throwError "Defining module mismatch: Thesis.RoutingExpectation.conditional_affinity_contraction"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExpectation.conditional_affinity_contraction"
#print axioms GamesExpectedTypes.target_33

section
universe u
open MeasureTheory Filter Finset Thesis.Games Thesis.Randomization Thesis.RandomizationExpectation Thesis.RoutingExpectation
open scoped MeasureTheory
theorem GamesExpectedTypes.target_34 : (∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {S : Type} [Fintype S] [DecidableEq S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) (s₀ : S)
    (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ n s t, 0 ≤ A n s t) (hB : ∀ n ω s t, 0 ≤ B n ω s t)
    (hArow : ∀ n s, ∑ t, A n s t ≤ 1) (hBrow : ∀ n ω s, ∑ t, B n ω s t ≤ 1)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (rowAffinity A B n s) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s *
      rowAffinity A B n s ω) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n]
      (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (n extra : ℕ)
    (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ, μ[rowAffinity A B l s | ℱ l] ω ≤ b),
    (∫ ω, ordinaryOverlap (n+extra) A (fun l => B l ω) s₀ ∂μ) ≤ b^n) := by exact @Thesis.RoutingExpectation.conditional_affinity_full_depth.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExpectation.conditional_affinity_full_depth
  let expected ← getConstInfo `GamesExpectedTypes.target_34
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExpectation.conditional_affinity_full_depth"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExpectation.conditional_affinity_full_depth | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExpectation do
    throwError "Defining module mismatch: Thesis.RoutingExpectation.conditional_affinity_full_depth"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExpectation.conditional_affinity_full_depth"
#print axioms GamesExpectedTypes.target_34

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames
theorem GamesExpectedTypes.target_35 : (∀ {n m} (net : Network n m) (x : Vec n)
    (hx : net.Regular (x,0)) (hγ : PositiveFanIn (net.trace (x,0))),
    HasFDerivAt net.eval (matrixCLM (fun j i =>
      sgOccupation (net.trace (x,0)) j i false -
      sgOccupation (net.trace (x,0)) j i true)) x) := by exact @Thesis.BackwardGames.stopping_game_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.BackwardGames.stopping_game_gradient
  let expected ← getConstInfo `GamesExpectedTypes.target_35
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.BackwardGames.stopping_game_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.BackwardGames.stopping_game_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.BackwardGames do
    throwError "Defining module mismatch: Thesis.BackwardGames.stopping_game_gradient"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.BackwardGames.stopping_game_gradient"
#print axioms GamesExpectedTypes.target_35

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames
theorem GamesExpectedTypes.target_36 : (∀ {n m} (net : Network n m) (x : Vec n)
    (hx : net.Regular (x,0)) (hγ : PositiveFanIn (net.trace (x,0)))
    (_hw : NonnegativeWeights (net.trace (x,0)))
    (j : Fin m) (i : Fin n),
    fderiv ℝ net.eval x (Pi.single i 1) j =
      sgOccupation (net.trace (x,0)) j i false - sgOccupation (net.trace (x,0)) j i true) := by exact @Thesis.BackwardGames.thesis_gradient_representation
end
run_cmd do
  let target ← getConstInfo `Thesis.BackwardGames.thesis_gradient_representation
  let expected ← getConstInfo `GamesExpectedTypes.target_36
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.BackwardGames.thesis_gradient_representation"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.BackwardGames.thesis_gradient_representation | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.BackwardGames do
    throwError "Defining module mismatch: Thesis.BackwardGames.thesis_gradient_representation"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.BackwardGames.thesis_gradient_representation"
#print axioms GamesExpectedTypes.target_36

section
open HiddenMonotonicity Matrix Finset Filter Thesis.BackwardGames Thesis.StoppingDecomposition
open scoped Topology
theorem GamesExpectedTypes.target_37 : (∀ {n m} (net : Network n m) (x : PairVec n),
    (net.decomposeWith stopPair x).1 - (net.decomposeWith stopPair x).2 = net.eval (x.1-x.2)) := by exact @Thesis.StoppingDecomposition.thesis_stopping_validity
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDecomposition.thesis_stopping_validity
  let expected ← getConstInfo `GamesExpectedTypes.target_37
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDecomposition.thesis_stopping_validity"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDecomposition.thesis_stopping_validity | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDecomposition do
    throwError "Defining module mismatch: Thesis.StoppingDecomposition.thesis_stopping_validity"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDecomposition.thesis_stopping_validity"
#print axioms GamesExpectedTypes.target_37

section
open HiddenMonotonicity Matrix Finset Filter Thesis.BackwardGames Thesis.StoppingDecomposition
open scoped Topology
theorem GamesExpectedTypes.target_38 : (∀ {n m} (net : Network n m)
    (x : PairVec n) (hx : net.Strict (x.1-x.2))
    (hγ : Thesis.BackwardGames.PositiveFanIn (net.originalTrace (x.1-x.2)))
    (j : Fin m) (i : Fin n),
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).1 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i false ∧
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).2 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i true) := by exact @Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient
  let expected ← getConstInfo `GamesExpectedTypes.target_38
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.StoppingDecomposition do
    throwError "Defining module mismatch: Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.StoppingDecomposition.thesis_stopping_decomposition_gradient"
#print axioms GamesExpectedTypes.target_38

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward
theorem GamesExpectedTypes.target_39 : (∀ {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (R : Vec m) (i : Fin n),
    lrp α β ε net x R i = ∑ j, R j *
      (rgOccupation net α β ε x j i false - rgOccupation net α β ε x j i true)) := by exact @Thesis.RoutingBackward.thesis_alpha_beta_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingBackward.thesis_alpha_beta_recovery
  let expected ← getConstInfo `GamesExpectedTypes.target_39
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingBackward.thesis_alpha_beta_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingBackward.thesis_alpha_beta_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingBackward do
    throwError "Defining module mismatch: Thesis.RoutingBackward.thesis_alpha_beta_recovery"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingBackward.thesis_alpha_beta_recovery"
#print axioms GamesExpectedTypes.target_39

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.AttentionBackward Thesis.AffineOutputBackward
theorem GamesExpectedTypes.target_40 : (∀ {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (x : Vec n) (hx : net.Strict x) (hγ : PositiveFanIn (net.originalTrace x))
    (u : Fin r) (i : Fin n),
    fderiv ℝ (affineOutput net C b) x (Pi.single i 1) u =
      ∑ j, C u j * (sgOccupation (net.originalTrace x) j i false -
        sgOccupation (net.originalTrace x) j i true)) := by exact @Thesis.AffineOutputBackward.thesis_affine_output_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.AffineOutputBackward.thesis_affine_output_gradient
  let expected ← getConstInfo `GamesExpectedTypes.target_40
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AffineOutputBackward.thesis_affine_output_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AffineOutputBackward.thesis_affine_output_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AffineOutputBackward do
    throwError "Defining module mismatch: Thesis.AffineOutputBackward.thesis_affine_output_gradient"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AffineOutputBackward.thesis_affine_output_gradient"
#print axioms GamesExpectedTypes.target_40

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.AttentionBackward Thesis.AffineOutputBackward
theorem GamesExpectedTypes.target_41 : (∀ {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (α β ε : ℝ) (x : Vec n) (R : Vec r) (i : Fin n),
    affineOutputLRP net C b α β ε x R i = ∑ u, R u *
      (readoutOccupation net C b α β ε x u i false -
       readoutOccupation net C b α β ε x u i true)) := by exact @Thesis.AffineOutputBackward.thesis_affine_output_lrp
end
run_cmd do
  let target ← getConstInfo `Thesis.AffineOutputBackward.thesis_affine_output_lrp
  let expected ← getConstInfo `GamesExpectedTypes.target_41
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AffineOutputBackward.thesis_affine_output_lrp"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AffineOutputBackward.thesis_affine_output_lrp | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AffineOutputBackward do
    throwError "Defining module mismatch: Thesis.AffineOutputBackward.thesis_affine_output_lrp"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AffineOutputBackward.thesis_affine_output_lrp"
#print axioms GamesExpectedTypes.target_41

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.Regularization Thesis.SoftplusBackward
theorem GamesExpectedTypes.target_42 : (∀ {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (_hw : net.Nonnegative) (hγ : PositiveFanIn net) (x : Vec n) (j : Fin m) (i : Fin n),
    fderiv ℝ (softEval θ net) x (Pi.single i 1) j =
      softOccupation net θ x j i false - softOccupation net θ x j i true) := by exact @Thesis.SoftplusBackward.thesis_softplus_gradient
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusBackward.thesis_softplus_gradient
  let expected ← getConstInfo `GamesExpectedTypes.target_42
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusBackward.thesis_softplus_gradient"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusBackward.thesis_softplus_gradient | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusBackward do
    throwError "Defining module mismatch: Thesis.SoftplusBackward.thesis_softplus_gradient"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusBackward.thesis_softplus_gradient"
#print axioms GamesExpectedTypes.target_42

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.SoftplusDecomposition
theorem GamesExpectedTypes.target_43 : (∀ {n m} (net : Network n m) (θ : ℝ),
    softEval θ net = net.forwardWith (softplus θ)) := by exact @Thesis.SoftplusDecomposition.softEval_eq_forwardWith
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusDecomposition.softEval_eq_forwardWith
  let expected ← getConstInfo `GamesExpectedTypes.target_43
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusDecomposition.softEval_eq_forwardWith"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusDecomposition.softEval_eq_forwardWith | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusDecomposition do
    throwError "Defining module mismatch: Thesis.SoftplusDecomposition.softEval_eq_forwardWith"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusDecomposition.softEval_eq_forwardWith"
#print axioms GamesExpectedTypes.target_43

section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.SoftplusDecomposition
theorem GamesExpectedTypes.target_44 : (∀ {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (x : PairVec n),
    (net.decomposeWith (fun z => softSplit θ z.1 z.2) x).1 -
      (net.decomposeWith (fun z => softSplit θ z.1 z.2) x).2 = softEval θ net (x.1-x.2)) := by exact @Thesis.SoftplusDecomposition.thesis_softplus_forward
end
run_cmd do
  let target ← getConstInfo `Thesis.SoftplusDecomposition.thesis_softplus_forward
  let expected ← getConstInfo `GamesExpectedTypes.target_44
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.SoftplusDecomposition.thesis_softplus_forward"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.SoftplusDecomposition.thesis_softplus_forward | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.SoftplusDecomposition do
    throwError "Defining module mismatch: Thesis.SoftplusDecomposition.thesis_softplus_forward"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.SoftplusDecomposition.thesis_softplus_forward"
#print axioms GamesExpectedTypes.target_44

section
open Thesis.Regularization
theorem GamesExpectedTypes.target_45 : (∀ (θ z : ℝ) (hθ : 0 < θ),
    IsGreatest ((fun p : ℝ => p * z + θ * Real.binEntropy p) '' Set.Icc 0 1)
      (softplus θ z)) := by exact @Thesis.Regularization.softplus_variational
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.softplus_variational
  let expected ← getConstInfo `GamesExpectedTypes.target_45
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Regularization.softplus_variational"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.softplus_variational | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.softplus_variational"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.softplus_variational"
#print axioms GamesExpectedTypes.target_45

section
open Thesis.Regularization
theorem GamesExpectedTypes.target_46 : (∀ (θ z p : ℝ) (hθ : 0 < θ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1),
    p * z + θ * Real.binEntropy p = softplus θ z ↔ p = gate θ z) := by exact @Thesis.Regularization.entropy_gate_unique
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.entropy_gate_unique
  let expected ← getConstInfo `GamesExpectedTypes.target_46
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Regularization.entropy_gate_unique"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.entropy_gate_unique | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.entropy_gate_unique"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.entropy_gate_unique"
#print axioms GamesExpectedTypes.target_46

section
universe u
open Thesis.Regularization
theorem GamesExpectedTypes.target_47 : (∀ {A : Type u} [Fintype A] [Nonempty A] (θ : ℝ) (q : A → ℝ) (hθ : 0 < θ),
    IsGreatest ((fun p : A → ℝ => (∑ i, p i * q i) + θ * entropy p) ''
      {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}) (logPartition θ q)) := by exact @Thesis.Regularization.routing_variational.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.routing_variational
  let expected ← getConstInfo `GamesExpectedTypes.target_47
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Regularization.routing_variational"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.routing_variational | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.routing_variational"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.routing_variational"
#print axioms GamesExpectedTypes.target_47

section
universe u
open Finset Thesis.Regularization Thesis.ReferencePolicy
theorem GamesExpectedTypes.target_48 : (∀ {A : Type u} [Fintype A] [Nonempty A] (θ : ℝ) (ρ q : A → ℝ) (hθ : 0 < θ)
    (hρ : ∀ i, 0 < ρ i),
    IsGreatest ((fun p : A → ℝ => (∑ i, p i * q i) - θ * kl p ρ) ''
      {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}) (referenceValue θ ρ q)) := by exact @Thesis.ReferencePolicy.thesis_kl_legendre_fenchel.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.ReferencePolicy.thesis_kl_legendre_fenchel
  let expected ← getConstInfo `GamesExpectedTypes.target_48
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.ReferencePolicy.thesis_kl_legendre_fenchel"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReferencePolicy.thesis_kl_legendre_fenchel | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReferencePolicy do
    throwError "Defining module mismatch: Thesis.ReferencePolicy.thesis_kl_legendre_fenchel"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReferencePolicy.thesis_kl_legendre_fenchel"
#print axioms GamesExpectedTypes.target_48

section
universe u
open Finset Thesis.Regularization Thesis.ReferencePolicy
theorem GamesExpectedTypes.target_49 : (∀ {A : Type u} [Fintype A] [Nonempty A] (θ : ℝ) (ρ q p : A → ℝ) (hθ : 0 < θ)
    (hρ : ∀ i, 0 < ρ i) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1),
    (∑ i, p i * q i) - θ * kl p ρ = referenceValue θ ρ q ↔ p = referencePolicy θ ρ q) := by exact @Thesis.ReferencePolicy.reference_policy_unique.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.ReferencePolicy.reference_policy_unique
  let expected ← getConstInfo `GamesExpectedTypes.target_49
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.ReferencePolicy.reference_policy_unique"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReferencePolicy.reference_policy_unique | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReferencePolicy do
    throwError "Defining module mismatch: Thesis.ReferencePolicy.reference_policy_unique"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReferencePolicy.reference_policy_unique"
#print axioms GamesExpectedTypes.target_49

section
universe u
open Finset Thesis.Regularization Thesis.ReferencePolicy
theorem GamesExpectedTypes.target_50 : (∀ {A : Type u} [Fintype A] [Nonempty A] (ρ u : A → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hu : ∀ i, 0 < u i),
    IsGreatest ((fun p : A → ℝ => (∑ i, p i * Real.log (u i)) - kl p ρ) ''
      {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}) (Real.log (∑ i, ρ i * u i))) := by exact @Thesis.ReferencePolicy.thesis_attention_value_policy.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.ReferencePolicy.thesis_attention_value_policy
  let expected ← getConstInfo `GamesExpectedTypes.target_50
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.ReferencePolicy.thesis_attention_value_policy"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.ReferencePolicy.thesis_attention_value_policy | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.ReferencePolicy do
    throwError "Defining module mismatch: Thesis.ReferencePolicy.thesis_attention_value_policy"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.ReferencePolicy.thesis_attention_value_policy"
#print axioms GamesExpectedTypes.target_50

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.AttentionBackward
theorem GamesExpectedTypes.target_51 : (∀ {T K C D : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (x : Vec (K*D)),
    HasFDerivAt (conditionedAttention A Wv bv) (matrixCLM (effectiveWeight A Wv)) x) := by exact @Thesis.AttentionBackward.conditionedAttention_hasFDerivAt
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionBackward.conditionedAttention_hasFDerivAt
  let expected ← getConstInfo `GamesExpectedTypes.target_51
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AttentionBackward.conditionedAttention_hasFDerivAt"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionBackward.conditionedAttention_hasFDerivAt | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionBackward do
    throwError "Defining module mismatch: Thesis.AttentionBackward.conditionedAttention_hasFDerivAt"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionBackward.conditionedAttention_hasFDerivAt"
#print axioms GamesExpectedTypes.target_51

section
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.AttentionBackward
theorem GamesExpectedTypes.target_52 : (∀ {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (_hε : 0 < ε)
    (_hA : ∀ t k, 0 ≤ A t k) (_hA1 : ∀ t, ∑ k, A t k = 1)
    (x : Vec (K*D)) (R : Vec m) (i : Fin (K*D)),
    attentionLRP A Wv bv tail α β ε x R i = ∑ j, R j *
      (attentionOccupation A Wv bv tail α β ε x j i false -
       attentionOccupation A Wv bv tail α β ε x j i true)) := by exact @Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery
  let expected ← getConstInfo `GamesExpectedTypes.target_52
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.AttentionBackward do
    throwError "Defining module mismatch: Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery"
#print axioms GamesExpectedTypes.target_52

section
open Finset Thesis.Games
theorem GamesExpectedTypes.target_53 : (∀ {S : Type} [Fintype S] (n : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t) (s : S),
    (∑ path : Paths S n, Real.sqrt (pathLaw n A s path * pathLaw n B s path)) =
      backwardDP n (fun i u v => Real.sqrt (A i u v * B i u v)) (fun _ => 1) s) := by exact @Thesis.Games.trajectory_overlap_eq_DP
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.trajectory_overlap_eq_DP
  let expected ← getConstInfo `GamesExpectedTypes.target_53
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Games.trajectory_overlap_eq_DP"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.trajectory_overlap_eq_DP | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.trajectory_overlap_eq_DP"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.trajectory_overlap_eq_DP"
#print axioms GamesExpectedTypes.target_53

section
open Finset Thesis.Games
theorem GamesExpectedTypes.target_54 : (∀ {S : Type} [Fintype S] (n : ℕ) (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ)
    (hh : ∀ i s, h i s ≠ 0) (hterminal : ∀ t, h n t = 1) (s : S) (path : Paths S n),
    pathLaw n (fun i u v => K i u v * h (i+1) v / h i u) s path =
      pathLaw n K s path / h 0 s) := by exact @Thesis.Games.doob_survival_path
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.doob_survival_path
  let expected ← getConstInfo `GamesExpectedTypes.target_54
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Games.doob_survival_path"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.doob_survival_path | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.doob_survival_path"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.doob_survival_path"
#print axioms GamesExpectedTypes.target_54

section
universe u
open Finset Thesis.Games
theorem GamesExpectedTypes.target_55 : (∀ {S : Type u} [Fintype S] (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1),
    (1/2 : ℝ) * (∑ s, (Real.sqrt (p s) - Real.sqrt (q s))^2) = 1-overlap p q) := by exact @Thesis.Games.hellinger_identity.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.hellinger_identity
  let expected ← getConstInfo `GamesExpectedTypes.target_55
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.hellinger_identity"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.hellinger_identity | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.hellinger_identity"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.hellinger_identity"
#print axioms GamesExpectedTypes.target_55

section
universe u
open Finset Thesis.Games
theorem GamesExpectedTypes.target_56 : (∀ {S : Type u} [Fintype S] (p q : S → ℝ) (ZA ZB : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (_hZA : 0 < ZA) (_hZB : 0 < ZB),
    overlap (fun s => p s / ZA) (fun s => q s / ZB) = overlap p q / Real.sqrt (ZA*ZB)) := by exact @Thesis.Games.survival_overlap.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.survival_overlap
  let expected ← getConstInfo `GamesExpectedTypes.target_56
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.survival_overlap"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.survival_overlap | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.survival_overlap"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.survival_overlap"
#print axioms GamesExpectedTypes.target_56

section
universe u
open Finset Thesis.Games
theorem GamesExpectedTypes.target_57 : (∀ {S : Type u} [Fintype S] (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hp1 : ∑ s, p s = 1) (hq1 : ∑ s, q s = 1),
    overlap p q = 1 ↔ p = q) := by exact @Thesis.Games.overlap_eq_one_iff.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.overlap_eq_one_iff
  let expected ← getConstInfo `GamesExpectedTypes.target_57
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.overlap_eq_one_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.overlap_eq_one_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.overlap_eq_one_iff"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.overlap_eq_one_iff"
#print axioms GamesExpectedTypes.target_57

section
universe u
open Finset Thesis.Games
theorem GamesExpectedTypes.target_58 : (∀ {S : Type u} [Fintype S] (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s),
    overlap p q = 0 ↔ ∀ s, p s = 0 ∨ q s = 0) := by exact @Thesis.Games.overlap_eq_zero_iff.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.overlap_eq_zero_iff
  let expected ← getConstInfo `GamesExpectedTypes.target_58
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.Games.overlap_eq_zero_iff"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.overlap_eq_zero_iff | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.overlap_eq_zero_iff"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.overlap_eq_zero_iff"
#print axioms GamesExpectedTypes.target_58

section
universe u v
open Finset Thesis.Games Thesis.Coarsening
theorem GamesExpectedTypes.target_59 : (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x),
    1 - overlap (pushforward f p) (pushforward f q) ≤ 1 - overlap p q) := by exact @Thesis.Coarsening.hellinger_coarsening.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Coarsening.hellinger_coarsening
  let expected ← getConstInfo `GamesExpectedTypes.target_59
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Coarsening.hellinger_coarsening"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Coarsening.hellinger_coarsening | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Coarsening do
    throwError "Defining module mismatch: Thesis.Coarsening.hellinger_coarsening"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Coarsening.hellinger_coarsening"
#print axioms GamesExpectedTypes.target_59

section
universe u v
open Finset Thesis.Games Thesis.Coarsening
theorem GamesExpectedTypes.target_60 : (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] (erase : X → Y) (recover : Y → X)
    (hleft : Function.LeftInverse recover erase) (hright : Function.RightInverse recover erase)
    (p q : X → ℝ),
    overlap (fun y => p (recover y)) (fun y => q (recover y)) = overlap p q) := by exact @Thesis.Coarsening.surviving_overlap_recovery.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Coarsening.surviving_overlap_recovery
  let expected ← getConstInfo `GamesExpectedTypes.target_60
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Coarsening.surviving_overlap_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Coarsening.surviving_overlap_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Coarsening do
    throwError "Defining module mismatch: Thesis.Coarsening.surviving_overlap_recovery"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Coarsening.surviving_overlap_recovery"
#print axioms GamesExpectedTypes.target_60

section
open Finset Thesis.Games Thesis.Randomization
theorem GamesExpectedTypes.target_61 : (∀ {S : Type} [Fintype S] (A B : Option S → ℝ)
    (hB : ∀ s, 0 ≤ B s) (hBsum : ∑ s, B s = 1) (hBdead : B none = 1),
    (∑ s, Real.sqrt (A (some s) * B (some s))) = 0) := by exact @Thesis.Randomization.thesis_alive_mismatch_ordinary
end
run_cmd do
  let target ← getConstInfo `Thesis.Randomization.thesis_alive_mismatch_ordinary
  let expected ← getConstInfo `GamesExpectedTypes.target_61
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Randomization.thesis_alive_mismatch_ordinary"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Randomization.thesis_alive_mismatch_ordinary | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Randomization do
    throwError "Defining module mismatch: Thesis.Randomization.thesis_alive_mismatch_ordinary"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Randomization.thesis_alive_mismatch_ordinary"
#print axioms GamesExpectedTypes.target_61

section
open Finset Thesis.Games Thesis.Randomization
theorem GamesExpectedTypes.target_62 : (∀ {S : Type} [Fintype S] (A B : Option S → ℝ)
    (hAstop : A none = 0) (hB : ∀ s, 0 ≤ B s) (hBsum : ∑ s, B s = 1) (hBdead : B none = 1),
    (∑ s, Real.sqrt (A s * B s)) = 0) := by exact @Thesis.Randomization.thesis_alive_mismatch_full
end
run_cmd do
  let target ← getConstInfo `Thesis.Randomization.thesis_alive_mismatch_full
  let expected ← getConstInfo `GamesExpectedTypes.target_62
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Randomization.thesis_alive_mismatch_full"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Randomization.thesis_alive_mismatch_full | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Randomization do
    throwError "Defining module mismatch: Thesis.Randomization.thesis_alive_mismatch_full"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Randomization.thesis_alive_mismatch_full"
#print axioms GamesExpectedTypes.target_62

section
open Finset Thesis.Games Thesis.Randomization
theorem GamesExpectedTypes.target_63 : (∀ {S : Type} [Fintype S] (n extra : ℕ) (A B : ℕ → S → S → ℝ)
    (aliveA aliveB : ℕ → S → Bool) (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1)
    (hA : ∀ l s t, 0 ≤ A l s t) (hB : ∀ l s t, 0 ≤ B l s t)
    (hArow : ∀ l s, ∑ t, A l s t ≤ 1) (hBrow : ∀ l s, ∑ t, B l s t ≤ 1)
    (hdeadA : ∀ l s, aliveA l s = false → ∀ t, A l s t = 0)
    (hdeadB : ∀ l s, aliveB l s = false → ∀ t, B l s t = 0)
    (hrow : ∀ l < n, ∀ s, aliveA l s = true ∧ aliveB l s = true →
      (∑ t, Real.sqrt (A l s t * B l s t)) ≤ b) (s : S),
    ordinaryOverlap (n+extra) A B s ≤ b^n) := by exact @Thesis.Randomization.thesis_randomization_routing_full_depth
end
run_cmd do
  let target ← getConstInfo `Thesis.Randomization.thesis_randomization_routing_full_depth
  let expected ← getConstInfo `GamesExpectedTypes.target_63
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Randomization.thesis_randomization_routing_full_depth"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Randomization.thesis_randomization_routing_full_depth | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Randomization do
    throwError "Defining module mismatch: Thesis.Randomization.thesis_randomization_routing_full_depth"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Randomization.thesis_randomization_routing_full_depth"
#print axioms GamesExpectedTypes.target_63

section
universe u
open MeasureTheory Filter Finset Thesis.Games Thesis.Randomization Thesis.RandomizationExpectation
open scoped MeasureTheory
theorem GamesExpectedTypes.target_64 : (∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {S : Type} [Fintype S] [DecidableEq S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) (alive : ℕ → Ω → S → Bool)
    (s₀ : S) (η : ℝ) (hη : 0 ≤ η)
    (hA : ∀ n s t, 0 ≤ A n s t) (hB : ∀ n ω s t, 0 ≤ B n ω s t)
    (hArow : ∀ n s, ∑ t, A n s t ≤ 1) (hBrow : ∀ n ω s, ∑ t, B n ω s t ≤ 1)
    (hdead : ∀ n ω s, alive n ω s = false → ∀ t, B n ω s t = 0)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (fun ω => if alive n ω s then (1:ℝ) else 0) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s *
      (if alive n ω s then (1:ℝ) else 0)) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n] (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (n extra : ℕ) (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ,
      μ[(fun ω => if alive l ω s then (1:ℝ) else 0) | ℱ l] ω ≤ η),
    (∫ ω, ordinaryOverlap (n+extra) A (fun l => B l ω) s₀ ∂μ) ≤ η^n) := by exact @Thesis.RandomizationExpectation.thesis_rand_adf_full_depth.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RandomizationExpectation.thesis_rand_adf_full_depth
  let expected ← getConstInfo `GamesExpectedTypes.target_64
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RandomizationExpectation.thesis_rand_adf_full_depth"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RandomizationExpectation.thesis_rand_adf_full_depth | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RandomizationExpectation do
    throwError "Defining module mismatch: Thesis.RandomizationExpectation.thesis_rand_adf_full_depth"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RandomizationExpectation.thesis_rand_adf_full_depth"
#print axioms GamesExpectedTypes.target_64

section
universe u
open MeasureTheory Filter Finset Thesis.Games Thesis.Randomization Thesis.RandomizationExpectation
open scoped MeasureTheory
theorem GamesExpectedTypes.target_65 : (∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c Z : Ω → ℝ) (z C : ℝ) (hz : 0 < z)
    (hc0 : ∀ᵐ ω ∂μ, 0 ≤ c ω) (hc : Integrable c μ)
    (hE : MeasurableSet {ω | z ≤ Z ω})
    (hH : Integrable (fun ω => if z ≤ Z ω then 1 - c ω / Real.sqrt (Z ω) else 0) μ)
    (hbound : (∫ ω, c ω ∂μ) ≤ C),
    μ.real {ω | z ≤ Z ω} - C / Real.sqrt z ≤
      ∫ ω, (if z ≤ Z ω then 1 - c ω / Real.sqrt (Z ω) else 0) ∂μ) := by exact @Thesis.RandomizationExpectation.thesis_conditioned_survival_lower.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RandomizationExpectation.thesis_conditioned_survival_lower
  let expected ← getConstInfo `GamesExpectedTypes.target_65
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RandomizationExpectation.thesis_conditioned_survival_lower"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RandomizationExpectation.thesis_conditioned_survival_lower | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RandomizationExpectation do
    throwError "Defining module mismatch: Thesis.RandomizationExpectation.thesis_conditioned_survival_lower"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RandomizationExpectation.thesis_conditioned_survival_lower"
#print axioms GamesExpectedTypes.target_65


section
universe u v
open Finset Thesis.Games Thesis.Coarsening
theorem GamesExpectedTypes.target_66 : (∀ {X : Type u} {Y : Type v} [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x),
    overlap p q ≤ overlap (pushforward f p) (pushforward f q)) := by exact @Thesis.Coarsening.overlap_coarsening.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Coarsening.overlap_coarsening
  let expected ← getConstInfo `GamesExpectedTypes.target_66
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Coarsening.overlap_coarsening"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Coarsening.overlap_coarsening | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Coarsening do
    throwError "Defining module mismatch: Thesis.Coarsening.overlap_coarsening"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Coarsening.overlap_coarsening"
#print axioms GamesExpectedTypes.target_66

section
universe u v
open Finset Thesis.Games
theorem GamesExpectedTypes.target_67 : (∀ {S : Type u} {T : Type v} [Fintype S] [Fintype T] (A B : S → T → ℝ)
    (hA : ∀ s t, 0 ≤ A s t) (hB : ∀ s t, 0 ≤ B s t)
    (hA1 : ∀ s, ∑ t, A s t = 1) (hB1 : ∀ s, ∑ t, B s t = 1) (s : S),
    (∑ t, Real.sqrt (A s t * B s t)) ≤ 1) := by exact @Thesis.Games.geometric_kernel_substochastic.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.geometric_kernel_substochastic
  let expected ← getConstInfo `GamesExpectedTypes.target_67
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Games.geometric_kernel_substochastic"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.geometric_kernel_substochastic | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.geometric_kernel_substochastic"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.geometric_kernel_substochastic"
#print axioms GamesExpectedTypes.target_67

section
open Finset Thesis.Games
theorem GamesExpectedTypes.target_68 : (∀ {S : Type} [Fintype S] (n : ℕ) (A B : ℕ → S → S → ℝ)
    (hA : ∀ i s t, 0 ≤ A i s t) (hB : ∀ i s t, 0 ≤ B i s t)
    (s : S) (path : Paths S n),
    Real.sqrt (pathLaw n A s path * pathLaw n B s path) =
      pathLaw n (fun i u v => Real.sqrt (A i u v * B i u v)) s path) := by exact @Thesis.Games.path_geometric_mean
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.path_geometric_mean
  let expected ← getConstInfo `GamesExpectedTypes.target_68
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Games.path_geometric_mean"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.path_geometric_mean | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.path_geometric_mean"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.path_geometric_mean"
#print axioms GamesExpectedTypes.target_68

section
universe u v
open Finset Thesis.Games
theorem GamesExpectedTypes.target_69 : (∀ {X : Type u} {Y : Type v} [Fintype X] [DecidableEq Y] (p q : X → ℝ) (terminal : X → Y)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (y : Y),
    0 ≤ pixelDisagreement p q terminal y) := by exact @Thesis.Games.pixelDisagreement_nonneg.{u, v}
end
run_cmd do
  let target ← getConstInfo `Thesis.Games.pixelDisagreement_nonneg
  let expected ← getConstInfo `GamesExpectedTypes.target_69
  unless target.levelParams.length == 2 && expected.levelParams.length == 2 do
    throwError "Universe arity mismatch: Thesis.Games.pixelDisagreement_nonneg"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Games.pixelDisagreement_nonneg | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Games do
    throwError "Defining module mismatch: Thesis.Games.pixelDisagreement_nonneg"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Games.pixelDisagreement_nonneg"
#print axioms GamesExpectedTypes.target_69

section
open Thesis.Regularization
theorem GamesExpectedTypes.target_70 : (∀ (θ u v : ℝ) (hθ : 0 < θ),
    (softSplit θ u v).1 - (softSplit θ u v).2 = softplus θ (u - v)) := by exact @Thesis.Regularization.softSplit_recovery
end
run_cmd do
  let target ← getConstInfo `Thesis.Regularization.softSplit_recovery
  let expected ← getConstInfo `GamesExpectedTypes.target_70
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.Regularization.softSplit_recovery"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.Regularization.softSplit_recovery | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.Regularization do
    throwError "Defining module mismatch: Thesis.Regularization.softSplit_recovery"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.Regularization.softSplit_recovery"
#print axioms GamesExpectedTypes.target_70

