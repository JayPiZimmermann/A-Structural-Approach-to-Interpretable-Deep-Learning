import Thesis.RoutingNetwork
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.unusedVariables false
open Lean Elab Command

section
open Finset Thesis.RoutingExtended
theorem GamesGlobalExpectedTypes.target_0 : (∀ (w : ℝ) (hw : 0 ≤ w) (v : WithBot ℝ),
    Thesis.RoutingGate.logCoordinate (w * expZero v) =
      Thesis.RoutingGate.logCoordinate w + v) := by exact @Thesis.RoutingExtended.source_edge_score
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.source_edge_score
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_0
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.source_edge_score"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.source_edge_score | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.source_edge_score"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.source_edge_score"
#print axioms GamesGlobalExpectedTypes.target_0

section
universe u
open Finset Thesis.RoutingExtended
theorem GamesGlobalExpectedTypes.target_1 : (∀ {A : Type u} [Fintype A] (θ : ℝ) (p : Policy A),
    Monotone (fun m => routedMass θ m p)) := by exact @Thesis.RoutingExtended.routedMass_monotone.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.routedMass_monotone
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_1
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.routedMass_monotone"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.routedMass_monotone | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.routedMass_monotone"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.routedMass_monotone"
#print axioms GamesGlobalExpectedTypes.target_1

section
universe u
open Finset Thesis.RoutingExtended
theorem GamesGlobalExpectedTypes.target_2 : (∀ {A : Type u} [Fintype A] [DecidableEq A] (θ : ℝ) (hθ : 0 < θ)
    (m : A → ℝ) (outside : A) (p : Policy A),
    sourceValue θ m p ≤ sourceValue θ m (gibbs θ m outside)) := by exact @Thesis.RoutingExtended.sourceValue_gibbs_optimal.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.sourceValue_gibbs_optimal
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_2
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.sourceValue_gibbs_optimal"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.sourceValue_gibbs_optimal | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.sourceValue_gibbs_optimal"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.sourceValue_gibbs_optimal"
#print axioms GamesGlobalExpectedTypes.target_2

section
universe u
open Finset Thesis.RoutingExtended
theorem GamesGlobalExpectedTypes.target_3 : (∀ {A : Type u} [Fintype A] [DecidableEq A] (m : A → ℝ) (hm : ∀ i, 0 ≤ m i) (outside : A),
    routedMass 1 m (gibbs 1 m outside) = ∑ i, m i) := by exact @Thesis.RoutingExtended.gibbs_anchor_mass.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.gibbs_anchor_mass
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_3
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.gibbs_anchor_mass"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.gibbs_anchor_mass | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.gibbs_anchor_mass"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.gibbs_anchor_mass"
#print axioms GamesGlobalExpectedTypes.target_3

section
universe u
open Finset Thesis.RoutingExtended
theorem GamesGlobalExpectedTypes.target_4 : (∀ {A : Type u} [Fintype A] [DecidableEq A] (m : A → ℝ) (hm : ∀ i, 0 ≤ m i)
    (outside i : A) (hi : i ≠ outside),
    (gibbs 1 m outside).prob i = m i / ∑ j, m j) := by exact @Thesis.RoutingExtended.gibbs_anchor_nonoutside.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.gibbs_anchor_nonoutside
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_4
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.gibbs_anchor_nonoutside"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.gibbs_anchor_nonoutside | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.gibbs_anchor_nonoutside"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.gibbs_anchor_nonoutside"
#print axioms GamesGlobalExpectedTypes.target_4

section
universe u
open Finset Thesis.RoutingExtended
theorem GamesGlobalExpectedTypes.target_5 : (∀ {A : Type u} [Fintype A] (θ : ℝ) (m : A → ℝ) (p : Policy A) (hm : ∀ i, m i ≤ 0),
    sourceValue θ m p = ⊥ ∧ routedMass θ m p = 0) := by exact @Thesis.RoutingExtended.empty_stream_value.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.empty_stream_value
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_5
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.empty_stream_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.empty_stream_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.empty_stream_value"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.empty_stream_value"
#print axioms GamesGlobalExpectedTypes.target_5

section
universe u
open Finset Thesis.RoutingExtended
theorem GamesGlobalExpectedTypes.target_6 : (∀ {A : Type u} [Fintype A] [DecidableEq A] (θ : ℝ) (m : A → ℝ) (outside : A)
    (hm : ∀ i, m i ≤ 0),
    gibbs θ m outside = pure outside) := by exact @Thesis.RoutingExtended.empty_stream_absorbs.{u}
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingExtended.empty_stream_absorbs
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_6
  unless target.levelParams.length == 1 && expected.levelParams.length == 1 do
    throwError "Universe arity mismatch: Thesis.RoutingExtended.empty_stream_absorbs"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingExtended.empty_stream_absorbs | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingExtended do
    throwError "Defining module mismatch: Thesis.RoutingExtended.empty_stream_absorbs"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingExtended.empty_stream_absorbs"
#print axioms GamesGlobalExpectedTypes.target_6

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
theorem GamesGlobalExpectedTypes.target_7 : (∀ (θ : ℝ) (hθ : 0 < θ) (t : Tree) (plus minus : Strategy t),
    auxiliary θ t plus (canonical θ t) ≤ value θ t ∧
      value θ t ≤ auxiliary θ t (canonical θ t) minus) := by exact @Thesis.RoutingProfiles.auxiliary_saddle
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.auxiliary_saddle
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_7
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.auxiliary_saddle"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.auxiliary_saddle | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.auxiliary_saddle"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.auxiliary_saddle"
#print axioms GamesGlobalExpectedTypes.target_7

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
theorem GamesGlobalExpectedTypes.target_8 : (∀ (θ : ℝ) (t : Tree) (plus minus : Strategy t),
    reported θ t plus minus =
      (Thesis.RoutingGate.logCoordinate (auxiliary θ t plus minus),
       Thesis.RoutingGate.logCoordinate (-auxiliary θ t plus minus))) := by exact @Thesis.RoutingProfiles.reported_coordinates
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.reported_coordinates
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_8
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.reported_coordinates"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.reported_coordinates | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.reported_coordinates"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.reported_coordinates"
#print axioms GamesGlobalExpectedTypes.target_8

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
theorem GamesGlobalExpectedTypes.target_9 : (∀ (θ : ℝ) (t : Tree) (plus minus : Strategy t),
    auxiliary θ t plus minus =
      expZero (reported θ t plus minus).1 - expZero (reported θ t plus minus).2) := by exact @Thesis.RoutingProfiles.auxiliary_eq_reported_difference
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.auxiliary_eq_reported_difference
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_9
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.auxiliary_eq_reported_difference"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.auxiliary_eq_reported_difference | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.auxiliary_eq_reported_difference"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.auxiliary_eq_reported_difference"
#print axioms GamesGlobalExpectedTypes.target_9

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
theorem GamesGlobalExpectedTypes.target_10 : (∀ (θ : ℝ) (hθ : 0 < θ) (t : Tree),
    IsNash θ t (canonical θ t)) := by exact @Thesis.RoutingProfiles.canonical_nash
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.canonical_nash
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_10
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.canonical_nash"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.canonical_nash | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.canonical_nash"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.canonical_nash"
#print axioms GamesGlobalExpectedTypes.target_10

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
theorem GamesGlobalExpectedTypes.target_11 : (∀ (θ : ℝ) (hθ : 0 < θ) (t : Tree),
    IsSubgamePerfect θ t (canonical θ t)) := by exact @Thesis.RoutingProfiles.canonical_subgame_perfect
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.canonical_subgame_perfect
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_11
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.canonical_subgame_perfect"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.canonical_subgame_perfect | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.canonical_subgame_perfect"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.canonical_subgame_perfect"
#print axioms GamesGlobalExpectedTypes.target_11

section
open Thesis.RoutingExtended Thesis.RoutingProfiles
theorem GamesGlobalExpectedTypes.target_12 : (∀ (θ : ℝ) (q : Bool) (p n : Tree)
    (h : signed q (value θ p + value θ n) ≤ 0),
    (canonical θ (.activation q p n)).1 = false) := by exact @Thesis.RoutingProfiles.canonical_stops_log_ties
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingProfiles.canonical_stops_log_ties
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_12
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingProfiles.canonical_stops_log_ties"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingProfiles.canonical_stops_log_ties | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingProfiles do
    throwError "Defining module mismatch: Thesis.RoutingProfiles.canonical_stops_log_ties"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingProfiles.canonical_stops_log_ties"
#print axioms GamesGlobalExpectedTypes.target_12

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
theorem GamesGlobalExpectedTypes.target_13 : (∀ {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (ha : ∀ i, 0 ≤ a i)
    (hv : ∀ i, value 1 (child i) = signed q (a i)),
    actionMass q (extend ε b w)
      (fun i => value 1 (extend (.terminal (signed q 1)) (.terminal (signed q 1)) child i)) =
      extend ε b (fun i => w i * a i)) := by exact @Thesis.RoutingNetwork.route_action_masses
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.route_action_masses
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_13
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.route_action_masses"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.route_action_masses | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.route_action_masses"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.route_action_masses"
#print axioms GamesGlobalExpectedTypes.target_13

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
theorem GamesGlobalExpectedTypes.target_14 : (∀ {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, value 1 (child i) = signed q (a i)),
    value 1 (route q ε b w child hε hb hw) = signed q (ε + (b + ∑ i, w i * a i))) := by exact @Thesis.RoutingNetwork.route_anchor_value
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.route_anchor_value
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_14
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.route_anchor_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.route_anchor_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.route_anchor_value"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.route_anchor_value"
#print axioms GamesGlobalExpectedTypes.target_14

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
theorem GamesGlobalExpectedTypes.target_15 : (∀ {n} (q : Bool) (ε b : ℝ) (w a : Fin n → ℝ)
    (child : Fin n → Tree) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, value 1 (child i) = signed q (a i)) (i : Fin n),
    (canonical 1 (route q ε b w child hε hb hw)).1.prob i.succ.succ =
      w i * a i / (ε + (b + ∑ j, w j * a j))) := by exact @Thesis.RoutingNetwork.route_anchor_ordinary_probability
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.route_anchor_ordinary_probability
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_15
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.route_anchor_ordinary_probability"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.route_anchor_ordinary_probability | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.route_anchor_ordinary_probability"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.route_anchor_ordinary_probability"
#print axioms GamesGlobalExpectedTypes.target_15

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
theorem GamesGlobalExpectedTypes.target_16 : (∀ {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool),
    value 1 (networkGame net ε hε x j q) = signed q (net.eval x j)) := by exact @Thesis.RoutingNetwork.networkGame_value
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.networkGame_value
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_16
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.networkGame_value"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.networkGame_value | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.networkGame_value"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.networkGame_value"
#print axioms GamesGlobalExpectedTypes.target_16

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
theorem GamesGlobalExpectedTypes.target_17 : (∀ {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin m) (q : Bool),
    IsSubgamePerfect θ (networkGame net ε hε x j q) (canonical θ (networkGame net ε hε x j q))) := by exact @Thesis.RoutingNetwork.networkGame_subgame_perfect
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.networkGame_subgame_perfect
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_17
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.networkGame_subgame_perfect"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.networkGame_subgame_perfect | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.networkGame_subgame_perfect"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.networkGame_subgame_perfect"
#print axioms GamesGlobalExpectedTypes.target_17

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
theorem GamesGlobalExpectedTypes.target_18 : (∀ {n m} (net : Network n m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool),
    reported 1 (networkGame net ε hε x j q)
      (canonical 1 (networkGame net ε hε x j q)) (canonical 1 (networkGame net ε hε x j q)) =
      (Thesis.RoutingGate.logCoordinate (signed q (net.eval x j)),
       Thesis.RoutingGate.logCoordinate (-signed q (net.eval x j)))) := by exact @Thesis.RoutingNetwork.networkGame_reported
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.networkGame_reported
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_18
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.networkGame_reported"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.networkGame_reported | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.networkGame_reported"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.networkGame_reported"
#print axioms GamesGlobalExpectedTypes.target_18

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
theorem GamesGlobalExpectedTypes.target_19 : (∀ {n k m} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (tail : Network k m) (ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (q : Bool),
    reported 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q)
      (canonical 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q))
      (canonical 1 (networkGame (.layer wp wn bp bn tail) ε hε x j q)) =
      if q then (Thesis.RoutingGate.logCoordinate ((Network.layer wp wn bp bn tail).eval x j), ⊥)
      else (⊥, Thesis.RoutingGate.logCoordinate ((Network.layer wp wn bp bn tail).eval x j))) := by exact @Thesis.RoutingNetwork.networkLayer_reported
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.networkLayer_reported
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_19
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.networkLayer_reported"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.networkLayer_reported | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.networkLayer_reported"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.networkLayer_reported"
#print axioms GamesGlobalExpectedTypes.target_19

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
theorem GamesGlobalExpectedTypes.target_20 : (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool),
    (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)).1 =
      decide (0 < preactivation wp wn bp bn x j)) := by exact @Thesis.RoutingNetwork.inputLayerGames_selected_gate
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.inputLayerGames_selected_gate
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_20
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.inputLayerGames_selected_gate"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.inputLayerGames_selected_gate | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.inputLayerGames_selected_gate"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.inputLayerGames_selected_gate"
#print axioms GamesGlobalExpectedTypes.target_20

section
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
theorem GamesGlobalExpectedTypes.target_21 : (∀ {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree) (x : Vec n)
    (hx : ∀ i, 0 ≤ x i) (hv : ∀ i q, value 1 (input i q) = signed q (x i))
    (j : Fin k) (q : Bool),
    (canonical 1 (layerGames wp wn bp bn ε hε input j q)).1 =
      decide (0 < preactivation wp wn bp bn x j)) := by exact @Thesis.RoutingNetwork.layerGames_selected_gate
end
run_cmd do
  let target ← getConstInfo `Thesis.RoutingNetwork.layerGames_selected_gate
  let expected ← getConstInfo `GamesGlobalExpectedTypes.target_21
  unless target.levelParams.length == 0 && expected.levelParams.length == 0 do
    throwError "Universe arity mismatch: Thesis.RoutingNetwork.layerGames_selected_gate"
  let env ← getEnv
  let some index := env.getModuleIdxFor? `Thesis.RoutingNetwork.layerGames_selected_gate | throwError "Target was not imported"
  unless env.header.moduleNames[index.toNat]! == `Thesis.RoutingNetwork do
    throwError "Defining module mismatch: Thesis.RoutingNetwork.layerGames_selected_gate"
  liftTermElabM do
    let levels := expected.levelParams.map Level.param
    let targetType := target.type.instantiateLevelParams target.levelParams levels
    unless ← Meta.isDefEq targetType expected.type do
      throwError "Exact type mismatch: Thesis.RoutingNetwork.layerGames_selected_gate"
#print axioms GamesGlobalExpectedTypes.target_21

