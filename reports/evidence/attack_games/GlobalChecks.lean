import Thesis.RoutingNetwork

#print axioms Thesis.RoutingExtended.expZero_coe
#print axioms Thesis.RoutingExtended.expZero_bottom
#print axioms Thesis.RoutingExtended.expZero_sourceValue
#print axioms Thesis.RoutingExtended.routedMass_nonnegative
#print axioms Thesis.RoutingExtended.log_routedMass
#print axioms Thesis.RoutingExtended.expZero_logCoordinate
#print axioms Thesis.RoutingExtended.source_edge_score
#print axioms Thesis.RoutingExtended.routedMass_monotone
#print axioms Thesis.RoutingExtended.tilted_nonnegative
#print axioms Thesis.RoutingExtended.tilted_positive_iff
#print axioms Thesis.RoutingExtended.policy_positive_some
#print axioms Thesis.RoutingExtended.supported_partition_positive
#print axioms Thesis.RoutingExtended.entropy_bound_nonnegative
#print axioms Thesis.RoutingExtended.entropy_value_nonnegative
#print axioms Thesis.RoutingExtended.score_temperature_identity
#print axioms Thesis.RoutingExtended.gibbs_supported
#print axioms Thesis.RoutingExtended.gibbs_value_positive
#print axioms Thesis.RoutingExtended.gibbs_optimal
#print axioms Thesis.RoutingExtended.empty_stream_value
#print axioms Thesis.RoutingExtended.empty_stream_absorbs
#print axioms Thesis.RoutingExtended.sourceValue_gibbs_optimal
#print axioms Thesis.RoutingExtended.tilted_one
#print axioms Thesis.RoutingExtended.gibbs_anchor_mass
#print axioms Thesis.RoutingExtended.gibbs_anchor_probability
#print axioms Thesis.RoutingExtended.gibbs_anchor_nonoutside
#print axioms Thesis.RoutingProfiles.signed_involutive
#print axioms Thesis.RoutingProfiles.gateValue_plus
#print axioms Thesis.RoutingProfiles.gateValue_minus
#print axioms Thesis.RoutingProfiles.gate_action_monotone
#print axioms Thesis.RoutingProfiles.gate_action_bound
#print axioms Thesis.RoutingProfiles.actionMass_nonnegative
#print axioms Thesis.RoutingProfiles.routingOperator_monotone
#print axioms Thesis.RoutingProfiles.routing_choice_bound
#print axioms Thesis.RoutingProfiles.canonical_value
#print axioms Thesis.RoutingProfiles.auxiliary_saddle
#print axioms Thesis.RoutingProfiles.positive_parts_difference
#print axioms Thesis.RoutingProfiles.routed_coordinates
#print axioms Thesis.RoutingProfiles.reported_coordinates
#print axioms Thesis.RoutingProfiles.auxiliary_eq_reported_difference
#print axioms Thesis.RoutingProfiles.canonical_nash
#print axioms Thesis.RoutingProfiles.canonical_subgame_perfect
#print axioms Thesis.RoutingProfiles.canonical_stops_log_ties
#print axioms Thesis.RoutingNetwork.sum_extend
#print axioms Thesis.RoutingNetwork.extend_nonnegative
#print axioms Thesis.RoutingNetwork.route_action_masses
#print axioms Thesis.RoutingNetwork.route_anchor_value
#print axioms Thesis.RoutingNetwork.route_anchor_ordinary_probability
#print axioms Thesis.RoutingNetwork.signed_opponent
#print axioms Thesis.RoutingNetwork.signed_difference
#print axioms Thesis.RoutingNetwork.gateValue_signed
#print axioms Thesis.RoutingNetwork.activation_anchor_value
#print axioms Thesis.RoutingNetwork.denominator_difference
#print axioms Thesis.RoutingNetwork.inputLayerGames_value
#print axioms Thesis.RoutingNetwork.layerGames_value
#print axioms Thesis.RoutingNetwork.propagate_value
#print axioms Thesis.RoutingNetwork.networkGame_value
#print axioms Thesis.RoutingNetwork.networkGame_subgame_perfect
#print axioms Thesis.RoutingNetwork.networkGame_reported
#print axioms Thesis.RoutingNetwork.networkGame_nonnegative_reported
#print axioms Thesis.RoutingNetwork.eval_nonnegative
#print axioms Thesis.RoutingNetwork.networkLayer_reported
#print axioms Thesis.RoutingNetwork.inputLayerGames_continuation
#print axioms Thesis.RoutingNetwork.layerGames_continuation
#print axioms Thesis.RoutingNetwork.inputLayerGames_selected_gate
#print axioms Thesis.RoutingNetwork.layerGames_selected_gate

noncomputable section
namespace GlobalRoutingChecks
open Thesis.RoutingProfiles Thesis.RoutingExtended
def tieTree : Tree := .activation true (.terminal 2) (.terminal (-3))

theorem selected_negative_log_tie :
    Thesis.RoutingGate.chosenLogAction ((2:ℝ)-3) = false ∧
    Thesis.RoutingGate.logCoordinate ((2:ℝ)-3) = ⊥ ∧
    Thesis.RoutingGate.logCoordinate (-((2:ℝ)-3)) = (0 : WithBot ℝ) := by
  norm_num [
    Thesis.RoutingGate.chosenLogAction_eq_positive, Thesis.RoutingGate.logCoordinate]

theorem positive_probability_on_zero_mass :
    sourceValue 1 (fun b : Bool => if b then (0:ℝ) else 4) (pure true) = ⊥ := by
  norm_num [sourceValue, Supported, Thesis.RoutingExtended.pure]

theorem empty_stream_selects_absorption :
    gibbs 1 (fun _ : Bool => (0:ℝ)) false = pure false :=
  empty_stream_absorbs 1 _ false (fun _ => le_rfl)

theorem tieTree_source_spne : IsSubgamePerfect 1 tieTree (canonical 1 tieTree) :=
  canonical_subgame_perfect 1 (by norm_num) tieTree
end GlobalRoutingChecks
#print axioms GlobalRoutingChecks.selected_negative_log_tie
#print axioms GlobalRoutingChecks.positive_probability_on_zero_mass
#print axioms GlobalRoutingChecks.empty_stream_selects_absorption
#print axioms GlobalRoutingChecks.tieTree_source_spne
