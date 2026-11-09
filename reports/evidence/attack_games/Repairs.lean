import Thesis.StoppingBoundary
import Thesis.RoutingGate
import Thesis.SoftplusBoundary
import Thesis.RoutingSupport
import Thesis.RoutingTransitions
import Thesis.RoutingExpectation

set_option pp.universes true
#check @Thesis.StoppingBoundary.transition_normalized
#check @Thesis.StoppingBoundary.path_discount_recovery
#check @Thesis.StoppingBoundary.selected_operator_occupation
#check @Thesis.StoppingBoundary.strict_gradient_occupation
#print axioms Thesis.StoppingBoundary.fanIn_nonnegative
#print axioms Thesis.StoppingBoundary.zero_fanIn_weights
#print axioms Thesis.StoppingBoundary.transition_normalized
#print axioms Thesis.StoppingBoundary.transition_nonnegative
#print axioms Thesis.StoppingBoundary.transition_eq_original
#print axioms Thesis.StoppingBoundary.path_discount_recovery
#print axioms Thesis.StoppingBoundary.occupation_kernels
#print axioms Thesis.StoppingBoundary.probability_nonnegative
#print axioms Thesis.StoppingBoundary.discount_nonnegative
#print axioms Thesis.StoppingBoundary.occupation_nonnegative
#print axioms Thesis.StoppingBoundary.selected_operator_occupation
#print axioms Thesis.StoppingBoundary.strict_gradient_occupation
#check @Thesis.RoutingGate.chosenLogPolicy_optimal
#check @Thesis.RoutingGate.nonpositive_log_policies_tied
#check @Thesis.RoutingGate.chosenLogPolicy_stops_at_nonpositive
#check @Thesis.RoutingGate.positive_log_policy_strict
#print axioms Thesis.RoutingGate.chosenLogAction_eq_positive
#print axioms Thesis.RoutingGate.nonpositive_log_actions_tied
#print axioms Thesis.RoutingGate.chosenLogAction_stops_at_nonpositive
#print axioms Thesis.RoutingGate.positive_continue_strictly_better
#print axioms Thesis.RoutingGate.chosenLogAction_optimal
#print axioms Thesis.RoutingGate.chosenLogAction_mass
#print axioms Thesis.RoutingGate.gate_value
#print axioms Thesis.RoutingGate.signed_policy_bound
#print axioms Thesis.RoutingGate.signed_gate_optimal
#print axioms Thesis.RoutingGate.logCoordinate_monotone
#print axioms Thesis.RoutingGate.chosenLogPolicy_eq_gate
#print axioms Thesis.RoutingGate.chosenLogPolicy_optimal
#print axioms Thesis.RoutingGate.nonpositive_log_policies_tied
#print axioms Thesis.RoutingGate.chosenLogPolicy_stops_at_nonpositive
#print axioms Thesis.RoutingGate.positive_log_policy_strict
#print axioms Thesis.RoutingGate.signed_optimal_iff
#print axioms Thesis.RoutingGate.negative_signed_utility_strict
#print axioms Thesis.RoutingGate.logCoordinate_nonpositive
#print axioms Thesis.RoutingGate.logCoordinate_selected_value
#print axioms Thesis.RoutingGate.negative_log_tie_is_not_utility_tie
#print axioms Thesis.RoutingGate.frozenGate_hasDerivAt
#print axioms Thesis.RoutingGate.frozenGate_nonnegative
#print axioms Thesis.RoutingGate.frozenGate_reference_value
#print axioms Thesis.RoutingGate.varyingGate_hasDerivAt
#check @Thesis.SoftplusBoundary.transition_normalized
#check @Thesis.SoftplusBoundary.zero_fanIn_absorbs
#check @Thesis.SoftplusBoundary.gradient_occupation
#print axioms Thesis.SoftplusBoundary.transition_normalized
#print axioms Thesis.SoftplusBoundary.transition_nonnegative
#print axioms Thesis.SoftplusBoundary.transition_ordinary
#print axioms Thesis.SoftplusBoundary.zero_fanIn_absorbs
#print axioms Thesis.SoftplusBoundary.path_discount_recovery
#print axioms Thesis.SoftplusBoundary.occupation_kernels
#print axioms Thesis.SoftplusBoundary.probability_nonnegative
#print axioms Thesis.SoftplusBoundary.discount_nonnegative
#print axioms Thesis.SoftplusBoundary.occupation_nonnegative
#print axioms Thesis.SoftplusBoundary.gradient_occupation
#check @Thesis.RoutingSupport.sourceLRP_eq_lrp
#check @Thesis.RoutingSupport.source_alpha_beta_recovery
#check @Thesis.RoutingSupport.source_alpha_beta_output_seed
#print axioms Thesis.RoutingSupport.sourceLayer_zero_input
#print axioms Thesis.RoutingSupport.sourceLRP_zero_input
#print axioms Thesis.RoutingSupport.sourceLRP_eq_lrp
#print axioms Thesis.RoutingSupport.source_alpha_beta_recovery
#print axioms Thesis.RoutingSupport.source_alpha_beta_output_seed
#check @Thesis.RoutingTransitions.transition_nonnegative
#check @Thesis.RoutingTransitions.transition_normalized
#check @Thesis.RoutingTransitions.probability_nonnegative
#print axioms Thesis.RoutingTransitions.posDenominator_nonnegative
#print axioms Thesis.RoutingTransitions.negDenominator_nonnegative
#print axioms Thesis.RoutingTransitions.positive_stream_subprobability
#print axioms Thesis.RoutingTransitions.negative_stream_subprobability
#print axioms Thesis.RoutingTransitions.ordinary_nonnegative
#print axioms Thesis.RoutingTransitions.ordinary_sum
#print axioms Thesis.RoutingTransitions.ordinary_subprobability
#print axioms Thesis.RoutingTransitions.transition_normalized
#print axioms Thesis.RoutingTransitions.transition_nonnegative
#print axioms Thesis.RoutingTransitions.transition_ordinary
#print axioms Thesis.RoutingTransitions.probability_nonnegative
#print axioms Thesis.RoutingTransitions.occupation_nonnegative
#check @Thesis.RoutingExpectation.conditional_affinity_contraction
#check @Thesis.RoutingExpectation.conditional_affinity_full_depth
#print axioms Thesis.RoutingExpectation.conditional_affinity_contraction
#print axioms Thesis.RoutingExpectation.conditional_affinity_full_depth

#print axioms Thesis.StoppingBoundary.strict_stopping_decomposition_gradient
#print axioms Thesis.StoppingBoundary.strict_affine_output_gradient
#print axioms Thesis.RoutingSupport.sourceAffineOutputLRP_eq
#print axioms Thesis.RoutingSupport.source_affine_output_lrp

noncomputable section
namespace RepairChecks
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward
theorem selected_negative_log_tie :
    (Thesis.RoutingGate.chosenLogPolicy (-1)).val = 0 ∧
    Thesis.RoutingGate.logPolicy (-1) (Thesis.RoutingGate.gate 1) = ⊥ := by
  exact ⟨Thesis.RoutingGate.chosenLogPolicy_stops_at_nonpositive (-1) (by norm_num),
    Thesis.RoutingGate.nonpositive_log_policies_tied (-1) (by norm_num) _⟩
theorem zero_open_stopping_row :
    Thesis.StoppingBoundary.transition
      (fun (_ : Fin 1) (_ : Fin 1) => (0:ℝ)) (fun _ _ => 0)
      (fun _ => true) 0 false none = 1 := by
  simp [Thesis.StoppingBoundary.transition, fanIn]
theorem bias_and_empty_stream_row :
    Thesis.RoutingTransitions.transition
      (fun (_ : Fin 1) (_ : Fin 1) => (1:ℝ)) (fun _ _ => 0)
      (fun _ => 1) (fun _ => 0) 0 (fun _ => 1) 0 false (some (0,false)) = 1/4 ∧
    Thesis.RoutingTransitions.transition
      (fun (_ : Fin 1) (_ : Fin 1) => (1:ℝ)) (fun _ _ => 0)
      (fun _ => 1) (fun _ => 0) 0 (fun _ => 1) 0 false none = 3/4 := by
  norm_num [Thesis.RoutingTransitions.transition, Thesis.RoutingTransitions.ordinary,
    Thesis.RoutingGate.chosenLogAction_eq_positive, preactivation,
    posContribution, negContribution, posDenominator, negDenominator,
    Matrix.mulVec, Matrix.sub_apply, Matrix.zero_apply, dotProduct, Pi.sub_apply, Pi.add_apply,
    Fin.sum_univ_succ, Fintype.sum_prod_type, Fintype.sum_bool]
  change (0:ℝ) < (1-0+1)
  norm_num
end RepairChecks
#print axioms RepairChecks.selected_negative_log_tie
#print axioms RepairChecks.zero_open_stopping_row
#print axioms RepairChecks.bias_and_empty_stream_row
