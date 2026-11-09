import HiddenMonotonicity
import Thesis

#print axioms HiddenMonotonicity.MaskedTrace.run_bulk
#print axioms HiddenMonotonicity.MaskedTrace.run_unified
#print axioms HiddenMonotonicity.MaskedTrace.run_zero_actual
#print axioms HiddenMonotonicity.MaskedTrace.run_stabilized
#print axioms HiddenMonotonicity.Network.affine_readout_closed_form
#print axioms HiddenMonotonicity.Network.affine_logit_derivative
#print axioms HiddenMonotonicity.matrix_backward_sum
#print axioms HiddenMonotonicity.matrix_backward_difference
#print axioms HiddenMonotonicity.matrix_shift_difference
#print axioms HiddenMonotonicity.matrix_two_head_reconstruction
#print axioms HiddenMonotonicity.affine_closed_form
#print axioms HiddenMonotonicity.Network.plain_backward_absolute_Q_closed_form
#print axioms HiddenMonotonicity.Network.backward_partial_invariants
#print axioms HiddenMonotonicity.Network.plain_head_gradient_formulas
#print axioms HiddenMonotonicity.max_derivative_left
#print axioms HiddenMonotonicity.max_derivative_right
#print axioms HiddenMonotonicity.maxpool_correct
#print axioms HiddenMonotonicity.residual_correct
#print axioms HiddenMonotonicity.weighted_sum_correct
#print axioms HiddenMonotonicity.multiplicative_split_correct
#print axioms HiddenMonotonicity.common_offset_correct
#print axioms HiddenMonotonicity.mixing_correct
#print axioms HiddenMonotonicity.winner_pool_correct
#print axioms HiddenMonotonicity.shift_mask_invariant
#print axioms HiddenMonotonicity.intervalProduct_self
#print axioms HiddenMonotonicity.transported_product
#print axioms HiddenMonotonicity.sources_sum
#print axioms HiddenMonotonicity.affine_finite_sum
#print axioms HiddenMonotonicity.shifted_source_sum
#print axioms HiddenMonotonicity.shifted_gradient_g_finite_sum
#print axioms HiddenMonotonicity.shifted_gradient_h_finite_sum
#print axioms HiddenMonotonicity.shifted_heads_reconstruct
#print axioms HiddenMonotonicity.positive_matrix_monotone
#print axioms HiddenMonotonicity.Network.monotone
#print axioms HiddenMonotonicity.affine_layer_mix
#print axioms HiddenMonotonicity.max_jensen
#print axioms HiddenMonotonicity.Network.convex
#print axioms HiddenMonotonicity.max_sub
#print axioms HiddenMonotonicity.pre_difference
#print axioms HiddenMonotonicity.split_correct
#print axioms HiddenMonotonicity.max_common_shift
#print axioms HiddenMonotonicity.pre_common_shift
#print axioms HiddenMonotonicity.lift_chain_rule
#print axioms HiddenMonotonicity.lift_differential
#print axioms HiddenMonotonicity.relu_derivative_positive
#print axioms HiddenMonotonicity.relu_derivative_negative
#print axioms HiddenMonotonicity.backward_invariant
#print axioms HiddenMonotonicity.paper_backward_invariant_counterexample
#print axioms HiddenMonotonicity.backward_sum
#print axioms HiddenMonotonicity.backward_difference
#print axioms HiddenMonotonicity.shift_difference
#print axioms HiddenMonotonicity.shift_sum
#print axioms HiddenMonotonicity.shifted_backward_difference
#print axioms HiddenMonotonicity.shifted_formula_counterexample
#print axioms HiddenMonotonicity.two_head_reconstruction
#print axioms HiddenMonotonicity.multiplicative_convexity_counterexample
#print axioms HiddenMonotonicity.connected_flat_head_derivatives
#print axioms HiddenMonotonicity.nonzero_mass_zero_balanced
#print axioms HiddenMonotonicity.Network.valid_decomposition_recovery
#print axioms HiddenMonotonicity.Network.forwardWith_relu
#print axioms HiddenMonotonicity.mixPair_valid
#print axioms HiddenMonotonicity.Network.mixing_recovery
#print axioms HiddenMonotonicity.Network.mixing_one_is_split
#print axioms HiddenMonotonicity.Network.decomposition_nonnegative
#print axioms HiddenMonotonicity.mixPair_nonnegative
#print axioms HiddenMonotonicity.MaskedTrace.activeMap_apply
#print axioms HiddenMonotonicity.MaskedTrace.inactiveMap_apply
#print axioms HiddenMonotonicity.MaskedTrace.difference_splitLayer
#print axioms HiddenMonotonicity.MaskedTrace.difference_splitJac
#print axioms HiddenMonotonicity.layerJac_trace
#print axioms HiddenMonotonicity.Network.jacobian_trace
#print axioms HiddenMonotonicity.Network.hasFDerivAt_eval_trace
#print axioms HiddenMonotonicity.layer_difference
#print axioms HiddenMonotonicity.Network.correct
#print axioms HiddenMonotonicity.shifted_layer_preactivation
#print axioms HiddenMonotonicity.Network.shift
#print axioms HiddenMonotonicity.preP_apply
#print axioms HiddenMonotonicity.layer_derivative
#print axioms HiddenMonotonicity.Network.hasFDerivAt_split
#print axioms HiddenMonotonicity.layerJac_positive_input
#print axioms HiddenMonotonicity.layerJac_negative_input
#print axioms HiddenMonotonicity.actual_positive_pullback
#print axioms HiddenMonotonicity.actual_negative_pullback
#print axioms HiddenMonotonicity.Network.hasFDerivAt_eval
#print axioms HiddenMonotonicity.preactivation_difference
#print axioms HiddenMonotonicity.layerFun_difference
#print axioms HiddenMonotonicity.Network.trace_originalTrace
#print axioms HiddenMonotonicity.Network.regular_iff_strict
#print axioms HiddenMonotonicity.Network.trace_absCLM
#print axioms HiddenMonotonicity.Network.originalTrace_absCLM
#print axioms HiddenMonotonicity.Network.hasFDerivAt_originalTrace
#print axioms HiddenMonotonicity.affineLayer_hasFDerivAt
#print axioms HiddenMonotonicity.reluLayer_hasFDerivAt
#print axioms HiddenMonotonicity.minLayer_hasFDerivAt
#print axioms HiddenMonotonicity.Network.absCLM_eq_absoluteMap
#print axioms HiddenMonotonicity.Network.sensitivity_complementarity_absolute
#print axioms HiddenMonotonicity.Network.qSources_have_derivatives
#print axioms HiddenMonotonicity.QSource.row_pull
#print axioms HiddenMonotonicity.sourceRows_pull
#print axioms HiddenMonotonicity.Network.qSources_sum
#print axioms HiddenMonotonicity.Network.stabilized_backward_Q_closed_form
#print axioms HiddenMonotonicity.Network.stabilized_backward_invariant
#print axioms HiddenMonotonicity.Network.plain_backward_Q_closed_form
#print axioms HiddenMonotonicity.Network.qSources_eq_absolute
#print axioms HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form
#print axioms HiddenMonotonicity.assemble_balancedLift
#print axioms HiddenMonotonicity.balancedLift_difference
#print axioms HiddenMonotonicity.Network.symmetric_head_derivative
#print axioms HiddenMonotonicity.reluLayer_continuous
#print axioms HiddenMonotonicity.Network.eventually_strict_trace
#print axioms HiddenMonotonicity.Network.locally_constant_jacobian
#print axioms HiddenMonotonicity.Network.regional_gradient_blindness
#print axioms HiddenMonotonicity.common_shift_derivative
#print axioms HiddenMonotonicity.vector_lift_chain_rule
#print axioms HiddenMonotonicity.monotone_directional_nonnegative
#print axioms HiddenMonotonicity.canonical_weight_split
#print axioms HiddenMonotonicity.shiftCoefficient_product
#print axioms HiddenMonotonicity.shifted_source_coefficient
#print axioms HiddenMonotonicity.input_dependent_shift_counterexample
#print axioms HiddenMonotonicity.assemble_partialPair
#print axioms HiddenMonotonicity.shiftPair_sum
#print axioms HiddenMonotonicity.unified_shift
#print axioms HiddenMonotonicity.MaskedTrace.splitLayer_common
#print axioms HiddenMonotonicity.MaskedTrace.splitLayer_signed
#print axioms HiddenMonotonicity.MaskedTrace.pull_sum
#print axioms HiddenMonotonicity.MaskedTrace.pull_unified
#print axioms HiddenMonotonicity.MaskedTrace.stabilized_bulk
#print axioms HiddenMonotonicity.MaskedTrace.stabilized_unified
#print axioms HiddenMonotonicity.MaskedTrace.stabilized_backward_closed_form_g
#print axioms HiddenMonotonicity.MaskedTrace.stabilized_backward_closed_form_h
#print axioms HiddenMonotonicity.MaskedTrace.stabilized_backward_invariant
#print axioms HiddenMonotonicity.MaskedTrace.zero_shift_actual
#print axioms HiddenMonotonicity.Network.local_sensitivities_correct
#print axioms HiddenMonotonicity.MaskedTrace.bulkCoefficient_zero
#print axioms HiddenMonotonicity.Network.sensitivity_complementarity
#print axioms HiddenMonotonicity.row_sum_comp
#print axioms HiddenMonotonicity.MaskedTrace.correction_terms_sum
#print axioms HiddenMonotonicity.Network.stabilized_backward_closed_form
#print axioms HiddenMonotonicity.MaskedTrace.bulkCoefficient_product
#print axioms HiddenMonotonicity.MaskedTrace.bulkCoefficient_half
#print axioms HiddenMonotonicity.MaskedTrace.correction_half
#print axioms HiddenMonotonicity.Network.half_shift_gradients
#print axioms HiddenMonotonicity.MaskedTrace.stabilized_partial_invariants
#print axioms Thesis.AffineOutputBackward.originalJac_sg_coordinate
#print axioms Thesis.AffineOutputBackward.affineOutput_hasFDerivAt
#print axioms Thesis.AffineOutputBackward.thesis_affine_output_gradient
#print axioms Thesis.AffineOutputBackward.thesis_affine_output_lrp
#print axioms Thesis.AffineOutputBackward.readoutOccupation_nonneg
#print axioms Thesis.AttentionBackward.conditionedAttention_affine
#print axioms Thesis.AttentionBackward.conditionedAttention_hasFDerivAt
#print axioms Thesis.AttentionBackward.normalized_attention_bias
#print axioms Thesis.AttentionBackward.effective_contribution_factor
#print axioms Thesis.AttentionBackward.attentionLRP_matrix
#print axioms Thesis.AttentionBackward.attention_raw_recovery
#print axioms Thesis.AttentionBackward.attention_path_discount_recovery
#print axioms Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery
#print axioms Thesis.AttentionBackward.attentionProbability_nonneg
#print axioms Thesis.AttentionBackward.attentionDiscount_nonneg
#print axioms Thesis.AttentionBackward.attentionOccupation_nonneg
#print axioms Thesis.BackwardGames.gated_sub
#print axioms Thesis.BackwardGames.occupation_difference
#print axioms Thesis.BackwardGames.signedMap_matrix
#print axioms Thesis.BackwardGames.originalJac_occupation
#print axioms Thesis.BackwardGames.raw_path_integral
#print axioms Thesis.BackwardGames.sg_path_discount_recovery
#print axioms Thesis.BackwardGames.sg_occupation_kernels
#print axioms Thesis.BackwardGames.stopping_game_gradient
#print axioms Thesis.BackwardGames.sgProbability_nonneg
#print axioms Thesis.BackwardGames.sgDiscount_pos
#print axioms Thesis.BackwardGames.sgOccupation_nonneg
#print axioms Thesis.BackwardGames.sgTransition_normalized
#print axioms Thesis.BackwardGames.sgTransition_nonneg
#print axioms Thesis.BackwardGames.thesis_gradient_representation
#print axioms Thesis.BackwardGames.originalJac_coordinate_paths
#print axioms Thesis.BackwardGames.originalJac_no_path
#print axioms Thesis.Foundations.evalWith_relu
#print axioms Thesis.Foundations.affine_mix
#print axioms Thesis.Foundations.monotone_network
#print axioms Thesis.Foundations.activation_jensen
#print axioms Thesis.Foundations.jensen_comp
#print axioms Thesis.Foundations.positive_network_jensen
#print axioms Thesis.Foundations.icnn_jensen
#print axioms Thesis.Foundations.jensen_iff_convexOn
#print axioms Thesis.Foundations.icnn_convex
#print axioms Thesis.Foundations.icnn_affine_output
#print axioms Thesis.Foundations.monotone_affine_output
#print axioms Thesis.Foundations.relu_monotone
#print axioms Thesis.Foundations.relu_convex
#print axioms Thesis.Games.transport_mass
#print axioms Thesis.Games.transport_probability
#print axioms Thesis.Games.transport_nonneg
#print axioms Thesis.Games.sqrt_overlap_le
#print axioms Thesis.Games.overlap_nonneg
#print axioms Thesis.Games.overlap_le_one
#print axioms Thesis.Games.geometric_kernel_substochastic
#print axioms Thesis.Games.overlap_mass_decreases
#print axioms Thesis.Games.overlap_chain_rule
#print axioms Thesis.Games.overlap_path_factorization
#print axioms Thesis.Games.discounted_edge_recovery
#print axioms Thesis.Games.signed_discounted_edge_recovery
#print axioms Thesis.Games.routing_recovery
#print axioms Thesis.Games.survival_overlap
#print axioms Thesis.Games.hellinger_identity
#print axioms Thesis.Games.path_integral_eq_DP
#print axioms Thesis.Games.path_law_normalized
#print axioms Thesis.Games.path_geometric_mean
#print axioms Thesis.Games.trajectory_overlap_eq_DP
#print axioms Thesis.Games.discount_path_recovery
#print axioms Thesis.Games.pathDisagreement_nonneg
#print axioms Thesis.Games.pixelDisagreement_nonneg
#print axioms Thesis.Games.pixelDisagreement_formula
#print axioms Thesis.Games.pixelDisagreement_total
#print axioms Thesis.Games.overlap_sq_le_masses
#print axioms Thesis.Games.overlap_self
#print axioms Thesis.Games.overlap_eq_one_iff
#print axioms Thesis.Games.overlap_eq_zero_iff
#print axioms Thesis.Games.doob_kernel_normalized
#print axioms Thesis.Games.doob_kernel_nonneg
#print axioms Thesis.Games.doob_path_telescoping
#print axioms Thesis.Games.doob_survival_path
#print axioms Thesis.LayeredGames.best_attained
#print axioms Thesis.LayeredGames.selector_value
#print axioms Thesis.LayeredGames.le_best_max
#print axioms Thesis.LayeredGames.best_min_le
#print axioms Thesis.LayeredGames.Game.action_mono
#print axioms Thesis.LayeredGames.average_le
#print axioms Thesis.LayeredGames.le_average
#print axioms Thesis.LayeredGames.pure_average
#print axioms Thesis.LayeredGames.Game.optimal_lower
#print axioms Thesis.LayeredGames.Game.optimal_upper
#print axioms Thesis.LayeredGames.Game.saddle
#print axioms Thesis.LayeredGames.Game.bellman_unique
#print axioms Thesis.ReLUNetGame.kernel_nonnegative
#print axioms Thesis.ReLUNetGame.kernel_normalized
#print axioms Thesis.ReLUNetGame.continuation_recovery
#print axioms Thesis.ReLUNetGame.signed_layer
#print axioms Thesis.ReLUNetGame.signedValue_eq_network
#print axioms Thesis.ReLUNetGame.affine_output_value
#print axioms Thesis.ReLUNetGame.common_stopping_rule
#print axioms Thesis.ReLUNetGame.maximizing_action_characterization
#print axioms Thesis.Regularization.gate_pos
#print axioms Thesis.Regularization.gate_lt_one
#print axioms Thesis.Regularization.sigmoid_exp_ratio
#print axioms Thesis.Regularization.hasDerivAt_softplus
#print axioms Thesis.Regularization.deriv_softplus
#print axioms Thesis.Regularization.hasDerivAt_gate
#print axioms Thesis.Regularization.gate_derivative_pos
#print axioms Thesis.Regularization.binary_gibbs_bound
#print axioms Thesis.Regularization.binary_gibbs_value
#print axioms Thesis.Regularization.binary_gibbs_strict
#print axioms Thesis.Regularization.entropy_policy_le_softplus
#print axioms Thesis.Regularization.entropy_gate_value
#print axioms Thesis.Regularization.softplus_variational
#print axioms Thesis.Regularization.entropy_gate_unique
#print axioms Thesis.Regularization.hasDerivAt_deriv_softplus
#print axioms Thesis.Regularization.softplus_relu_bounds
#print axioms Thesis.Regularization.softSplit_recovery
#print axioms Thesis.Regularization.softSplit_nonneg
#print axioms Thesis.Regularization.softSplit_common_shift
#print axioms Thesis.Regularization.entropy_cell_bound
#print axioms Thesis.Regularization.partition_pos
#print axioms Thesis.Regularization.normalized_pos
#print axioms Thesis.Regularization.normalized_sum
#print axioms Thesis.Regularization.finite_gibbs_bound
#print axioms Thesis.Regularization.finite_gibbs_value
#print axioms Thesis.Regularization.routing_variational_bound
#print axioms Thesis.Regularization.routing_gibbs_value
#print axioms Thesis.Regularization.routing_variational
#print axioms Thesis.RoutingBackward.signed_routing_layer
#print axioms Thesis.RoutingBackward.full_lrp_matrix
#print axioms Thesis.RoutingBackward.rg_path_discount_recovery
#print axioms Thesis.RoutingBackward.rg_occupation_kernels
#print axioms Thesis.RoutingBackward.thesis_alpha_beta_recovery
#print axioms Thesis.RoutingBackward.posDenominator_pos
#print axioms Thesis.RoutingBackward.negDenominator_pos
#print axioms Thesis.RoutingBackward.rgProbability_nonneg
#print axioms Thesis.RoutingBackward.rgDiscount_nonneg
#print axioms Thesis.RoutingBackward.rgOccupation_nonneg
#print axioms Thesis.SoftplusBackward.softLayer_hasFDerivAt
#print axioms Thesis.SoftplusBackward.softTrace_layer_map
#print axioms Thesis.SoftplusBackward.softEval_hasFDerivAt
#print axioms Thesis.SoftplusBackward.soft_path_discount_recovery
#print axioms Thesis.SoftplusBackward.soft_occupation_kernels
#print axioms Thesis.SoftplusBackward.softProbability_nonneg
#print axioms Thesis.SoftplusBackward.softDiscount_pos
#print axioms Thesis.SoftplusBackward.softOccupation_nonneg
#print axioms Thesis.SoftplusBackward.thesis_softplus_gradient
#print axioms Thesis.SoftplusDecomposition.softEval_eq_forwardWith
#print axioms Thesis.SoftplusDecomposition.thesis_softplus_forward

-- Verify that all mapped Lean identifiers exist.
#check HiddenMonotonicity.MaskedTrace.bulkCoefficient_product
#check HiddenMonotonicity.MaskedTrace.difference_splitJac
#check HiddenMonotonicity.MaskedTrace.stabilized
#check HiddenMonotonicity.MaskedTrace.stabilized_bulk
#check HiddenMonotonicity.Network.affine_readout_closed_form
#check HiddenMonotonicity.Network.backward_partial_invariants
#check HiddenMonotonicity.Network.convex
#check HiddenMonotonicity.Network.correct
#check HiddenMonotonicity.Network.decomposition_nonnegative
#check HiddenMonotonicity.Network.local_sensitivities_correct
#check HiddenMonotonicity.Network.locally_constant_jacobian
#check HiddenMonotonicity.Network.mixing_one_is_split
#check HiddenMonotonicity.Network.mixing_recovery
#check HiddenMonotonicity.Network.monotone
#check HiddenMonotonicity.Network.plain_backward_absolute_Q_closed_form
#check HiddenMonotonicity.Network.plain_head_gradient_formulas
#check HiddenMonotonicity.Network.qSources_have_derivatives
#check HiddenMonotonicity.Network.regional_gradient_blindness
#check HiddenMonotonicity.Network.sensitivity_complementarity_absolute
#check HiddenMonotonicity.Network.shift
#check HiddenMonotonicity.Network.stabilized_backward_absolute_Q_closed_form
#check HiddenMonotonicity.Network.stabilized_backward_invariant
#check HiddenMonotonicity.Network.symmetric_head_derivative
#check HiddenMonotonicity.Network.valid_decomposition_recovery
#check HiddenMonotonicity.actual_negative_pullback
#check HiddenMonotonicity.actual_positive_pullback
#check HiddenMonotonicity.canonical_weight_split
#check HiddenMonotonicity.layer_derivative
#check HiddenMonotonicity.layer_difference
#check HiddenMonotonicity.matrix_backward_difference
#check HiddenMonotonicity.matrix_backward_sum
#check HiddenMonotonicity.maxpool_correct
#check HiddenMonotonicity.mixPair_nonnegative
#check HiddenMonotonicity.mixing_correct
#check HiddenMonotonicity.monotone_directional_nonnegative
#check HiddenMonotonicity.pre_difference
#check Thesis.AffineOutputBackward.thesis_affine_output_gradient
#check Thesis.AffineOutputBackward.thesis_affine_output_lrp
#check Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery
#check Thesis.BackwardGames.sgTransition_normalized
#check Thesis.BackwardGames.stopping_game_gradient
#check Thesis.BackwardGames.thesis_gradient_representation
#check Thesis.Foundations.icnn_affine_output
#check Thesis.Foundations.icnn_convex
#check Thesis.Foundations.monotone_affine_output
#check Thesis.Foundations.monotone_network
#check Thesis.Games.doob_kernel_nonneg
#check Thesis.Games.doob_kernel_normalized
#check Thesis.Games.doob_path_telescoping
#check Thesis.Games.doob_survival_path
#check Thesis.Games.geometric_kernel_substochastic
#check Thesis.Games.overlap_eq_one_iff
#check Thesis.Games.overlap_eq_zero_iff
#check Thesis.Games.overlap_mass_decreases
#check Thesis.Games.overlap_sq_le_masses
#check Thesis.Games.pathLaw
#check Thesis.Games.path_geometric_mean
#check Thesis.Games.path_law_normalized
#check Thesis.Games.pixelDisagreement_formula
#check Thesis.Games.pixelDisagreement_nonneg
#check Thesis.Games.pixelDisagreement_total
#check Thesis.Games.survival_overlap
#check Thesis.Games.trajectory_overlap_eq_DP
#check Thesis.LayeredGames.Game.bellman_unique
#check Thesis.LayeredGames.Game.optimal_lower
#check Thesis.LayeredGames.Game.optimal_upper
#check Thesis.LayeredGames.Game.saddle
#check Thesis.ReLUNetGame.affine_output_value
#check Thesis.ReLUNetGame.common_stopping_rule
#check Thesis.ReLUNetGame.signedValue_eq_network
#check Thesis.Regularization.entropy_gate_unique
#check Thesis.Regularization.finite_gibbs_bound
#check Thesis.Regularization.finite_gibbs_value
#check Thesis.Regularization.routing_variational
#check Thesis.Regularization.softSplit_recovery
#check Thesis.Regularization.softplus_variational
#check Thesis.RoutingBackward.thesis_alpha_beta_recovery
#check Thesis.SoftplusBackward.thesis_softplus_gradient
#check Thesis.SoftplusDecomposition.softEval_eq_forwardWith
#check Thesis.SoftplusDecomposition.thesis_softplus_forward
