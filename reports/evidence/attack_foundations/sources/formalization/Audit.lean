import HiddenMonotonicity
import Thesis

#print axioms HiddenMonotonicity.matrix_backward_sum
#print axioms HiddenMonotonicity.matrix_backward_difference
#print axioms HiddenMonotonicity.matrix_shift_difference
#print axioms HiddenMonotonicity.matrix_two_head_reconstruction
#print axioms HiddenMonotonicity.affine_closed_form
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
#print axioms HiddenMonotonicity.common_shift_derivative
#print axioms HiddenMonotonicity.vector_lift_chain_rule
#print axioms HiddenMonotonicity.monotone_directional_nonnegative
#print axioms HiddenMonotonicity.canonical_weight_split
#print axioms HiddenMonotonicity.shiftCoefficient_product
#print axioms HiddenMonotonicity.shifted_source_coefficient
#print axioms HiddenMonotonicity.input_dependent_shift_counterexample
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

-- Verify that all mapped Lean identifiers exist.
#check HiddenMonotonicity.Network.convex
#check HiddenMonotonicity.Network.correct
#check HiddenMonotonicity.Network.hasFDerivAt_split
#check HiddenMonotonicity.Network.monotone
#check HiddenMonotonicity.Network.shift
#check HiddenMonotonicity.actual_negative_pullback
#check HiddenMonotonicity.actual_positive_pullback
#check HiddenMonotonicity.affine_closed_form
#check HiddenMonotonicity.affine_finite_sum
#check HiddenMonotonicity.canonical_weight_split
#check HiddenMonotonicity.common_shift_derivative
#check HiddenMonotonicity.layer_derivative
#check HiddenMonotonicity.layer_difference
#check HiddenMonotonicity.lift_differential
#check HiddenMonotonicity.matrix_backward_difference
#check HiddenMonotonicity.matrix_backward_sum
#check HiddenMonotonicity.matrix_two_head_reconstruction
#check HiddenMonotonicity.maxpool_correct
#check HiddenMonotonicity.mixing_correct
#check HiddenMonotonicity.monotone_directional_nonnegative
#check HiddenMonotonicity.pre_difference
#check HiddenMonotonicity.shiftCoefficient_product
#check HiddenMonotonicity.shift_sum
#check HiddenMonotonicity.shifted_formula_counterexample
#check HiddenMonotonicity.shifted_gradient_g_finite_sum
#check HiddenMonotonicity.shifted_gradient_h_finite_sum
#check HiddenMonotonicity.shifted_heads_reconstruct
#check HiddenMonotonicity.shifted_source_coefficient
#check HiddenMonotonicity.vector_lift_chain_rule
#check Thesis.Games.discount_path_recovery
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
#check Thesis.Games.path_integral_eq_DP
#check Thesis.Games.path_law_normalized
#check Thesis.Games.pixelDisagreement_formula
#check Thesis.Games.pixelDisagreement_nonneg
#check Thesis.Games.pixelDisagreement_total
#check Thesis.Games.routing_recovery
#check Thesis.Games.survival_overlap
#check Thesis.Games.trajectory_overlap_eq_DP
#check Thesis.Regularization.entropy_gate_unique
#check Thesis.Regularization.finite_gibbs_bound
#check Thesis.Regularization.finite_gibbs_value
#check Thesis.Regularization.hasDerivAt_gate
#check Thesis.Regularization.hasDerivAt_softplus
#check Thesis.Regularization.routing_variational
#check Thesis.Regularization.softSplit_recovery
#check Thesis.Regularization.softplus_variational
