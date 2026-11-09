import Thesis.Foundations
import Thesis.LayeredGames
import Thesis.ReLUNetGame
import Thesis.ReLUNetEquilibrium
import Thesis.Bellman
import Thesis.BellmanReturn
import Thesis.Tropical
import Thesis.TropicalNetwork
import Thesis.SupportGeometry
import Thesis.SupportDerivatives
import Thesis.CompactSupport
import Thesis.PiecewiseLinear
import Thesis.SourceGeometryStatements
import Thesis.SourceFoundationsStatements
import HiddenMonotonicity.CurvaturePrimitives
import HiddenMonotonicity.DCTilt
import HiddenMonotonicity.SmoothCurvatureSplit
import HiddenMonotonicity.CurvatureMinimality
import HiddenMonotonicity.ModernSigmoid
import HiddenMonotonicity.ModernSoftplus
set_option pp.universes true
set_option pp.explicit true
#check @Thesis.Foundations.evalWith_relu
#print axioms Thesis.Foundations.evalWith_relu
#check @Thesis.Foundations.affine_mix
#print axioms Thesis.Foundations.affine_mix
#check @Thesis.Foundations.monotone_network
#print axioms Thesis.Foundations.monotone_network
#check @Thesis.Foundations.activation_jensen
#print axioms Thesis.Foundations.activation_jensen
#check @Thesis.Foundations.jensen_comp
#print axioms Thesis.Foundations.jensen_comp
#check @Thesis.Foundations.positive_network_jensen
#print axioms Thesis.Foundations.positive_network_jensen
#check @Thesis.Foundations.icnn_jensen
#print axioms Thesis.Foundations.icnn_jensen
#check @Thesis.Foundations.jensen_iff_convexOn
#print axioms Thesis.Foundations.jensen_iff_convexOn
#check @Thesis.Foundations.icnn_convex
#print axioms Thesis.Foundations.icnn_convex
#check @Thesis.Foundations.icnn_affine_output
#print axioms Thesis.Foundations.icnn_affine_output
#check @Thesis.Foundations.monotone_affine_output
#print axioms Thesis.Foundations.monotone_affine_output
#check @Thesis.Foundations.relu_monotone
#print axioms Thesis.Foundations.relu_monotone
#check @Thesis.Foundations.relu_convex
#print axioms Thesis.Foundations.relu_convex
#check @Thesis.LayeredGames.best_attained
#print axioms Thesis.LayeredGames.best_attained
#check @Thesis.LayeredGames.selector_value
#print axioms Thesis.LayeredGames.selector_value
#check @Thesis.LayeredGames.le_best_max
#print axioms Thesis.LayeredGames.le_best_max
#check @Thesis.LayeredGames.best_min_le
#print axioms Thesis.LayeredGames.best_min_le
#check @Thesis.LayeredGames.Game.action_mono
#print axioms Thesis.LayeredGames.Game.action_mono
#check @Thesis.LayeredGames.average_le
#print axioms Thesis.LayeredGames.average_le
#check @Thesis.LayeredGames.le_average
#print axioms Thesis.LayeredGames.le_average
#check @Thesis.LayeredGames.pure_average
#print axioms Thesis.LayeredGames.pure_average
#check @Thesis.LayeredGames.Game.optimal_lower
#print axioms Thesis.LayeredGames.Game.optimal_lower
#check @Thesis.LayeredGames.Game.optimal_upper
#print axioms Thesis.LayeredGames.Game.optimal_upper
#check @Thesis.LayeredGames.Game.saddle
#print axioms Thesis.LayeredGames.Game.saddle
#check @Thesis.LayeredGames.Game.bellman_unique
#print axioms Thesis.LayeredGames.Game.bellman_unique
#check @Thesis.ReLUNetGame.kernel_nonnegative
#print axioms Thesis.ReLUNetGame.kernel_nonnegative
#check @Thesis.ReLUNetGame.kernel_normalized
#print axioms Thesis.ReLUNetGame.kernel_normalized
#check @Thesis.ReLUNetGame.continuation_recovery
#print axioms Thesis.ReLUNetGame.continuation_recovery
#check @Thesis.ReLUNetGame.signed_layer
#print axioms Thesis.ReLUNetGame.signed_layer
#check @Thesis.ReLUNetGame.signedValue_eq_network
#print axioms Thesis.ReLUNetGame.signedValue_eq_network
#check @Thesis.ReLUNetGame.affine_output_value
#print axioms Thesis.ReLUNetGame.affine_output_value
#check @Thesis.ReLUNetGame.common_stopping_rule
#print axioms Thesis.ReLUNetGame.common_stopping_rule
#check @Thesis.ReLUNetGame.maximizing_action_characterization
#print axioms Thesis.ReLUNetGame.maximizing_action_characterization
#check @Thesis.ReLUNetGame.gateProbability_pure
#print axioms Thesis.ReLUNetGame.gateProbability_pure
#check @Thesis.ReLUNetGame.gateProbability_value
#print axioms Thesis.ReLUNetGame.gateProbability_value
#check @Thesis.ReLUNetGame.randomized_stop_bounds
#print axioms Thesis.ReLUNetGame.randomized_stop_bounds
#check @Thesis.ReLUNetGame.continuation_mono
#print axioms Thesis.ReLUNetGame.continuation_mono
#check @Thesis.ReLUNetGame.continuation_signed
#print axioms Thesis.ReLUNetGame.continuation_signed
#check @Thesis.ReLUNetGame.optimal_lower_pair
#print axioms Thesis.ReLUNetGame.optimal_lower_pair
#check @Thesis.ReLUNetGame.optimal_upper_pair
#print axioms Thesis.ReLUNetGame.optimal_upper_pair
#check @Thesis.ReLUNetGame.relu_net_game_equilibrium
#print axioms Thesis.ReLUNetGame.relu_net_game_equilibrium
#check @Thesis.ReLUNetGame.relu_net_game_affine_equilibrium
#print axioms Thesis.ReLUNetGame.relu_net_game_affine_equilibrium
#check @Thesis.Bellman.MDP.action_bound
#print axioms Thesis.Bellman.MDP.action_bound
#check @Thesis.Bellman.max_difference_bound
#print axioms Thesis.Bellman.max_difference_bound
#check @Thesis.Bellman.MDP.bellman_contracting
#print axioms Thesis.Bellman.MDP.bellman_contracting
#check @Thesis.Bellman.MDP.policyBellman_contracting
#print axioms Thesis.Bellman.MDP.policyBellman_contracting
#check @Thesis.Bellman.MDP.optimal_fixed
#print axioms Thesis.Bellman.MDP.optimal_fixed
#check @Thesis.Bellman.MDP.policy_fixed
#print axioms Thesis.Bellman.MDP.policy_fixed
#check @Thesis.Bellman.MDP.optimal_unique
#print axioms Thesis.Bellman.MDP.optimal_unique
#check @Thesis.Bellman.MDP.policy_unique
#print axioms Thesis.Bellman.MDP.policy_unique
#check @Thesis.Bellman.MDP.action_mono
#print axioms Thesis.Bellman.MDP.action_mono
#check @Thesis.Bellman.MDP.policyBellman_mono
#print axioms Thesis.Bellman.MDP.policyBellman_mono
#check @Thesis.Bellman.MDP.policyBellman_le
#print axioms Thesis.Bellman.MDP.policyBellman_le
#check @Thesis.Bellman.MDP.action_shift
#print axioms Thesis.Bellman.MDP.action_shift
#check @Thesis.Bellman.MDP.policyBellman_shift
#print axioms Thesis.Bellman.MDP.policyBellman_shift
#check @Thesis.Bellman.MDP.policy_le_optimal
#print axioms Thesis.Bellman.MDP.policy_le_optimal
#check @Thesis.Bellman.MDP.greedy_value
#print axioms Thesis.Bellman.MDP.greedy_value
#check @Thesis.Bellman.MDP.policyBellman_pure
#print axioms Thesis.Bellman.MDP.policyBellman_pure
#check @Thesis.Bellman.MDP.greedy_policy_optimal
#print axioms Thesis.Bellman.MDP.greedy_policy_optimal
#check @Thesis.Bellman.MDP.bellman_optimality
#print axioms Thesis.Bellman.MDP.bellman_optimality
#check @Thesis.Bellman.MDP.policyTransition_nonnegative
#print axioms Thesis.Bellman.MDP.policyTransition_nonnegative
#check @Thesis.Bellman.MDP.policyTransition_normalized
#print axioms Thesis.Bellman.MDP.policyTransition_normalized
#check @Thesis.Bellman.MDP.policyBellman_affine
#print axioms Thesis.Bellman.MDP.policyBellman_affine
#check @Thesis.Bellman.MDP.discountedOperator_bound
#print axioms Thesis.Bellman.MDP.discountedOperator_bound
#check @Thesis.Bellman.MDP.iterated_reward_bound
#print axioms Thesis.Bellman.MDP.iterated_reward_bound
#check @Thesis.Bellman.MDP.reward_series_summable
#print axioms Thesis.Bellman.MDP.reward_series_summable
#check @Thesis.Bellman.MDP.truncated_return
#print axioms Thesis.Bellman.MDP.truncated_return
#check @Thesis.Bellman.MDP.discounted_iterate
#print axioms Thesis.Bellman.MDP.discounted_iterate
#check @Thesis.Bellman.MDP.expected_return_hasSum
#print axioms Thesis.Bellman.MDP.expected_return_hasSum
#check @Thesis.Bellman.MDP.expected_return_eq_value
#print axioms Thesis.Bellman.MDP.expected_return_eq_value
#check @Thesis.Tropical.finiteMax_attained
#print axioms Thesis.Tropical.finiteMax_attained
#check @Thesis.Tropical.le_finiteMax
#print axioms Thesis.Tropical.le_finiteMax
#check @Thesis.Tropical.finiteMax_le
#print axioms Thesis.Tropical.finiteMax_le
#check @Thesis.Tropical.Polynomial.eval_monomial
#print axioms Thesis.Tropical.Polynomial.eval_monomial
#check @Thesis.Tropical.Polynomial.eval_max
#print axioms Thesis.Tropical.Polynomial.eval_max
#check @Thesis.Tropical.Polynomial.eval_add
#print axioms Thesis.Tropical.Polynomial.eval_add
#check @Thesis.Tropical.Polynomial.eval_scale
#print axioms Thesis.Tropical.Polynomial.eval_scale
#check @Thesis.Tropical.Polynomial.newton_max
#print axioms Thesis.Tropical.Polynomial.newton_max
#check @Thesis.Tropical.Polynomial.newton_add
#print axioms Thesis.Tropical.Polynomial.newton_add
#check @Thesis.Tropical.support_convexHull
#print axioms Thesis.Tropical.support_convexHull
#check @Thesis.Tropical.Polynomial.eval_eq_support
#print axioms Thesis.Tropical.Polynomial.eval_eq_support
#check @Thesis.Tropical.Polynomial.lifted_support
#print axioms Thesis.Tropical.Polynomial.lifted_support
#check @Thesis.Tropical.Polynomial.convex
#print axioms Thesis.Tropical.Polynomial.convex
#check @Thesis.Tropical.Polynomial.monotone
#print axioms Thesis.Tropical.Polynomial.monotone
#check @Thesis.Tropical.Polynomial.newton_nonnegative
#print axioms Thesis.Tropical.Polynomial.newton_nonnegative
#check @Thesis.Tropical.Polynomial.eval_weightedSum
#print axioms Thesis.Tropical.Polynomial.eval_weightedSum
#check @Thesis.Tropical.Polynomial.weightedSum_nonnegative
#print axioms Thesis.Tropical.Polynomial.weightedSum_nonnegative
#check @Thesis.Tropical.Polynomial.weightedSum_zero
#print axioms Thesis.Tropical.Polynomial.weightedSum_zero
#check @Thesis.Tropical.Polynomial.add_nonnegative
#print axioms Thesis.Tropical.Polynomial.add_nonnegative
#check @Thesis.Tropical.Polynomial.max_nonnegative
#print axioms Thesis.Tropical.Polynomial.max_nonnegative
#check @Thesis.Tropical.Polynomial.add_zero
#print axioms Thesis.Tropical.Polynomial.add_zero
#check @Thesis.Tropical.Polynomial.max_zero
#print axioms Thesis.Tropical.Polynomial.max_zero
#check @Thesis.Tropical.Polynomial.homogeneous
#print axioms Thesis.Tropical.Polynomial.homogeneous
#check @Thesis.Tropical.polynomialAffine_eval
#print axioms Thesis.Tropical.polynomialAffine_eval
#check @Thesis.Tropical.polynomialAffine_nonnegative
#print axioms Thesis.Tropical.polynomialAffine_nonnegative
#check @Thesis.Tropical.polynomialAffine_zero
#print axioms Thesis.Tropical.polynomialAffine_zero
#check @Thesis.Tropical.tropicalSplit_eval
#print axioms Thesis.Tropical.tropicalSplit_eval
#check @Thesis.Tropical.tropicalSplit_nonnegative
#print axioms Thesis.Tropical.tropicalSplit_nonnegative
#check @Thesis.Tropical.tropicalSplit_zero
#print axioms Thesis.Tropical.tropicalSplit_zero
#check @Thesis.Tropical.coordinate_eval
#print axioms Thesis.Tropical.coordinate_eval
#check @Thesis.Tropical.coordinate_nonnegative
#print axioms Thesis.Tropical.coordinate_nonnegative
#check @Thesis.Tropical.network_tropical_representation
#print axioms Thesis.Tropical.network_tropical_representation
#check @Thesis.Tropical.biasfree_network_support_representation
#print axioms Thesis.Tropical.biasfree_network_support_representation
#check @Thesis.Tropical.affine_network_tropical_representation
#print axioms Thesis.Tropical.affine_network_tropical_representation
#check @Thesis.Tropical.linear_eq_dot
#print axioms Thesis.Tropical.linear_eq_dot
#check @Thesis.Tropical.dot_le_support_hull
#print axioms Thesis.Tropical.dot_le_support_hull
#check @Thesis.Tropical.mem_hull_iff_support
#print axioms Thesis.Tropical.mem_hull_iff_support
#check @Thesis.Tropical.hull_subset_iff_support
#print axioms Thesis.Tropical.hull_subset_iff_support
#check @Thesis.Tropical.hull_eq_of_support_eq
#print axioms Thesis.Tropical.hull_eq_of_support_eq
#check @Thesis.Tropical.support_hull_zero
#print axioms Thesis.Tropical.support_hull_zero
#check @Thesis.Tropical.support_hull_homogeneous
#print axioms Thesis.Tropical.support_hull_homogeneous
#check @Thesis.Tropical.subgradient_iff_maximizing_face
#print axioms Thesis.Tropical.subgradient_iff_maximizing_face
#check @Thesis.Tropical.gradientRow_apply
#print axioms Thesis.Tropical.gradientRow_apply
#check @Thesis.Tropical.gradientRow_injective
#print axioms Thesis.Tropical.gradientRow_injective
#check @Thesis.Tropical.maximizing_point_derivative
#print axioms Thesis.Tropical.maximizing_point_derivative
#check @Thesis.Tropical.unique_generator_hasFDerivAt
#print axioms Thesis.Tropical.unique_generator_hasFDerivAt
#check @Thesis.Tropical.unique_face_extreme
#print axioms Thesis.Tropical.unique_face_extreme
#check @Thesis.Tropical.extreme_exposing_direction
#print axioms Thesis.Tropical.extreme_exposing_direction
#check @Thesis.Tropical.vertices_eq_attainable_gradients
#print axioms Thesis.Tropical.vertices_eq_attainable_gradients
#check @Thesis.Tropical.support_differentiable_iff_singleton_face
#print axioms Thesis.Tropical.support_differentiable_iff_singleton_face
#check @Thesis.Tropical.support_greatest
#print axioms Thesis.Tropical.support_greatest
#check @Thesis.Tropical.support_attained
#print axioms Thesis.Tropical.support_attained
#check @Thesis.Tropical.dot_le_support
#print axioms Thesis.Tropical.dot_le_support
#check @Thesis.Tropical.support_convex
#print axioms Thesis.Tropical.support_convex
#check @Thesis.Tropical.support_homogeneous
#print axioms Thesis.Tropical.support_homogeneous
#check @Thesis.Tropical.support_convexHull_compact
#print axioms Thesis.Tropical.support_convexHull_compact
#check @Thesis.Tropical.support_minkowski
#print axioms Thesis.Tropical.support_minkowski
#check @Thesis.Tropical.support_union
#print axioms Thesis.Tropical.support_union
#check @Thesis.Tropical.support_hull_union
#print axioms Thesis.Tropical.support_hull_union
#check @Thesis.Tropical.mem_compact_iff_support
#print axioms Thesis.Tropical.mem_compact_iff_support
#check @Thesis.Tropical.compact_subset_iff_support
#print axioms Thesis.Tropical.compact_subset_iff_support
#check @Thesis.Tropical.compact_eq_of_support_eq
#print axioms Thesis.Tropical.compact_eq_of_support_eq
#check @Thesis.PiecewiseLinear.Polyhedron.closed
#print axioms Thesis.PiecewiseLinear.Polyhedron.closed
#check @Thesis.PiecewiseLinear.Polyhedron.convex
#print axioms Thesis.PiecewiseLinear.Polyhedron.convex
#check @Thesis.PiecewiseLinear.polynomial_continuous
#print axioms Thesis.PiecewiseLinear.polynomial_continuous
#check @Thesis.PiecewiseLinear.differenceCell_cover
#print axioms Thesis.PiecewiseLinear.differenceCell_cover
#check @Thesis.PiecewiseLinear.differenceCell_affine
#print axioms Thesis.PiecewiseLinear.differenceCell_affine
#check @Thesis.PiecewiseLinear.polynomial_difference_cpwl
#print axioms Thesis.PiecewiseLinear.polynomial_difference_cpwl
#check @Thesis.PiecewiseLinear.restrictInput_eval
#print axioms Thesis.PiecewiseLinear.restrictInput_eval
#check @Thesis.PiecewiseLinear.canonicalize_nonnegative
#print axioms Thesis.PiecewiseLinear.canonicalize_nonnegative
#check @Thesis.PiecewiseLinear.canonicalize_eval
#print axioms Thesis.PiecewiseLinear.canonicalize_eval
#check @Thesis.PiecewiseLinear.network_cpwl
#print axioms Thesis.PiecewiseLinear.network_cpwl
#check @Thesis.PiecewiseLinear.affine_network_cpwl
#print axioms Thesis.PiecewiseLinear.affine_network_cpwl
#check @Thesis.SourceGeometry.polytope_vertex_support
#print axioms Thesis.SourceGeometry.polytope_vertex_support
#check @Thesis.SourceGeometry.support_properties
#print axioms Thesis.SourceGeometry.support_properties
#check @Thesis.SourceGeometry.newton_calculus
#print axioms Thesis.SourceGeometry.newton_calculus
#check @Thesis.SourceGeometry.weightedSum_newton
#print axioms Thesis.SourceGeometry.weightedSum_newton
#check @Thesis.SourceGeometry.affine_newton
#print axioms Thesis.SourceGeometry.affine_newton
#check @Thesis.SourceGeometry.minkowski_propagation
#print axioms Thesis.SourceGeometry.minkowski_propagation
#check @Thesis.SourceGeometry.network_polytopes_nonnegative
#print axioms Thesis.SourceGeometry.network_polytopes_nonnegative
#check @Thesis.SourceGeometry.tropicalSplit_newton
#print axioms Thesis.SourceGeometry.tropicalSplit_newton
#check @Thesis.SourceGeometry.coordinate_newton
#print axioms Thesis.SourceGeometry.coordinate_newton
#check @Thesis.SourceGeometry.minkowski_propagation_network
#print axioms Thesis.SourceGeometry.minkowski_propagation_network
#check @Thesis.SourceFoundations.monotone_represents
#print axioms Thesis.SourceFoundations.monotone_represents
#check @Thesis.SourceFoundations.icnn_represents_convex
#print axioms Thesis.SourceFoundations.icnn_represents_convex
#check @Thesis.SourceFoundations.maxout_special_cases
#print axioms Thesis.SourceFoundations.maxout_special_cases
#check @Thesis.SourceFoundations.bellman_equations
#print axioms Thesis.SourceFoundations.bellman_equations
#check @Thesis.SourceFoundations.shapley_bellman
#print axioms Thesis.SourceFoundations.shapley_bellman
#check @Thesis.SourceFoundations.subdifferential_face
#print axioms Thesis.SourceFoundations.subdifferential_face
#check @Thesis.SourceFoundations.split_tropical_rational
#print axioms Thesis.SourceFoundations.split_tropical_rational
#check @HiddenMonotonicity.SmoothDC.cumulative_continuous
#print axioms HiddenMonotonicity.SmoothDC.cumulative_continuous
#check @HiddenMonotonicity.SmoothDC.slope_continuous
#print axioms HiddenMonotonicity.SmoothDC.slope_continuous
#check @HiddenMonotonicity.SmoothDC.primitive_hasDerivAt
#print axioms HiddenMonotonicity.SmoothDC.primitive_hasDerivAt
#check @HiddenMonotonicity.SmoothDC.cumulative_monotone
#print axioms HiddenMonotonicity.SmoothDC.cumulative_monotone
#check @HiddenMonotonicity.SmoothDC.primitive_convex
#print axioms HiddenMonotonicity.SmoothDC.primitive_convex
#check @HiddenMonotonicity.SmoothDC.cumulative_atBot
#print axioms HiddenMonotonicity.SmoothDC.cumulative_atBot
#check @HiddenMonotonicity.SmoothDC.derivative_cumulative_representation
#print axioms HiddenMonotonicity.SmoothDC.derivative_cumulative_representation
#check @HiddenMonotonicity.SmoothDC.derivative_limit_atBot
#print axioms HiddenMonotonicity.SmoothDC.derivative_limit_atBot
#check @HiddenMonotonicity.SmoothDC.cumulative_abs_bound
#print axioms HiddenMonotonicity.SmoothDC.cumulative_abs_bound
#check @HiddenMonotonicity.SmoothDC.slope_abs_bound
#print axioms HiddenMonotonicity.SmoothDC.slope_abs_bound
#check @HiddenMonotonicity.SmoothDC.tilt_derivative_first
#print axioms HiddenMonotonicity.SmoothDC.tilt_derivative_first
#check @HiddenMonotonicity.SmoothDC.tilt_derivative_second
#print axioms HiddenMonotonicity.SmoothDC.tilt_derivative_second
#check @HiddenMonotonicity.SmoothDC.tilt_convex
#print axioms HiddenMonotonicity.SmoothDC.tilt_convex
#check @HiddenMonotonicity.SmoothDC.tilt_monotone
#print axioms HiddenMonotonicity.SmoothDC.tilt_monotone
#check @HiddenMonotonicity.SmoothDC.tilt_monotone_iff
#print axioms HiddenMonotonicity.SmoothDC.tilt_monotone_iff
#check @HiddenMonotonicity.SmoothDC.minimum_common_tilt
#print axioms HiddenMonotonicity.SmoothDC.minimum_common_tilt
#check @HiddenMonotonicity.SmoothDC.positiveCurvature_integrable
#print axioms HiddenMonotonicity.SmoothDC.positiveCurvature_integrable
#check @HiddenMonotonicity.SmoothDC.negativeCurvature_integrable
#print axioms HiddenMonotonicity.SmoothDC.negativeCurvature_integrable
#check @HiddenMonotonicity.SmoothDC.cumulative_curvature_split
#print axioms HiddenMonotonicity.SmoothDC.cumulative_curvature_split
#check @HiddenMonotonicity.SmoothDC.D1_sub_D2
#print axioms HiddenMonotonicity.SmoothDC.D1_sub_D2
#check @HiddenMonotonicity.SmoothDC.C1_hasDerivAt
#print axioms HiddenMonotonicity.SmoothDC.C1_hasDerivAt
#check @HiddenMonotonicity.SmoothDC.C2_hasDerivAt
#print axioms HiddenMonotonicity.SmoothDC.C2_hasDerivAt
#check @HiddenMonotonicity.SmoothDC.primitive_difference
#print axioms HiddenMonotonicity.SmoothDC.primitive_difference
#check @HiddenMonotonicity.SmoothDC.D1_abs_bounded
#print axioms HiddenMonotonicity.SmoothDC.D1_abs_bounded
#check @HiddenMonotonicity.SmoothDC.D2_abs_bounded
#print axioms HiddenMonotonicity.SmoothDC.D2_abs_bounded
#check @HiddenMonotonicity.SmoothDC.commonTilt_bounds
#print axioms HiddenMonotonicity.SmoothDC.commonTilt_bounds
#check @HiddenMonotonicity.SmoothDC.smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.smooth_dc_split
#check @HiddenMonotonicity.SmoothDC.canonical_tilt_minimality
#print axioms HiddenMonotonicity.SmoothDC.canonical_tilt_minimality
#check @HiddenMonotonicity.SmoothDC.convex_derivative_monotone
#print axioms HiddenMonotonicity.SmoothDC.convex_derivative_monotone
#check @HiddenMonotonicity.SmoothDC.curvature_minimality_ae
#print axioms HiddenMonotonicity.SmoothDC.curvature_minimality_ae
#check @HiddenMonotonicity.SmoothDC.slope_locally_AC
#print axioms HiddenMonotonicity.SmoothDC.slope_locally_AC
#check @HiddenMonotonicity.SmoothDC.primitive_second_derivatives_ae
#print axioms HiddenMonotonicity.SmoothDC.primitive_second_derivatives_ae
#check @HiddenMonotonicity.SmoothDC.affine_of_ae_second_derivative_zero
#print axioms HiddenMonotonicity.SmoothDC.affine_of_ae_second_derivative_zero
#check @HiddenMonotonicity.SmoothDC.integrable_nonnegative_derivative
#print axioms HiddenMonotonicity.SmoothDC.integrable_nonnegative_derivative
#check @HiddenMonotonicity.SmoothDC.sigmoidFirst_nonnegative
#print axioms HiddenMonotonicity.SmoothDC.sigmoidFirst_nonnegative
#check @HiddenMonotonicity.SmoothDC.sigmoidFirst_derivative
#print axioms HiddenMonotonicity.SmoothDC.sigmoidFirst_derivative
#check @HiddenMonotonicity.SmoothDC.sigmoidFirst_integrable
#print axioms HiddenMonotonicity.SmoothDC.sigmoidFirst_integrable
#check @HiddenMonotonicity.SmoothDC.sigmoidSecond_bound
#print axioms HiddenMonotonicity.SmoothDC.sigmoidSecond_bound
#check @HiddenMonotonicity.SmoothDC.sigmoidSecond_integrable
#print axioms HiddenMonotonicity.SmoothDC.sigmoidSecond_integrable
#check @HiddenMonotonicity.SmoothDC.sigmoid_curvature
#print axioms HiddenMonotonicity.SmoothDC.sigmoid_curvature
#check @HiddenMonotonicity.SmoothDC.sigmoid_derivative_locally_AC
#print axioms HiddenMonotonicity.SmoothDC.sigmoid_derivative_locally_AC
#check @HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.sigmoid_smooth_dc_split
#check @HiddenMonotonicity.SmoothDC.softplus_curvature
#print axioms HiddenMonotonicity.SmoothDC.softplus_curvature
#check @HiddenMonotonicity.SmoothDC.softplus_curvature_integrable
#print axioms HiddenMonotonicity.SmoothDC.softplus_curvature_integrable
#check @HiddenMonotonicity.SmoothDC.softplus_derivative_locally_AC
#print axioms HiddenMonotonicity.SmoothDC.softplus_derivative_locally_AC
#check @HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split
#print axioms HiddenMonotonicity.SmoothDC.softplus_smooth_dc_split
