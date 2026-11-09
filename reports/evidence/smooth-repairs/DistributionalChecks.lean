import HiddenMonotonicity.CurvatureMinimality
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Deriv.Support
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution
#check Homeomorph.subLeft
#check Homeomorph.subRight
#check ContDiff.deriv
#check ContDiff.deriv'
#check ContDiff.differentiable
#check HasCompactSupport.hasDerivAt_convolution_left
#check convolution_eq_swap
#check tendsto_one_div_add_atTop_nhds_zero_nat
#check tendsto_natCast_atTop_atTop
#check tendsto_inv_atTop_zero
#check Continuous.locallyIntegrable
#check LocallyIntegrable.intervalIntegrable
#check intervalIntegral.integral_eq_integral_of_support_subset
#check intervalIntegral.integral_eq_integral_of_support_subset_of_le
#check Continuous.continuousAt
#check contDiff_infty_iff_deriv
#check ContDiffBump
#check ContDiffBump.contDiff_normed
#check Filter.Tendsto.congr'
