import HiddenMonotonicity.BackwardStatements
import HiddenMonotonicity.FinitePolynomialWitness
import HiddenMonotonicity.BlockedPaths

open HiddenMonotonicity
#check @Network.plain_head_gradient_formulas
#check @Network.stabilized_backward_absolute_Q_closed_form
#check @Network.backward_partial_invariants
#check @Network.affine_readout_closed_form
#check @Network.affine_logit_derivative
#check @Network.sensitivity_complementarity_absolute
#check @Network.symmetric_head_derivative
#check @Network.hasFDerivAt_originalTrace
#check @Network.gradient_blindness
#check @Circuit.cnn_split_correct
#check @Circuit.cnn_stream_properties
#check @Circuit.maxout_multiplication_split_correct
#check @Circuit.ordinary_polynomial_stream_witnesses
#check @maxpool_correct
#check @winner_pool_correct
#check @pre_difference
#check @layer_difference
#print axioms Network.plain_head_gradient_formulas
#print axioms Network.stabilized_backward_absolute_Q_closed_form
#print axioms Network.affine_readout_closed_form
#print axioms Circuit.cnn_split_correct
#print axioms Circuit.maxout_multiplication_split_correct

namespace AttackHidden
noncomputable def zeroNet : Network 1 1 := .layer 0 0 0 0 (.output 1)
theorem zeroNet_canonical : zeroNet.Canonical := by simp [zeroNet, Network.Canonical]
theorem zeroNet_never_strict (x : Vec 1) : ¬zeroNet.Strict x := by
  simp [zeroNet, Network.Strict, affineLayer, matrixCLM]
theorem zeroNet_eval_zero (x : Vec 1) : zeroNet.eval x = 0 := by
  simp [zeroNet, Network.eval, relu]
  rfl
theorem zeroNet_split_zero (x : PairVec 1) : zeroNet.split x.1 x.2 = (0,0) := by
  simp [zeroNet, Network.split]
  all_goals rfl
theorem zeroNet_split_differentiable (x : PairVec 1) :
    HasFDerivAt (fun y : PairVec 1 => zeroNet.split y.1 y.2) (0 : PairVec 1 →L[ℝ] PairVec 1) x := by
  have he : (fun y : PairVec 1 => zeroNet.split y.1 y.2) = fun _ => (0,0) := by
    funext y
    simp [zeroNet, Network.split]
    all_goals rfl
  rw [he]
  exact hasFDerivAt_const (0,0) x
theorem shifted_bulk_half : (shiftPair (1/4 : ℝ) (((ContinuousLinearMap.proj (0 : Fin 1) : Row 1)),0)).1 +
    (shiftPair (1/4 : ℝ) (((ContinuousLinearMap.proj (0 : Fin 1) : Row 1)),0)).2 =
    (1/2 : ℝ) • ((ContinuousLinearMap.proj (0 : Fin 1) : Row 1)) := by
  rw [shiftPair_sum]
  norm_num
theorem intermediate_bulk_half : backPos (3/4) (-1/4) 1 1 0 + backNeg (3/4) (-1/4) 1 1 0 = (1/2 : ℝ) := by
  norm_num [backPos, backNeg]
theorem intermediate_bulk_not_one : backPos (3/4) (-1/4) 1 1 0 + backNeg (3/4) (-1/4) 1 1 0 ≠ (1 : ℝ) := by
  norm_num [backPos, backNeg]
theorem activated_affine_targets_differ : max (0 : ℝ) 1 - 1 = 0 ∧ (0 : ℝ) - 1 = -1 := by norm_num
theorem zero_gate_inactive : originalGate (fun _ _ : Fin 1 => (1 : ℝ)) 0 0 0 (0 : Vec 1) 0 = false := by
  simp [originalGate, affineLayer, matrixCLM]
theorem source_zero_gate_active : (0 : ℝ) ≥ 0 := le_rfl
theorem eta_zero_source_parts_not_canonical :
    ¬((2 : ℝ) = max (2-1) 0 ∧ (1 : ℝ) = max (-(2-1)) 0) := by norm_num
noncomputable def etaZeroNegative (x : ℝ) : ℝ := min (max x 0+1) (max (-x) 0)
theorem eta_zero_negative_midpoint_violation :
    etaZeroNegative ((-2+0)/2) > (etaZeroNegative (-2)+etaZeroNegative 0)/2 := by
  norm_num [etaZeroNegative]
#print axioms zeroNet_split_differentiable
#print axioms intermediate_bulk_not_one
#print axioms eta_zero_negative_midpoint_violation
end AttackHidden
