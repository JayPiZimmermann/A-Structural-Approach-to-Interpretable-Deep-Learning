import Thesis.RoutingReadoutHistory

noncomputable section
set_option autoImplicit false
open HiddenMonotonicity Thesis.RoutingReadoutHistory Thesis.RoutingBackward
open Thesis.AffineOutputBackward Thesis.BackwardGames
open scoped BigOperators
namespace ReadoutHistoryBoundary

def backbone : Network 1 1 := .output 1
def negativeWeight : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => -1
def unitInput : Vec 1 := fun _ => 1

theorem output_nonnegative : ∀ j, 0≤backbone.eval unitInput j := by
  intro j
  norm_num [backbone, Network.eval, unitInput]

-- The final affine value is negative; introducing a final activation would
-- incorrectly erase the reversed-ownership occupation checked below.
example : affineOutput backbone negativeWeight 0 unitInput 0 = -1 := by
  norm_num [affineOutput, backbone, Network.eval, unitInput, negativeWeight,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

example : readoutHistoryOccupation backbone negativeWeight 0 1 1 0 (by norm_num)
    unitInput 0 true 0 false = 1 := by
  rw [readoutHistoryOccupation_eq_readoutOccupation _ _ _ _ _ _ _ _ output_nonnegative]
  norm_num [readoutOccupation, readoutPos, readoutNeg, posContribution, negContribution,
    posDenominator, negDenominator, backbone, Network.eval, unitInput, negativeWeight,
    rgOccupation, rgProbability, rgDiscount, routingTrace, Paths, pathsFintype,
    Fin.sum_univ_succ]
  change (∑ _ : Unit, (1 : ℝ)*1) = 1
  simp

-- Stabilizer leakage is preserved, rather than renormalizing surviving paths.
example : readoutHistoryOccupation backbone negativeWeight 0 1 1 1 (by norm_num)
    unitInput 0 true 0 false = 1/2 := by
  rw [readoutHistoryOccupation_eq_readoutOccupation _ _ _ _ _ _ _ _ output_nonnegative]
  norm_num [readoutOccupation, readoutPos, readoutNeg, posContribution, negContribution,
    posDenominator, negDenominator, backbone, Network.eval, unitInput, negativeWeight,
    rgOccupation, rgProbability, rgDiscount, routingTrace, Paths, pathsFintype,
    Fin.sum_univ_succ]
  change (∑ _ : Unit, (1 : ℝ)*1) = 1
  simp

-- Both streams are empty at epsilon zero. All complete-history mass is still
-- present, while ordinary-neuron discounted occupation is zero.
example : readoutHistoryOccupation backbone (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 1 1 0 (by norm_num)
    unitInput 0 true 0 true = 0 := by
  rw [readoutHistoryOccupation_eq_readoutOccupation _ _ _ _ _ _ _ _ output_nonnegative]
  norm_num [readoutOccupation, readoutPos, readoutNeg, posContribution, negContribution,
    posDenominator, negDenominator, backbone, Network.eval, unitInput,
    rgOccupation, rgProbability, rgDiscount, routingTrace, Paths, pathsFintype,
    Fin.sum_univ_succ]

example : (∑ h : ForcedHistories
      (positiveReadout backbone (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (by norm_num) unitInput 0 true)
      (negativeReadout backbone (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (by norm_num) unitInput 0 true),
    forcedProbability 1 _ _ h) = 1 := forcedProbability_normalized 1 _ _

def signedBackbone : Network 1 1 :=
  .layer 0 (fun _ _ => 1) 0 0 (.output 1)
def negativeInput : Vec 1 := fun _ => -1

theorem signed_backbone_nonnegative : ∀ j,0≤signedBackbone.eval negativeInput j := by
  intro j
  norm_num [signedBackbone, Network.eval, negativeInput, relu,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem signed_fused_occupation :
    rgOccupation signedBackbone 1 1 0 negativeInput 0 0 false = 1 := by
  rw [(rg_occupation_kernels signedBackbone 1 1 0 negativeInput 0 0).1]
  norm_num [signedBackbone, routingTrace, occupations, gated, posContribution,
    negContribution, posDenominator, negDenominator, preactivation, negativeInput,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_succ]
  change (0 : ℝ)-1<0
  norm_num

-- Signed raw input is fused with the first signed weight before stream splitting.
example : readoutHistoryOccupation signedBackbone negativeWeight 0 1 1 0 (by norm_num)
    negativeInput 0 true 0 false = 1 := by
  rw [readoutHistoryOccupation_eq_readoutOccupation _ _ _ _ _ _ _ _ signed_backbone_nonnegative]
  norm_num [readoutOccupation, readoutPos, readoutNeg, posContribution, negContribution,
    posDenominator, negDenominator, signedBackbone, Network.eval, negativeInput,
    negativeWeight, relu, Matrix.mulVec, dotProduct, Matrix.sub_apply, Fin.sum_univ_succ]
  change (max (-((0 : ℝ)-1)) 0 / max (-((0 : ℝ)-1)) 0) *
    rgOccupation signedBackbone 1 1 0 negativeInput 0 0 false = 1
  norm_num [signed_fused_occupation]

end ReadoutHistoryBoundary
