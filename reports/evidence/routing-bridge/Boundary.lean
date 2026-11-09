import Thesis.RoutingPolicyPaths

noncomputable section
set_option autoImplicit false
namespace RoutingBridgeBoundary
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork
open Thesis.RoutingBackward Thesis.RoutingPolicyBridge
open scoped BigOperators

def negativeWeight : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 2
def negativeInput : Vec 1 := fun _ => -3

/-- A negative raw input times a negative weight belongs to the positive fused
stream; the empty negative stream still carries its fair-oracle cemetery mass. -/
example : inputStep 0 negativeWeight 0 0 0 (by norm_num) negativeInput 0 true
    (some (false,(0 : Fin 1).succ.succ)) = 1/2 := by
  rw [inputStep_ordinary, Thesis.RoutingTransitions.transition_ordinary]
  norm_num [negativeWeight, negativeInput, preactivation, posContribution,
    negContribution, posDenominator, negDenominator, Matrix.mulVec, dotProduct]

example :
    collapsed (canonical 1 (inputLayerGames 0 negativeWeight 0 0 0 (by norm_num)
      negativeInput 0 true)).1
      (inputPositive 0 negativeWeight 0 0 0 (by norm_num) negativeInput 0 true)
      (inputNegative 0 negativeWeight 0 0 0 (by norm_num) negativeInput 0 true) true none = 1/2 := by
  rw [input_collapsed_transition]
  norm_num [Thesis.RoutingTransitions.transition, Thesis.RoutingTransitions.ordinary,
    Thesis.RoutingGate.chosenLogAction_eq_positive, negativeWeight, negativeInput,
    preactivation, posContribution, negContribution, posDenominator, negDenominator,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Zero preactivation selects stopping even with a strictly positive stabilizer. -/
example : inputStep (fun (_ _ : Fin 1) => (1 : ℝ)) 0 0 0 1 (by norm_num)
    0 0 true none = 1 := by
  unfold inputStep
  erw [inputLayerGames_selected_gate]
  norm_num [stepProbability, preactivation, Matrix.mulVec, dotProduct]

/-- A positive-bias zero-input node is active but all complete mass is absorbed;
there is no ordinary predecessor available to carry relevance. -/
example :
    collapsed (canonical 1 (inputLayerGames
      (0 : Matrix (Fin 1) (Fin 0) ℝ) 0 (fun _ => 2) 0 0 (by norm_num) 0 0 true)).1
      (inputPositive (0 : Matrix (Fin 1) (Fin 0) ℝ) 0 (fun _ => 2) 0 0 (by norm_num) 0 0 true)
      (inputNegative (0 : Matrix (Fin 1) (Fin 0) ℝ) 0 (fun _ => 2) 0 0 (by norm_num) 0 0 true)
      true none = 1 := by
  rw [input_collapsed_transition]
  simp [Thesis.RoutingTransitions.transition, Thesis.RoutingTransitions.ordinary,
    Thesis.RoutingGate.chosenLogAction_eq_positive, preactivation, Matrix.mulVec, dotProduct]

/-- Bias/stabilizer leakage remains in the denominators at an active gate. -/
example : inputStep (fun (_ _ : Fin 1) => (2 : ℝ)) 0 (fun _ => 1) 0 1 (by norm_num)
    (fun _ => 1) 0 false (some (false,(0 : Fin 1).succ.succ)) = 1/4 := by
  erw [inputStep_ordinary, Thesis.RoutingTransitions.transition_ordinary]
  norm_num [preactivation, posContribution, negContribution, posDenominator, negDenominator,
    Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.zero_apply]
  erw [sub_zero]
  norm_num

end RoutingBridgeBoundary
