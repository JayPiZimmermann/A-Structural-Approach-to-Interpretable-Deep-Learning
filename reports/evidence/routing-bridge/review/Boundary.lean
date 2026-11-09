import Thesis.RoutingHistorySteps
import Thesis.RoutingReadoutHistory

noncomputable section
set_option autoImplicit false
namespace IndependentRoutingHistoryBoundary
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork
open Thesis.RoutingHistory Thesis.RoutingHistorySteps Thesis.RoutingPolicyBridge
open Thesis.RoutingBackward Thesis.BackwardGames Thesis.RoutingObservations
open Thesis.RoutingReadoutHistory Thesis.AffineOutputBackward
open scoped BigOperators

def oneWeight : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
def positiveInput : Vec 1 := fun _ => 2
def backbone : Network 1 1 := .layer oneWeight 0 0 0 (.output 1)

theorem backbone_value : backbone.eval positiveInput = positiveInput := by
  funext j
  norm_num [backbone, Network.eval, oneWeight, positiveInput, relu,
    Matrix.mulVec, dotProduct]

theorem backbone_positive : ∀ j, 0 ≤ backbone.eval positiveInput j := by
  rw [backbone_value]
  intro j
  norm_num [positiveInput]

/-- The full probability law remains normalized even though only one quarter
of the forced-readout/backbone histories reaches an ordinary input. -/
example : (∑ h : ForcedHistories
      (positiveReadout backbone (fun (_ _ : Fin 1) => (-3 : ℝ)) (fun (_ : Fin 1) => (1 : ℝ)) 0 (by norm_num) positiveInput 0 true)
      (negativeReadout backbone (fun (_ _ : Fin 1) => (-3 : ℝ)) (fun (_ : Fin 1) => (1 : ℝ)) 0 (by norm_num) positiveInput 0 true),
    forcedProbability 1
      (positiveReadout backbone (fun (_ _ : Fin 1) => (-3 : ℝ)) (fun (_ : Fin 1) => (1 : ℝ)) 0 (by norm_num) positiveInput 0 true)
      (negativeReadout backbone (fun (_ _ : Fin 1) => (-3 : ℝ)) (fun (_ : Fin 1) => (1 : ℝ)) 0 (by norm_num) positiveInput 0 true) h) = 1 :=
  forcedProbability_normalized _ _ _

/-- The output logit is negative: an accidental ReLU output gate would erase
the occupation that the following example must retain. -/
example : affineOutput backbone (fun (_ _ : Fin 1) => (-3 : ℝ)) (fun (_ : Fin 1) => (1 : ℝ)) positiveInput 0 = -5 := by
  norm_num [affineOutput, backbone_value, positiveInput, Matrix.mulVec, dotProduct]

theorem backbone_positive_occupation :
    rgOccupation backbone 2 1 0 positiveInput 0 0 false = 2 := by
  rw [(rg_occupation_kernels backbone 2 1 0 positiveInput 0 0).1]
  norm_num [backbone, routingTrace, occupations, gated, preactivation,
    posContribution, negContribution, posDenominator, negDenominator,
    oneWeight, positiveInput, Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem backbone_negative_occupation :
    rgOccupation backbone 2 1 0 positiveInput 0 0 true = 0 := by
  rw [(rg_occupation_kernels backbone 2 1 0 positiveInput 0 0).2]
  norm_num [backbone, routingTrace, occupations, gated, preactivation,
    posContribution, negContribution, posDenominator, negDenominator,
    oneWeight, positiveInput, Matrix.mulVec, dotProduct, Matrix.mul_apply]

/-- Source alpha=2, beta=1 gives nonzero negative-owner occupation despite
the negative logit, with full stopped/bias histories retained in the law. -/
example : readoutHistoryOccupation backbone (fun (_ _ : Fin 1) => (-3 : ℝ)) (fun (_ : Fin 1) => (1 : ℝ))
    2 1 0 (by norm_num) positiveInput 0 true 0 false = 2 := by
  erw [readoutHistoryOccupation_eq_readoutOccupation _ _ _ _ _ _ _ _ backbone_positive]
  norm_num [readoutOccupation, readoutPos, readoutNeg, backbone_value,
    backbone_positive_occupation, backbone_negative_occupation,
    positiveInput, posContribution, negContribution, posDenominator, negDenominator]

/-- A genuine intermediate mark integrates the complete lower backbone away.
The identity suffix visits its root with discount one. -/
example : intermediateOccupation (.output 1) 2 1 0 (by norm_num)
    (networkGame backbone 0 (by norm_num) positiveInput) 0 true 0 true = 1 := by
  unfold intermediateOccupation
  change integral 2 1 _ _ _ (rootObservation _ (if (0 : Fin 1) = 0 ∧ true = true then 1 else 0)) = 1
  rw [integral_root]
  simp

/-- The actual full-history first-target marginal keeps the half-probability
empty negative stream in the cemetery at epsilon zero. -/
example : (∑ h : Histories (inputLayerGames oneWeight 0 0 0 0 (by norm_num) positiveInput 0 true),
    if stepTarget true (inputProjection oneWeight 0 0 0 0 (by norm_num) positiveInput 0 true h) = none then
      probability (inputLayerGames oneWeight 0 0 0 0 (by norm_num) positiveInput 0 true)
        (canonical 1 (inputLayerGames oneWeight 0 0 0 0 (by norm_num) positiveInput 0 true))
        (canonical 1 (inputLayerGames oneWeight 0 0 0 0 (by norm_num) positiveInput 0 true)) h else 0) = 1/2 := by
  rw [input_history_transition]
  norm_num [Thesis.RoutingTransitions.transition, Thesis.RoutingTransitions.ordinary,
    Thesis.RoutingGate.chosenLogAction_eq_positive, oneWeight, positiveInput,
    preactivation, posContribution, negContribution, posDenominator, negDenominator,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool]

end IndependentRoutingHistoryBoundary
