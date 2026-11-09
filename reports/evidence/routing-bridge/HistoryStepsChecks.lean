import Thesis.RoutingHistorySteps

noncomputable section
set_option autoImplicit false
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
open Thesis.RoutingBackward Thesis.RoutingHistory Thesis.RoutingPolicyBridge
open Thesis.RoutingHistorySteps
open scoped BigOperators

-- These literal quantified contracts were authored from the intended
-- probability-fiber statements, independently of Lean's inferred-type printer.
example : ∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool)
    (target : Option (Fin n × Bool)),
    (∑ h : Histories (inputLayerGames wp wn bp bn ε hε x j q),
      if stepTarget q (inputProjection wp wn bp bn ε hε x j q h)=target then
        probability (inputLayerGames wp wn bp bn ε hε x j q)
          (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q))
          (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)) h else 0) =
      Thesis.RoutingTransitions.transition wp wn bp bn ε x j q target :=
  @input_history_transition

example : ∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree)
    (x : Vec n) (hx : ∀ i,0 ≤ x i)
    (hv : ∀ i q,value 1 (input i q)=signed q (x i))
    (j : Fin k) (q : Bool) (target : Option (Fin n × Bool)),
    (∑ h : Histories (layerGames wp wn bp bn ε hε input j q),
      if stepTarget q (layerProjection wp wn bp bn ε hε input j q h)=target then
        probability (layerGames wp wn bp bn ε hε input j q)
          (canonical 1 (layerGames wp wn bp bn ε hε input j q))
          (canonical 1 (layerGames wp wn bp bn ε hε input j q)) h else 0) =
      Thesis.RoutingTransitions.transition wp wn bp bn ε x j q target :=
  @layer_history_transition

example : ∀ {n : ℕ} (q qp qn : Bool) (op on : Fin (n+2))
    (wp wn : Fin (n+2) → ℝ) (hp : ∀ a,0 ≤ wp a) (hn : ∀ a,0 ≤ wn a)
    (cp cn : Fin (n+2) → Tree)
    (plus minus : Strategy (.activation q
      (.routing (n+2) qp op wp hp cp) (.routing (n+2) qn on wn hn cn))) (s : Step n),
    (∑ h : Histories (.activation q
      (.routing (n+2) qp op wp hp cp) (.routing (n+2) qn on wn hn cn)),
      if firstStep h=s then probability (.activation q
        (.routing (n+2) qp op wp hp cp) (.routing (n+2) qn on wn hn cn)) plus minus h
        else 0) =
      stepProbability (if q then plus.1 else minus.1)
        (if qp then plus.2.1.1 else minus.2.1.1)
        (if qn then plus.2.2.1 else minus.2.2.1) s := @firstStep_probability

namespace HistoryStepsBoundary

-- Off-equilibrium example: the two augmented absorbing actions stay distinct
-- before the target projection, although both map to the cemetery.
def toy : Tree := .activation true
  (.routing 2 true 0 (fun _ => 0) (fun _ => le_rfl) (fun _ => .terminal 0))
  (.routing 2 false 0 (fun _ => 0) (fun _ => le_rfl) (fun _ => .terminal 0))

def profile : Strategy toy :=
  (true,(pure 1,fun _ => ()),(pure 0,fun _ => ()))

example : firstStep (positive := fun _ : Fin 2 => Tree.terminal 0)
    (negative := fun _ : Fin 2 => Tree.terminal 0) (.inr (.inl ⟨1,()⟩)) = some (false,1) ∧
    firstStep (positive := fun _ : Fin 2 => Tree.terminal 0)
    (negative := fun _ : Fin 2 => Tree.terminal 0) (.inr (.inr ⟨0,()⟩)) = some (true,0) := by
  constructor <;> rfl

example : probability toy profile profile (.inr (.inl ⟨1,()⟩))=1/2 ∧
    probability toy profile profile (.inr (.inr ⟨0,()⟩))=1/2 := by
  unfold profile
  unfold toy
  norm_num [probability,Thesis.RoutingExtended.pure]

example : stepTarget (n := 0) true (some (false,1))=none ∧
    stepTarget (n := 0) true (some (true,0))=none := by
  constructor <;> rfl

def wp : Matrix (Fin 1) (Fin 1) ℝ := 0
def wn : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
def zeroBias : Vec 1 := 0
def signedInput : Vec 1 := fun _ => -2
def fused := inputLayerGames wp wn zeroBias zeroBias 0 (by norm_num) signedInput 0 true

-- The signed raw product is positive. Its negative stream is empty at epsilon
-- zero and contributes half the probability to the outside/cemetery action.
example : (∑ h : Histories fused,
    if stepTarget true (inputProjection wp wn zeroBias zeroBias 0 (by norm_num)
      signedInput 0 true h)=some (0,true) then
      probability fused (canonical 1 fused) (canonical 1 fused) h else 0)=1/2 := by
  unfold fused
  rw [input_history_transition]
  norm_num [Thesis.RoutingTransitions.transition,Thesis.RoutingTransitions.ordinary,
    Thesis.RoutingGate.chosenLogAction_eq_positive,preactivation,posContribution,
    negContribution,posDenominator,negDenominator,wp,wn,zeroBias,signedInput,
    Matrix.mulVec, dotProduct]

example : (∑ h : Histories fused,
    if stepTarget true (inputProjection wp wn zeroBias zeroBias 0 (by norm_num)
      signedInput 0 true h)=none then
      probability fused (canonical 1 fused) (canonical 1 fused) h else 0)=1/2 := by
  unfold fused
  rw [input_history_transition]
  norm_num [Thesis.RoutingTransitions.transition,Thesis.RoutingTransitions.ordinary,
    Thesis.RoutingGate.chosenLogAction_eq_positive,preactivation,posContribution,
    negContribution,posDenominator,negDenominator,wp,wn,zeroBias,signedInput,
    Matrix.mulVec, dotProduct,Fintype.sum_prod_type,Fintype.sum_bool]

-- At the activation log tie the actual initial microstep stops with mass one.
example : (∑ h : Histories (inputLayerGames wp wn zeroBias zeroBias 0 (by norm_num)
      (0 : Vec 1) 0 true),
    if inputProjection wp wn zeroBias zeroBias 0 (by norm_num) (0 : Vec 1) 0 true h=none then
      probability (inputLayerGames wp wn zeroBias zeroBias 0 (by norm_num) (0 : Vec 1) 0 true)
        (canonical 1 (inputLayerGames wp wn zeroBias zeroBias 0 (by norm_num) (0 : Vec 1) 0 true))
        (canonical 1 (inputLayerGames wp wn zeroBias zeroBias 0 (by norm_num) (0 : Vec 1) 0 true)) h
      else 0)=1 := by
  rw [input_projection_probability]
  simp only [inputStep,stepProbability,inputLayerGames_selected_gate]
  norm_num [preactivation,zeroBias]

end HistoryStepsBoundary

#print axioms Thesis.RoutingHistorySteps.routing_action_mass
#print axioms Thesis.RoutingHistorySteps.half_routing_action_mass
#print axioms Thesis.RoutingHistorySteps.firstStep_probability
#print axioms Thesis.RoutingHistorySteps.pushforward_comp
#print axioms Thesis.RoutingHistorySteps.input_projection_probability
#print axioms Thesis.RoutingHistorySteps.layer_projection_probability
#print axioms Thesis.RoutingHistorySteps.input_history_transition
#print axioms Thesis.RoutingHistorySteps.layer_history_transition
