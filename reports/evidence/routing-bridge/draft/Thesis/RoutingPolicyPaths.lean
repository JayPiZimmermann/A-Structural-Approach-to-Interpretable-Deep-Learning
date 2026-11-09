import Thesis.RoutingPolicyBridge

noncomputable section
namespace Thesis.RoutingPolicyPaths
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingNetwork
open Thesis.RoutingBackward Thesis.RoutingPolicyBridge Thesis.BackwardGames
open scoped BigOperators

/-- Ordinary surviving paths formed from the actual canonical policies of the
propagated source games. The endpoint owner is tracked separately from the root
owner. Bias, outside and stopped actions do not have an ordinary endpoint. -/
def propagateProbability (α β ε : ℝ) (hε : 0 ≤ ε) :
    {n m : ℕ} → (net : Network n m) → (Fin n → Bool → Tree) → (x : Vec n) →
      Fin m → Fin n → Bool → Bool → Paths (routingTrace α β ε net x) → ℝ
  | _, _, .output _, _, _, j, i, q, r, _ => if j=i ∧ q=r then 1 else 0
  | _, _, .layer wp wn bp bn tail, input, x, j, i, q, r, path =>
      layerStep wp wn bp bn ε hε input path.1 (Bool.xor r path.2.1)
        (some (path.2.1,i.succ.succ)) *
      propagateProbability α β ε hε tail (layerGames wp wn bp bn ε hε input)
        (fun h => relu (preactivation wp wn bp bn x h)) j path.1 q
        (Bool.xor r path.2.1) path.2.2

/-- Products of actual canonical ordinary microsteps equal the independently
defined routing path law. This is an ordinary-surviving-path identity; complete
stopped histories are represented separately by RoutingHistory.Histories. -/
theorem propagateProbability_eq {n m} (net : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε)
    (input : Fin n → Bool → Tree) (x : Vec n) (hx : ∀ i,0 ≤ x i)
    (hv : ∀ i q,value 1 (input i q)=signed q (x i))
    (j : Fin m) (i : Fin n) (q r : Bool) (path : Paths (routingTrace α β ε net x)) :
    propagateProbability α β ε hε net input x j i q r path =
      rgProbability α β ε net x j i (Bool.xor q r) path := by
  induction net generalizing q r with
  | output n =>
      cases q <;> cases r <;> simp [propagateProbability,rgProbability]
  | layer wp wn bp bn tail ih =>
      simp only [propagateProbability,rgProbability]
      rw [layerStep_ordinary wp wn bp bn ε hε input x hx hv]
      rw [ih (layerGames wp wn bp bn ε hε input)
        (fun h => relu (preactivation wp wn bp bn x h))
        (fun _ => le_max_right _ _) (layerGames_value wp wn bp bn ε hε input x hx hv)
        j path.1 q (Bool.xor r path.2.1) path.2.2]
      rw [Thesis.RoutingTransitions.transition_ordinary]
      cases r <;> cases path.2.1 <;> simp [Bool.xor_assoc]

/-- Ordinary paths of the actual full network game. The first layer fuses signed
raw inputs into contribution masses; the propagated hidden games use their
actual non-negative ReLU values. -/
def networkProbability (α β ε : ℝ) (hε : 0 ≤ ε) :
    {n m : ℕ} → (net : Network n m) → (x : Vec n) → Fin m → Fin n →
      Bool → Bool → Paths (routingTrace α β ε net x) → ℝ
  | _, _, .output _, _, j, i, q, r, _ => if j=i ∧ q=r then 1 else 0
  | _, _, .layer wp wn bp bn tail, x, j, i, q, r, path =>
      inputStep wp wn bp bn ε hε x path.1 (Bool.xor r path.2.1)
        (some (path.2.1,i.succ.succ)) *
      propagateProbability α β ε hε tail (inputLayerGames wp wn bp bn ε hε x)
        (fun h => relu (preactivation wp wn bp bn x h)) j path.1 q
        (Bool.xor r path.2.1) path.2.2

theorem networkProbability_eq {n m} (net : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (i : Fin n) (q r : Bool)
    (path : Paths (routingTrace α β ε net x)) :
    networkProbability α β ε hε net x j i q r path =
      rgProbability α β ε net x j i (Bool.xor q r) path := by
  cases net with
  | output n => cases q <;> cases r <;> simp [networkProbability,rgProbability]
  | layer wp wn bp bn tail =>
      simp only [networkProbability,rgProbability]
      rw [inputStep_ordinary]
      rw [propagateProbability_eq tail α β ε hε (inputLayerGames wp wn bp bn ε hε x)
        (fun h => relu (preactivation wp wn bp bn x h)) (fun _ => le_max_right _ _)
        (inputLayerGames_value wp wn bp bn ε hε x)]
      rw [Thesis.RoutingTransitions.transition_ordinary]
      cases r <;> cases path.2.1 <;> simp [Bool.xor_assoc]

/-- The source branch multiplier along the same actual microsteps. -/
def policyDiscount (α β ε : ℝ) : {n m : ℕ} → (net : Network n m) → (x : Vec n) →
    Fin n → Paths (routingTrace α β ε net x) → ℝ
  | _, _, .output _, _, _, _ => 1
  | _, _, .layer wp wn bp bn tail, x, i, path =>
      stepDiscount α β (some (path.2.1,i.succ.succ)) *
        policyDiscount α β ε tail (fun h => relu (preactivation wp wn bp bn x h))
          path.1 path.2.2

theorem policyDiscount_eq {n m} (net : Network n m) (α β ε : ℝ) (x : Vec n) (i : Fin n)
    (path : Paths (routingTrace α β ε net x)) :
    policyDiscount α β ε net x i path = rgDiscount α β ε net x path := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih => simp only [policyDiscount,stepDiscount,rgDiscount,ih]

/-- Discounted ordinary endpoints obtained from actual canonical policies agree
with the alpha-beta occupation used by the existing backward theorem. -/
theorem canonical_path_occupation {n m} (net : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (i : Fin n) (q r : Bool) :
    (∑ path : Paths (routingTrace α β ε net x),
      policyDiscount α β ε net x i path * networkProbability α β ε hε net x j i q r path) =
      rgOccupation net α β ε x j i (Bool.xor q r) := by
  simp only [policyDiscount_eq,networkProbability_eq,rgOccupation]

end Thesis.RoutingPolicyPaths
