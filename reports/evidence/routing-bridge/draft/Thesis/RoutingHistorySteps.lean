import Thesis.RoutingPolicyBridge

noncomputable section
namespace Thesis.RoutingHistorySteps
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
open Thesis.RoutingBackward Thesis.RoutingHistory Thesis.RoutingPolicyBridge
open scoped BigOperators

/-- Retain the initial activation decision, the fair oracle outcome and the
augmented route action of a full history. The continuation history is forgotten. -/
def firstStep {n : ℕ} {positive negative : Fin (n+2) → Tree} :
    Unit ⊕ (((a : Fin (n+2)) × Histories (positive a)) ⊕
      ((a : Fin (n+2)) × Histories (negative a))) → Step n
  | .inl _ => none
  | .inr (.inl h) => some (false,h.1)
  | .inr (.inr h) => some (true,h.1)

/-- Integrating every continuation after a fixed actual routing action gives
the controlling player's action probability. This holds off equilibrium too. -/
theorem routing_action_mass {k : ℕ} (q : Bool) (outside : Fin k)
    (w : Fin k → ℝ) (hw : ∀ a,0 ≤ w a) (child : Fin k → Tree)
    (plus minus : Strategy (.routing k q outside w hw child)) (a : Fin k) :
    (∑ h : Histories (.routing k q outside w hw child),
      if h.1=a then probability (.routing k q outside w hw child) plus minus h else 0) =
      (if q then plus.1 else minus.1).prob a := by
  change (∑ h : (i : Fin k) × Histories (child i),
    if h.1=a then probability (.routing k q outside w hw child) plus minus h else 0) = _
  rw [Fintype.sum_sigma]
  simp only [probability]
  calc
    (∑ i, ∑ h : Histories (child i), if i=a then
        (if q then plus.1 else minus.1).prob i *
          probability (child i) (plus.2 i) (minus.2 i) h else 0) =
        ∑ i, if i=a then (if q then plus.1 else minus.1).prob i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i=a
      · simp only [hi,ite_true,← Finset.mul_sum,probability_normalized,mul_one]
      · simp [hi]
    _ = _ := by simp

theorem half_routing_action_mass {k : ℕ} (child : Fin k → Tree)
    (policy : Policy (Fin k)) (plus minus : (a : Fin k) → Strategy (child a)) (a : Fin k) :
    (∑ h : (i : Fin k) × Histories (child i), if h.1=a then
      (1/2 : ℝ) * (policy.prob h.1 * probability (child h.1) (plus h.1) (minus h.1) h.2)
      else 0) = policy.prob a / 2 := by
  rw [Fintype.sum_sigma]
  calc
    (∑ i, ∑ h : Histories (child i), if i=a then
      (1/2 : ℝ) * (policy.prob i * probability (child i) (plus i) (minus i) h) else 0) =
      ∑ i, if i=a then (1/2 : ℝ) * policy.prob i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i=a
        · simp only [hi,ite_true,← mul_assoc,← Finset.mul_sum,probability_normalized,mul_one]
        · simp [hi]
    _ = _ := by simp; ring

/-- The first-microstep marginal of the complete history law on the existing
activation/routing tree. Separate stop, bias and outside actions are retained. -/
theorem firstStep_probability {n : ℕ} (q qp qn : Bool)
    (op on : Fin (n+2)) (wp wn : Fin (n+2) → ℝ)
    (hp : ∀ a,0 ≤ wp a) (hn : ∀ a,0 ≤ wn a)
    (cp cn : Fin (n+2) → Tree)
    (plus minus : Strategy (.activation q
      (.routing (n+2) qp op wp hp cp) (.routing (n+2) qn on wn hn cn)))
    (s : Step n) :
    (∑ h : Histories (.activation q
        (.routing (n+2) qp op wp hp cp) (.routing (n+2) qn on wn hn cn)),
      if firstStep h=s then probability (.activation q
        (.routing (n+2) qp op wp hp cp) (.routing (n+2) qn on wn hn cn)) plus minus h
        else 0) =
      stepProbability (if q then plus.1 else minus.1)
        (if qp then plus.2.1.1 else minus.2.1.1)
        (if qn then plus.2.2.1 else minus.2.2.1) s := by
  change (∑ h : Unit ⊕ (((a : Fin (n+2)) × Histories (cp a)) ⊕
      ((a : Fin (n+2)) × Histories (cn a))),
    if firstStep h=s then probability (.activation q
      (.routing (n+2) qp op wp hp cp) (.routing (n+2) qn on wn hn cn)) plus minus h
      else 0) = _
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  cases s with
  | none => simp [firstStep,probability,stepProbability]
  | some s =>
      rcases s with ⟨b,a⟩
      cases b
      all_goals
        by_cases hg : (if q then plus.1 else minus.1)=true
        · simp only [firstStep,probability,stepProbability,hg,ite_true,
            Option.some.injEq,Prod.mk.injEq,Bool.false_eq_true,Bool.true_eq_false,
            false_and,true_and,ite_false,Finset.sum_const_zero,
            zero_add,add_zero,ite_self]
          exact half_routing_action_mass _ _ _ _ a
        · simp [firstStep,probability,stepProbability,hg]

/-- Composition of finite probability pushforwards, proved by summing actual
fibers. No probabilistic independence assumption is used. -/
theorem pushforward_comp {X Y Z : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] [DecidableEq Z] (p : X → ℝ) (f : X → Y) (g : Y → Z) (z : Z) :
    (∑ x, if g (f x)=z then p x else 0) =
      ∑ y, if g y=z then (∑ x, if f x=y then p x else 0) else 0 := by
  symm
  have h (y : Y) :
      (if g y=z then (∑ x, if f x=y then p x else 0) else 0) =
      ∑ x, if f x=y then (if g y=z then p x else 0) else 0 := by
    by_cases hy : g y=z <;> simp [hy]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

def inputProjection {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool) :
    Histories (inputLayerGames wp wn bp bn ε hε x j q) → Step n := firstStep

def layerProjection {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree) (j : Fin k) (q : Bool) :
    Histories (layerGames wp wn bp bn ε hε input j q) → Step n := firstStep

theorem input_projection_probability {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool) (s : Step n) :
    (∑ h : Histories (inputLayerGames wp wn bp bn ε hε x j q),
      if inputProjection wp wn bp bn ε hε x j q h=s then
        probability (inputLayerGames wp wn bp bn ε hε x j q)
          (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q))
          (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)) h else 0) =
      inputStep wp wn bp bn ε hε x j q s := by
  have h := firstStep_probability q q (!q) (0 : Fin (n+2)) 0
      (extend ε (max (bp j-bn j) 0) (posContribution wp wn x j))
      (extend ε (max (-(bp j-bn j)) 0) (negContribution wp wn x j))
      (extend_nonnegative _ _ _ hε (le_max_right _ _) (fun _ => le_max_right _ _))
      (extend_nonnegative _ _ _ hε (le_max_right _ _) (fun _ => le_max_right _ _))
      _ _ (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q))
      (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)) s
  simp only [ite_self] at h
  exact h

theorem layer_projection_probability {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree)
    (j : Fin k) (q : Bool) (s : Step n) :
    (∑ h : Histories (layerGames wp wn bp bn ε hε input j q),
      if layerProjection wp wn bp bn ε hε input j q h=s then
        probability (layerGames wp wn bp bn ε hε input j q)
          (canonical 1 (layerGames wp wn bp bn ε hε input j q))
          (canonical 1 (layerGames wp wn bp bn ε hε input j q)) h else 0) =
      layerStep wp wn bp bn ε hε input j q s := by
  have h := firstStep_probability q q (!q) (0 : Fin (n+2)) 0
      (extend ε (max (bp j-bn j) 0) (fun i => max (wp j i-wn j i) 0))
      (extend ε (max (-(bp j-bn j)) 0) (fun i => max (-(wp j i-wn j i)) 0))
      (extend_nonnegative _ _ _ hε (le_max_right _ _) (fun _ => le_max_right _ _))
      (extend_nonnegative _ _ _ hε (le_max_right _ _) (fun _ => le_max_right _ _))
      _ _ (canonical 1 (layerGames wp wn bp bn ε hε input j q))
      (canonical 1 (layerGames wp wn bp bn ε hε input j q)) s
  simp only [ite_self] at h
  exact h

/-- The actual full-history law has exactly the input transition as its first
ordinary/cemetery target marginal. Signed raw inputs are allowed. -/
theorem input_history_transition {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (q : Bool)
    (target : Option (Fin n × Bool)) :
    (∑ h : Histories (inputLayerGames wp wn bp bn ε hε x j q),
      if stepTarget q (inputProjection wp wn bp bn ε hε x j q h)=target then
        probability (inputLayerGames wp wn bp bn ε hε x j q)
          (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q))
          (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)) h else 0) =
      Thesis.RoutingTransitions.transition wp wn bp bn ε x j q target := by
  rw [pushforward_comp]
  simp_rw [input_projection_probability]
  exact congrFun (input_collapsed_transition wp wn bp bn ε hε x j q) target

/-- The corresponding actual hidden-layer marginal; predecessor games encode
non-negative activations, while bias/outside and stopped histories all survive
until the explicit cemetery projection. -/
theorem layer_history_transition {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (input : Fin n → Bool → Tree)
    (x : Vec n) (hx : ∀ i,0 ≤ x i)
    (hv : ∀ i q,value 1 (input i q)=signed q (x i))
    (j : Fin k) (q : Bool) (target : Option (Fin n × Bool)) :
    (∑ h : Histories (layerGames wp wn bp bn ε hε input j q),
      if stepTarget q (layerProjection wp wn bp bn ε hε input j q h)=target then
        probability (layerGames wp wn bp bn ε hε input j q)
          (canonical 1 (layerGames wp wn bp bn ε hε input j q))
          (canonical 1 (layerGames wp wn bp bn ε hε input j q)) h else 0) =
      Thesis.RoutingTransitions.transition wp wn bp bn ε x j q target := by
  rw [pushforward_comp]
  simp_rw [layer_projection_probability]
  exact congrFun (layer_collapsed_transition wp wn bp bn ε hε input x hx hv j q) target

end Thesis.RoutingHistorySteps
