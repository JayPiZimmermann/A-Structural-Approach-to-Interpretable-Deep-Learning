import Thesis.RoutingHistory
import Thesis.RoutingTransitions

noncomputable section
namespace Thesis.RoutingPolicyBridge
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingExtended Thesis.RoutingNetwork
open Thesis.RoutingBackward
open scoped BigOperators

/-- One actual activation/oracle/routing microhistory: none is activation
stopping; some retains both the oracle sign and the full augmented route action. -/
abbrev Step (n : ℕ) := Option (Bool × Fin (n+2))

def stepProbability {n} (gate : Bool) (positive negative : Policy (Fin (n+2))) : Step n → ℝ
  | none => if gate then 0 else 1
  | some (b,a) => if gate then (if b then negative.prob a else positive.prob a)/2 else 0

def stepDiscount {n} (α β : ℝ) : Step n → ℝ
  | none => 1
  | some (b,_) => if b then 2*β else 2*α

def stepTarget {n} (q : Bool) : Step n → Option (Fin n × Bool)
  | none => none
  | some (b,a) => Fin.cases none (Fin.cases none (fun i => some (i,Bool.xor q b))) a

def collapsed {n} (gate : Bool) (positive negative : Policy (Fin (n+2))) (q : Bool)
    (target : Option (Fin n × Bool)) : ℝ :=
  ∑ h : Step n,if stepTarget q h=target then stepProbability gate positive negative h else 0

theorem stepProbability_normalized {n} (gate : Bool) (positive negative : Policy (Fin (n+2))) :
    (∑ h : Step n,stepProbability gate positive negative h)=1 := by
  cases gate <;> simp [stepProbability,Fintype.sum_option,Fintype.sum_prod_type,
    ← Finset.sum_div,positive.normalized,negative.normalized]

theorem stepProbability_nonnegative {n} (gate : Bool) (positive negative : Policy (Fin (n+2)))
    (h : Step n) : 0≤stepProbability gate positive negative h := by
  cases h with
  | none => cases gate <;> norm_num [stepProbability]
  | some h => rcases h with ⟨b,a⟩; cases gate <;> cases b <;>
      simp only [stepProbability,Bool.false_eq_true,ite_false,ite_true]
      all_goals first | exact le_rfl | exact div_nonneg (positive.nonnegative a) (by norm_num)
        | exact div_nonneg (negative.nonnegative a) (by norm_num)

theorem collapsed_normalized {n} (gate : Bool) (positive negative : Policy (Fin (n+2))) (q : Bool) :
    (∑ target,collapsed gate positive negative q target)=1 := by
  unfold collapsed
  rw [Finset.sum_comm]
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using
    stepProbability_normalized gate positive negative

/-- Exact pushforward of the source microstep, with the fair oracle probability
and ownership switch preserved. Bias/outside actions have no ordinary target. -/
theorem collapsed_ordinary {n} (gate : Bool) (positive negative : Policy (Fin (n+2)))
    (q b : Bool) (i : Fin n) :
    collapsed gate positive negative q (some (i,Bool.xor q b)) =
      if gate then (if b then negative.prob i.succ.succ else positive.prob i.succ.succ)/2 else 0 := by
  cases gate <;> cases q <;> cases b <;>
    simp [collapsed,stepTarget,stepProbability,Fintype.sum_option,Fintype.sum_prod_type,
      Fin.sum_univ_succ]

theorem collapsed_cemetery {n} (gate : Bool) (positive negative : Policy (Fin (n+2))) (q : Bool) :
    collapsed gate positive negative q none =
      1-∑ target : Fin n × Bool,collapsed gate positive negative q (some target) := by
  have h := collapsed_normalized gate positive negative q
  rw [Fintype.sum_option] at h
  linarith

def inputPositive {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0≤ε) (x : Vec n) (j : Fin k) (q : Bool) : Policy (Fin (n+2)) :=
  (canonical 1 (route q ε (max (bp j-bn j) 0) (posContribution wp wn x j)
    (fun _ => .terminal (signed q 1)) hε (le_max_right _ _) (fun _ => le_max_right _ _))).1

def inputNegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0≤ε) (x : Vec n) (j : Fin k) (q : Bool) : Policy (Fin (n+2)) :=
  (canonical 1 (route (!q) ε (max (-(bp j-bn j)) 0) (negContribution wp wn x j)
    (fun _ => .terminal (signed (!q) 1)) hε (le_max_right _ _) (fun _ => le_max_right _ _))).1

def layerPositive {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0≤ε) (input : Fin n → Bool → Tree) (j : Fin k) (q : Bool) : Policy (Fin (n+2)) :=
  (canonical 1 (route q ε (max (bp j-bn j) 0) (fun i => max (wp j i-wn j i) 0)
    (fun i => input i q) hε (le_max_right _ _) (fun _ => le_max_right _ _))).1

def layerNegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0≤ε) (input : Fin n → Bool → Tree) (j : Fin k) (q : Bool) : Policy (Fin (n+2)) :=
  (canonical 1 (route (!q) ε (max (-(bp j-bn j)) 0) (fun i => max (-(wp j i-wn j i)) 0)
    (fun i => input i (!q)) hε (le_max_right _ _) (fun _ => le_max_right _ _))).1

theorem input_policy_probabilities {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0≤ε) (x : Vec n) (j : Fin k) (q : Bool) (i : Fin n) :
    (inputPositive wp wn bp bn ε hε x j q).prob i.succ.succ=
      posContribution wp wn x j i / posDenominator wp wn bp bn ε x j ∧
    (inputNegative wp wn bp bn ε hε x j q).prob i.succ.succ=
      negContribution wp wn x j i / negDenominator wp wn bp bn ε x j := by
  constructor
  · rw [inputPositive,route_anchor_ordinary_probability q ε _ _ (fun _ => 1) _ _ _ _
      (fun _ => zero_le_one) (fun _ => rfl)]
    simp only [mul_one,posDenominator]
    congr 1 <;> ring
  · rw [inputNegative,route_anchor_ordinary_probability (!q) ε _ _ (fun _ => 1) _ _ _ _
      (fun _ => zero_le_one) (fun _ => rfl)]
    simp only [mul_one,negDenominator]
    congr 1 <;> ring

theorem layer_policy_probabilities {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0≤ε) (input : Fin n → Bool → Tree) (x : Vec n)
    (hx : ∀ i,0≤x i) (hv : ∀ i q,value 1 (input i q)=signed q (x i))
    (j : Fin k) (q : Bool) (i : Fin n) :
    (layerPositive wp wn bp bn ε hε input j q).prob i.succ.succ=
      posContribution wp wn x j i / posDenominator wp wn bp bn ε x j ∧
    (layerNegative wp wn bp bn ε hε input j q).prob i.succ.succ=
      negContribution wp wn x j i / negDenominator wp wn bp bn ε x j := by
  have hp (a : Fin n) : max (wp j a-wn j a) 0*x a=posContribution wp wn x j a := by
    rw [max_mul_of_nonneg _ _ (hx a)]
    simp [posContribution,mul_comm]
  have hn (a : Fin n) : max (-(wp j a-wn j a)) 0*x a=negContribution wp wn x j a := by
    rw [max_mul_of_nonneg _ _ (hx a)]
    unfold negContribution
    congr 1 <;> ring
  constructor
  · rw [layerPositive,route_anchor_ordinary_probability q ε _ _ x _ _ _ _ hx (fun a => hv a q)]
    simp_rw [hp]
    unfold posDenominator
    congr 1 <;> ring
  · rw [layerNegative,route_anchor_ordinary_probability (!q) ε _ _ x _ _ _ _ hx (fun a => hv a (!q))]
    simp_rw [hn]
    unfold negDenominator
    congr 1 <;> ring

def inputStep {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0≤ε) (x : Vec n) (j : Fin k) (q : Bool) : Step n → ℝ :=
  stepProbability (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)).1
    (inputPositive wp wn bp bn ε hε x j q) (inputNegative wp wn bp bn ε hε x j q)

def layerStep {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0≤ε) (input : Fin n → Bool → Tree) (j : Fin k) (q : Bool) : Step n → ℝ :=
  stepProbability (canonical 1 (layerGames wp wn bp bn ε hε input j q)).1
    (layerPositive wp wn bp bn ε hε input j q) (layerNegative wp wn bp bn ε hε input j q)

theorem inputStep_ordinary {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0≤ε) (x : Vec n) (j : Fin k) (q b : Bool) (i : Fin n) :
    inputStep wp wn bp bn ε hε x j q (some (b,i.succ.succ))=
      Thesis.RoutingTransitions.transition wp wn bp bn ε x j q (some (i,Bool.xor q b)) := by
  rw [Thesis.RoutingTransitions.transition_ordinary]
  simp only [inputStep,stepProbability,inputLayerGames_selected_gate,decide_eq_true_eq]
  rw [(input_policy_probabilities wp wn bp bn ε hε x j q i).1,
      (input_policy_probabilities wp wn bp bn ε hε x j q i).2]
  cases q <;> cases b <;> rfl

theorem layerStep_ordinary {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (hε : 0≤ε) (input : Fin n → Bool → Tree) (x : Vec n)
    (hx : ∀ i,0≤x i) (hv : ∀ i q,value 1 (input i q)=signed q (x i))
    (j : Fin k) (q b : Bool) (i : Fin n) :
    layerStep wp wn bp bn ε hε input j q (some (b,i.succ.succ))=
      Thesis.RoutingTransitions.transition wp wn bp bn ε x j q (some (i,Bool.xor q b)) := by
  rw [Thesis.RoutingTransitions.transition_ordinary]
  simp only [layerStep,stepProbability,layerGames_selected_gate wp wn bp bn ε hε input x hx hv,
    decide_eq_true_eq]
  rw [(layer_policy_probabilities wp wn bp bn ε hε input x hx hv j q i).1,
      (layer_policy_probabilities wp wn bp bn ε hε input x hx hv j q i).2]
  cases q <;> cases b <;> rfl

end Thesis.RoutingPolicyBridge
