import Thesis.RoutingBackward
import Thesis.RoutingGate

/-! Total routing rows at the nonnegative-activation anchor. Bias and stabilizer
mass remain in the denominators. The cemetery receives their omitted mass and
the mass of empty sign streams; the log-space activation tie selects stopping.
This constructs normalized rows and ordinary path probabilities, not an
all-policy extensive-form equilibrium. -/
noncomputable section
namespace Thesis.RoutingTransitions
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward

theorem posDenominator_nonnegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) :
    0 ≤ posDenominator wp wn bp bn ε x j :=
  add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => le_max_right _ _)
    (le_max_right _ _)) hε

theorem negDenominator_nonnegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) :
    0 ≤ negDenominator wp wn bp bn ε x j :=
  add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => le_max_right _ _)
    (le_max_right _ _)) hε

theorem positive_stream_subprobability {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) :
    (∑ i, posContribution wp wn x j i / posDenominator wp wn bp bn ε x j) ≤ 1 := by
  rw [← Finset.sum_div]
  apply div_le_one_of_le₀ _ (posDenominator_nonnegative wp wn bp bn ε hε x j)
  have hb := le_max_right (bp j - bn j) 0
  unfold posDenominator
  linarith

theorem negative_stream_subprobability {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) :
    (∑ i, negContribution wp wn x j i / negDenominator wp wn bp bn ε x j) ≤ 1 := by
  rw [← Finset.sum_div]
  apply div_le_one_of_le₀ _ (negDenominator_nonnegative wp wn bp bn ε hε x j)
  have hb := le_max_right (-(bp j - bn j)) 0
  unfold negDenominator
  linarith

def ordinary {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (x : Vec n) (j : Fin k) (turn : Bool) (target : Fin n × Bool) : ℝ :=
  (if target.2 = turn then
    posContribution wp wn x j target.1 / posDenominator wp wn bp bn ε x j
   else negContribution wp wn x j target.1 / negDenominator wp wn bp bn ε x j) / 2

theorem ordinary_nonnegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k)
    (turn : Bool) (target : Fin n × Bool) : 0 ≤ ordinary wp wn bp bn ε x j turn target := by
  unfold ordinary
  apply div_nonneg _ (by norm_num)
  split_ifs
  · exact div_nonneg (le_max_right _ _) (posDenominator_nonnegative wp wn bp bn ε hε x j)
  · exact div_nonneg (le_max_right _ _) (negDenominator_nonnegative wp wn bp bn ε hε x j)

theorem ordinary_sum {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (x : Vec n) (j : Fin k) (turn : Bool) :
    (∑ target, ordinary wp wn bp bn ε x j turn target) =
      (∑ i, posContribution wp wn x j i / posDenominator wp wn bp bn ε x j) / 2 +
      (∑ i, negContribution wp wn x j i / negDenominator wp wn bp bn ε x j) / 2 := by
  cases turn <;>
    simp [ordinary, Fintype.sum_prod_type,
      Finset.sum_add_distrib, Finset.sum_div, add_comm]

theorem ordinary_subprobability {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k) (turn : Bool) :
    (∑ target, ordinary wp wn bp bn ε x j turn target) ≤ 1 := by
  rw [ordinary_sum]
  have hp := positive_stream_subprobability wp wn bp bn ε hε x j
  have hn := negative_stream_subprobability wp wn bp bn ε hε x j
  linarith

/-- Full row, with all stopping, bias, stabilizer, and empty-stream mass absorbed. -/
def transition {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (x : Vec n) (j : Fin k) (turn : Bool) : Option (Fin n × Bool) → ℝ
  | none => if Thesis.RoutingGate.chosenLogAction (preactivation wp wn bp bn x j) then
      1 - ∑ target, ordinary wp wn bp bn ε x j turn target else 1
  | some target => if Thesis.RoutingGate.chosenLogAction (preactivation wp wn bp bn x j) then
      ordinary wp wn bp bn ε x j turn target else 0

theorem transition_normalized {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (x : Vec n) (j : Fin k) (turn : Bool) :
    (∑ target, transition wp wn bp bn ε x j turn target) = 1 := by
  rw [Fintype.sum_option]
  by_cases hg : Thesis.RoutingGate.chosenLogAction (preactivation wp wn bp bn x j) = true
  · simp [transition, hg]
  · simp [transition, hg]

theorem transition_nonnegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 ≤ ε) (x : Vec n) (j : Fin k)
    (turn : Bool) (target : Option (Fin n × Bool)) :
    0 ≤ transition wp wn bp bn ε x j turn target := by
  cases target with
  | none =>
      simp only [transition]
      split_ifs
      · exact sub_nonneg.mpr (ordinary_subprobability wp wn bp bn ε hε x j turn)
      · exact zero_le_one
  | some target =>
      simp only [transition]
      split_ifs
      · exact ordinary_nonnegative wp wn bp bn ε hε x j turn target
      · exact le_rfl

theorem transition_ordinary {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (x : Vec n) (j : Fin k) (turn p : Bool) (i : Fin n) :
    transition wp wn bp bn ε x j turn (some (i,p)) =
      if 0 < preactivation wp wn bp bn x j then
        (if p = turn then posContribution wp wn x j i / posDenominator wp wn bp bn ε x j
         else negContribution wp wn x j i / negDenominator wp wn bp bn ε x j) / 2 else 0 := by
  simp [transition, ordinary, Thesis.RoutingGate.chosenLogAction_eq_positive]

/-- Includes epsilon zero and empty streams under the real-division convention. -/
theorem probability_nonnegative {n m} (net : Network n m) (α β ε : ℝ) (hε : 0 ≤ ε)
    (x : Vec n) (j : Fin m) (i : Fin n) (p : Bool)
    (path : Paths (routingTrace α β ε net x)) : 0 ≤ rgProbability α β ε net x j i p path := by
  induction net generalizing p with
  | output n => simp only [rgProbability]; split_ifs <;> norm_num
  | layer wp wn bp bn tail ih =>
      simp only [rgProbability]
      apply mul_nonneg _ (ih (fun h => relu (preactivation wp wn bp bn x h)) j path.1
        (Bool.xor p path.2.1) path.2.2)
      split_ifs
      · exact div_nonneg (div_nonneg (le_max_right _ _)
          (negDenominator_nonnegative wp wn bp bn ε hε x _)) (by norm_num)
      · exact div_nonneg (div_nonneg (le_max_right _ _)
          (posDenominator_nonnegative wp wn bp bn ε hε x _)) (by norm_num)
      · exact le_rfl

theorem occupation_nonnegative {n m} (net : Network n m) (α β ε : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 ≤ ε) (x : Vec n)
    (j : Fin m) (i : Fin n) (p : Bool) : 0 ≤ rgOccupation net α β ε x j i p :=
  Finset.sum_nonneg fun path _ => mul_nonneg (rgDiscount_nonneg net α β ε hα hβ x path)
    (probability_nonnegative net α β ε hε x j i p path)

end Thesis.RoutingTransitions
