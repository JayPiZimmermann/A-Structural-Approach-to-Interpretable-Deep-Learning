import Thesis.SoftplusBackward
import Thesis.StoppingBoundary

/-! Softplus occupations at constant and nonconstant neurons. A zero-fan-in
continuation is absorbed; its zero structural discount makes all ordinary input
occupations zero. No positive-row assumption is needed for the derivative identity. -/
noncomputable section
namespace Thesis.SoftplusBoundary
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward
open Thesis.SoftplusBackward Thesis.Regularization

/-- Sigmoid stopping mixed with the total continuation kernel, including zero rows. -/
def transition {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (j : Fin k) (turn : Bool) (target : Option (Fin n × Bool)) : ℝ :=
  (if target = none then 1 - gate θ z else 0) +
    gate θ z * Thesis.StoppingBoundary.transition wp wn (fun _ => true) j turn target

theorem transition_normalized {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (j : Fin k) (turn : Bool) : (∑ target, transition θ z wp wn j turn target) = 1 := by
  simp only [transition, Finset.sum_add_distrib, ← Finset.mul_sum,
    Thesis.StoppingBoundary.transition_normalized, mul_one]
  simp

theorem transition_nonnegative {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i)
    (j : Fin k) (turn : Bool) (target : Option (Fin n × Bool)) :
    0 ≤ transition θ z wp wn j turn target := by
  apply add_nonneg
  · split_ifs
    · exact sub_nonneg.mpr (gate_lt_one θ z).le
    · exact le_rfl
  · exact mul_nonneg (gate_pos θ z).le
      (Thesis.StoppingBoundary.transition_nonnegative wp wn (fun _ => true) hw j turn target)

theorem transition_ordinary {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (j : Fin k) (turn p : Bool) (i : Fin n) :
    transition θ z wp wn j turn (some (i,p)) =
      gate θ z * (if p = turn then wp j i else wn j i) / fanIn wp wn j := by
  simp only [transition, Option.some_ne_none, ite_false, zero_add,
    Thesis.StoppingBoundary.transition, ite_true]
  ring

theorem zero_fanIn_absorbs {n k} (θ z : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (j : Fin k) (turn : Bool) (hz : fanIn wp wn j = 0) :
    transition θ z wp wn j turn none = 1 := by
  simp [transition, Thesis.StoppingBoundary.transition, hz]

theorem path_discount_recovery {n m} (net : Network n m) (θ : ℝ)
    (hw : net.Nonnegative) (x : Vec n) (j : Fin m) (i : Fin n) (p : Bool)
    (path : Paths (softTrace θ net x)) :
    softDiscount θ net x path * softProbability θ net x j i p path =
      rawWeight (softTrace θ net x) j i p path := by
  induction net generalizing p with
  | output n => simp [softDiscount, softProbability, softTrace, rawWeight]
  | layer wp wn bp bn tail ih =>
      have hweights : ∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i := fun j i => ⟨hw.1 j i, hw.2.1 j i⟩
      by_cases hz : fanIn wp wn path.1 = 0
      · have he := Thesis.StoppingBoundary.zero_fanIn_weights wp wn hweights path.1 hz i
        simp [softDiscount, softProbability, softTrace, rawWeight, hz, he.1, he.2]
      · simp only [softDiscount, softProbability, softTrace, rawWeight, ite_true]
        have ht := ih hw.2.2 (softLayer θ wp wn bp bn x) j path.1
          (Bool.xor p path.2.1) path.2.2
        cases hs : path.2.1 <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at *
        all_goals rw [← ht]; field_simp

theorem occupation_kernels {n m} (net : Network n m) (θ : ℝ)
    (hw : net.Nonnegative) (x : Vec n) (j : Fin m) (i : Fin n) :
    softOccupation net θ x j i false = (occupations (softTrace θ net x)).1 j i ∧
      softOccupation net θ x j i true = (occupations (softTrace θ net x)).2 j i := by
  simp only [softOccupation, path_discount_recovery net θ hw]
  exact raw_path_integral _ j i

theorem probability_nonnegative {n m} (net : Network n m) (θ : ℝ)
    (hw : net.Nonnegative) (x : Vec n) (j : Fin m) (i : Fin n) (p : Bool)
    (path : Paths (softTrace θ net x)) : 0 ≤ softProbability θ net x j i p path := by
  induction net generalizing p with
  | output n => simp only [softProbability]; split_ifs <;> norm_num
  | layer wp wn bp bn tail ih =>
      simp only [softProbability]
      apply mul_nonneg _ (ih hw.2.2 (softLayer θ wp wn bp bn x) j path.1
        (Bool.xor p path.2.1) path.2.2)
      apply div_nonneg _ (Thesis.StoppingBoundary.fanIn_nonnegative wp wn
        (fun j i => ⟨hw.1 j i, hw.2.1 j i⟩) _)
      apply mul_nonneg (gate_pos θ _).le
      split_ifs
      · exact hw.2.1 _ _
      · exact hw.1 _ _

theorem discount_nonnegative {n m} (net : Network n m) (θ : ℝ)
    (hw : net.Nonnegative) (x : Vec n) (path : Paths (softTrace θ net x)) :
    0 ≤ softDiscount θ net x path := by
  induction net with
  | output n => exact zero_le_one
  | layer wp wn bp bn tail ih =>
      exact mul_nonneg (Thesis.StoppingBoundary.fanIn_nonnegative wp wn
        (fun j i => ⟨hw.1 j i, hw.2.1 j i⟩) _) (ih hw.2.2 _ path.2.2)

theorem occupation_nonnegative {n m} (net : Network n m) (θ : ℝ)
    (hw : net.Nonnegative) (x : Vec n) (j : Fin m) (i : Fin n) (p : Bool) :
    0 ≤ softOccupation net θ x j i p :=
  Finset.sum_nonneg fun path _ => mul_nonneg (discount_nonnegative net θ hw x path)
    (probability_nonnegative net θ hw x j i p path)

/-- Actual Softplus derivative for all nonnegative split weights, including zero fan-in. -/
theorem gradient_occupation {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (hw : net.Nonnegative) (x : Vec n) (j : Fin m) (i : Fin n) :
    fderiv ℝ (softEval θ net) x (Pi.single i 1) j =
      softOccupation net θ x j i false - softOccupation net θ x j i true := by
  rw [(softEval_hasFDerivAt net θ hθ x).fderiv, originalJac_coordinate_paths]
  simp only [softOccupation, path_discount_recovery net θ hw]

end Thesis.SoftplusBoundary
