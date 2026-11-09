import Thesis.StoppingDecomposition
import Thesis.AffineOutputBackward

/-! Total stopping kernels, including constant neurons. The original strictly
positive fan-in results remain available. Selected-mask identities hold at ties;
classical derivative statements retain the strict-activation hypothesis. -/
noncomputable section
namespace Thesis.StoppingBoundary
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.StoppingDecomposition

theorem fanIn_nonnegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i) (j : Fin k) :
    0 ≤ fanIn wp wn j :=
  Finset.sum_nonneg fun i _ => add_nonneg (hw j i).1 (hw j i).2

theorem zero_fanIn_weights {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i) (j : Fin k)
    (hz : fanIn wp wn j = 0) (i : Fin n) : wp j i = 0 ∧ wn j i = 0 := by
  have hs := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => add_nonneg (hw j i).1 (hw j i).2)).mp hz
  have h := hs i (Finset.mem_univ i)
  exact ⟨by linarith [(hw j i).1, (hw j i).2],
    by linarith [(hw j i).1, (hw j i).2]⟩

/-- A constant neuron continues to the cemetery, as stipulated in the source game. -/
def transition {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (g : Fin k → Bool)
    (j : Fin k) (turn : Bool) : Option (Fin n × Bool) → ℝ
  | none => if g j ∧ fanIn wp wn j ≠ 0 then 0 else 1
  | some (i,p) => if g j then
      (if p = turn then wp j i else wn j i) / fanIn wp wn j else 0

theorem transition_normalized {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (g : Fin k → Bool) (j : Fin k) (turn : Bool) :
    (∑ target, transition wp wn g j turn target) = 1 := by
  by_cases hz : fanIn wp wn j = 0
  · simp [transition, hz, Fintype.sum_option]
  · cases hg : g j
    · simp [transition, hg, Fintype.sum_option]
    · cases turn <;>
        simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
          transition, hg, ite_true, Bool.true_eq_false, Bool.false_eq_true, ite_false]
      all_goals
        simp only [true_and]
        simp_rw [← add_div]
        rw [← Finset.sum_div]
        have hs : (∑ i, (wp j i + wn j i)) ≠ 0 := hz
        simp [fanIn, add_comm, hs]

theorem transition_nonnegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (g : Fin k → Bool) (hw : ∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i)
    (j : Fin k) (turn : Bool) (target : Option (Fin n × Bool)) :
    0 ≤ transition wp wn g j turn target := by
  cases target with
  | none => simp only [transition]; split_ifs <;> norm_num
  | some t =>
      rcases t with ⟨i,p⟩
      simp only [transition]
      split_ifs
      · exact div_nonneg (hw j i).1 (fanIn_nonnegative wp wn hw j)
      · exact div_nonneg (hw j i).2 (fanIn_nonnegative wp wn hw j)
      · exact le_rfl

theorem transition_eq_original {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (g : Fin k → Bool) (j : Fin k) (turn : Bool) (hz : fanIn wp wn j ≠ 0) :
    transition wp wn g j turn = sgTransition wp wn g j turn := by
  funext target
  cases target <;> simp [transition, sgTransition, hz]

/-- Zero-fan-in rows have zero edges, so discount recovery needs no division cancellation there. -/
theorem path_discount_recovery {n m} (tr : MaskedTrace n m)
    (hw : NonnegativeWeights tr) (j : Fin m) (i : Fin n) (p : Bool) (path : Paths tr) :
    sgDiscount tr path * sgProbability tr j i p path = rawWeight tr j i p path := by
  induction tr generalizing p with
  | output n => simp [sgDiscount, sgProbability, rawWeight]
  | layer wp wn g tail ih =>
      have ht := ih hw.2 j path.1 (Bool.xor p path.2.1) path.2.2
      by_cases hz : fanIn wp wn path.1 = 0
      · have he := zero_fanIn_weights wp wn hw.1 path.1 hz i
        simp [sgDiscount, sgProbability, rawWeight, hz, he.1, he.2]
      · simp only [sgDiscount, sgProbability, rawWeight]
        cases hg : g path.1
        · simp
        · simp only [ite_true]
          rw [show fanIn wp wn path.1 * sgDiscount tail path.2.2 *
              ((if path.2.1 then wn path.1 i else wp path.1 i) / fanIn wp wn path.1 *
                sgProbability tail j path.1 (Bool.xor p path.2.1) path.2.2) =
              (if path.2.1 then wn path.1 i else wp path.1 i) *
                (sgDiscount tail path.2.2 * sgProbability tail j path.1 (Bool.xor p path.2.1) path.2.2) by
                  field_simp]
          rw [ht]

theorem occupation_kernels {n m} (tr : MaskedTrace n m) (hw : NonnegativeWeights tr)
    (j : Fin m) (i : Fin n) :
    sgOccupation tr j i false = (occupations tr).1 j i ∧
      sgOccupation tr j i true = (occupations tr).2 j i := by
  simp only [sgOccupation, path_discount_recovery tr hw]
  exact raw_path_integral tr j i

theorem probability_nonnegative {n m} (tr : MaskedTrace n m) (hw : NonnegativeWeights tr)
    (j : Fin m) (i : Fin n) (p : Bool) (path : Paths tr) :
    0 ≤ sgProbability tr j i p path := by
  induction tr generalizing p with
  | output n => simp only [sgProbability]; split_ifs <;> norm_num
  | layer wp wn g tail ih =>
      simp only [sgProbability]
      apply mul_nonneg _ (ih hw.2 j path.1 (Bool.xor p path.2.1) path.2.2)
      split_ifs
      · exact div_nonneg (hw.1 _ _).2 (fanIn_nonnegative wp wn hw.1 _)
      · exact div_nonneg (hw.1 _ _).1 (fanIn_nonnegative wp wn hw.1 _)
      · exact le_rfl

theorem discount_nonnegative {n m} (tr : MaskedTrace n m) (hw : NonnegativeWeights tr)
    (path : Paths tr) : 0 ≤ sgDiscount tr path := by
  induction tr with
  | output n => exact zero_le_one
  | layer wp wn g tail ih =>
      exact mul_nonneg (fanIn_nonnegative wp wn hw.1 _) (ih hw.2 path.2.2)

theorem occupation_nonnegative {n m} (tr : MaskedTrace n m) (hw : NonnegativeWeights tr)
    (j : Fin m) (i : Fin n) (p : Bool) : 0 ≤ sgOccupation tr j i p :=
  Finset.sum_nonneg fun path _ => mul_nonneg (discount_nonnegative tr hw path)
    (probability_nonnegative tr hw j i p path)

/-- Algebra of the selected backward operator, including tied and constant neurons.
No ordinary derivative is asserted here. -/
theorem selected_operator_occupation {n m} (tr : MaskedTrace n m) (hw : NonnegativeWeights tr)
    (j : Fin m) (i : Fin n) :
    tr.originalJac (Pi.single i 1) j = sgOccupation tr j i false - sgOccupation tr j i true := by
  rw [originalJac_coordinate_paths]
  simp only [sgOccupation, path_discount_recovery tr hw]

/-- The actual classical derivative on a strict activation cell, now including zero rows. -/
theorem strict_gradient_occupation {n m} (net : Network n m) (x : Vec n)
    (hx : net.Strict x) (hw : NonnegativeWeights (net.originalTrace x))
    (j : Fin m) (i : Fin n) :
    fderiv ℝ net.eval x (Pi.single i 1) j =
      sgOccupation (net.originalTrace x) j i false - sgOccupation (net.originalTrace x) j i true := by
  rw [(net.hasFDerivAt_originalTrace x hx).fderiv]
  exact selected_operator_occupation _ hw j i

/-- Actual stopping-stream derivatives on strict cells, including constant neurons. -/
theorem strict_stopping_decomposition_gradient {n m} (net : Network n m)
    (x : PairVec n) (hx : net.Strict (x.1-x.2))
    (hw : NonnegativeWeights (net.originalTrace (x.1-x.2))) (j : Fin m) (i : Fin n) :
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).1 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i false ∧
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).2 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i true := by
  rw [(stopping_hasFDerivAt net x hx).fderiv, stoppingJac_occupation]
  constructor
  · change ((occupations (net.originalTrace (x.1-x.2))).1 *ᵥ (Pi.single i 1) +
      (occupations (net.originalTrace (x.1-x.2))).2 *ᵥ 0) j = _
    simp only [Matrix.mulVec_zero, add_zero]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, (occupation_kernels _ hw j i).1]
  · change ((occupations (net.originalTrace (x.1-x.2))).2 *ᵥ (Pi.single i 1) +
      (occupations (net.originalTrace (x.1-x.2))).1 *ᵥ 0) j = _
    simp only [Matrix.mulVec_zero, add_zero]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, (occupation_kernels _ hw j i).2]

/-- The actual signed affine logit gradient, with no positive-fan-in restriction. -/
theorem strict_affine_output_gradient {n m r} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (x : Vec n) (hx : net.Strict x)
    (hw : NonnegativeWeights (net.originalTrace x)) (u : Fin r) (i : Fin n) :
    fderiv ℝ (Thesis.AffineOutputBackward.affineOutput net C b) x (Pi.single i 1) u =
      ∑ j, C u j * (sgOccupation (net.originalTrace x) j i false -
        sgOccupation (net.originalTrace x) j i true) := by
  rw [(Thesis.AffineOutputBackward.affineOutput_hasFDerivAt net C b x hx).fderiv]
  change (∑ j, C u j * (net.originalTrace x).originalJac (Pi.single i 1) j) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [selected_operator_occupation _ hw j i]

end Thesis.StoppingBoundary
