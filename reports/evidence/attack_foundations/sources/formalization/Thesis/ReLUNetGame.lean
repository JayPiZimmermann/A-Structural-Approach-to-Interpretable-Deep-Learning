import Thesis.Foundations
import Thesis.LayeredGames

/-! The signed stopping game of Gaubert--Vlassopoulos on the shared Network.
The continuation operator explicitly uses normalized split weights and structural
discounts; the forward identity is proved through every layer. -/
noncomputable section
namespace Thesis.ReLUNetGame
open Finset Matrix HiddenMonotonicity

def rowDiscount {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (i : Fin k) : ℝ :=
  ∑ j, (wp i j + wn i j)

def NonzeroRows {n m} : Network n m → Prop
  | .output _ => True
  | .layer wp wn _ _ tail => (∀ i, rowDiscount wp wn i ≠ 0) ∧ NonzeroRows tail

/-- The two successor signs are kept separate. -/
def kernel {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (i : Fin k) (turn : Bool) (j : Fin n) (nextTurn : Bool) : ℝ :=
  (if turn = nextTurn then wp i j else wn i j) / rowDiscount wp wn i

theorem kernel_nonnegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hp : ∀ i j, 0 ≤ wp i j) (hn : ∀ i j, 0 ≤ wn i j)
    (i : Fin k) (turn : Bool) (j : Fin n) (nextTurn : Bool) :
    0 ≤ kernel wp wn i turn j nextTurn := by
  apply div_nonneg
  · split_ifs <;> first | exact hp i j | exact hn i j
  · exact sum_nonneg fun j _ => add_nonneg (hp i j) (hn i j)

theorem kernel_normalized {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (i : Fin k) (h : rowDiscount wp wn i ≠ 0) (turn : Bool) :
    (∑ j, ∑ nextTurn : Bool, kernel wp wn i turn j nextTurn) = 1 := by
  cases turn <;> simp only [kernel, Fintype.sum_bool, Bool.true_eq_false,
    Bool.false_eq_true, not_false_eq_true, ite_false, ite_true]
  · simp_rw [← add_div]
    rw [← sum_div]
    simpa [rowDiscount,add_comm] using div_self h
  · simp_rw [← add_div]
    rw [← sum_div]
    exact div_self h

/-- Signed continuation reward after discounting the normalized transition. -/
def continuation {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (b : Fin k → ℝ) (p q : Fin n → ℝ) (i : Fin k) : ℝ :=
  b i + rowDiscount wp wn i *
    ∑ j, (wp i j / rowDiscount wp wn i * p j + wn i j / rowDiscount wp wn i * q j)

theorem continuation_recovery {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (b : Fin k → ℝ) (p q : Fin n → ℝ) (i : Fin k)
    (h : rowDiscount wp wn i ≠ 0) :
    continuation wp wn b p q i = ((wp.mulVec p + wn.mulVec q) + b) i := by
  unfold continuation
  rw [mul_sum]
  have hs : ∀ j, rowDiscount wp wn i *
      (wp i j / rowDiscount wp wn i * p j + wn i j / rowDiscount wp wn i * q j) =
      wp i j * p j + wn i j * q j := by
    intro j
    field_simp
  simp only [hs, sum_add_distrib, Matrix.mulVec, dotProduct, Pi.add_apply]
  ring

/-- Bellman backward induction, displayed in the network's forward layer order.
The negative-turn player minimizes, so its stopping operator is min rather than max. -/
def signedValue {n m} : Network n m → (Fin n → ℝ) → (Fin n → ℝ) →
    (Fin m → ℝ) × (Fin m → ℝ)
  | .output _, p, q => (p,q)
  | .layer wp wn bp bn tail, p, q =>
      signedValue tail
        (fun i => max (continuation wp wn (bp-bn) p q i) 0)
        (fun i => min (continuation wn wp (bn-bp) p q i) 0)

theorem signed_layer {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Fin k → ℝ) (x : Fin n → ℝ)
    (h : ∀ i, rowDiscount wp wn i ≠ 0) :
    (fun i => max (continuation wp wn (bp-bn) x (-x) i) 0) =
      (fun i => relu (((wp-wn).mulVec x+(bp-bn)) i)) ∧
    (fun i => min (continuation wn wp (bn-bp) x (-x) i) 0) =
      -(fun i => relu (((wp-wn).mulVec x+(bp-bn)) i)) := by
  have hn : ∀ i, rowDiscount wn wp i ≠ 0 := by
    intro i
    simpa [rowDiscount, add_comm] using h i
  have hp : ∀ i, continuation wp wn (bp-bn) x (-x) i =
      ((wp-wn).mulVec x+(bp-bn)) i := by
    intro i
    rw [continuation_recovery _ _ _ _ _ _ (h i)]
    rw [sub_mulVec, mulVec_neg]
    rfl
  have hm : ∀ i, continuation wn wp (bn-bp) x (-x) i =
      -(((wp-wn).mulVec x+(bp-bn)) i) := by
    intro i
    rw [continuation_recovery _ _ _ _ _ _ (hn i)]
    simp only [mulVec_neg, sub_mulVec, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  constructor
  · funext i; rw [hp]; rfl
  · funext i
    rw [hm]
    simp only [relu, Pi.neg_apply]
    rcases le_total (((wp-wn).mulVec x+(bp-bn)) i) 0 with hz | hz
    · rw [max_eq_right hz, min_eq_right (neg_nonneg.mpr hz), neg_zero]
    · rw [max_eq_left hz, min_eq_left (neg_nonpos.mpr hz)]

/-- thm:relu_net_game_value / eq:rng_value_identity at all activation states of
an arbitrary varying-width network, with all bias terms and discounts retained. -/
theorem signedValue_eq_network {n m} (net : Network n m) (h : NonzeroRows net)
    (x : Fin n → ℝ) : signedValue net x (-x) = (net.eval x,-net.eval x) := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [signedValue, Network.eval]
      rw [(signed_layer wp wn bp bn x h.1).1, (signed_layer wp wn bp bn x h.1).2]
      exact ih h.2 _

/-- The final output state has forced continuation, hence an affine value. -/
theorem affine_output_value {n m k} (net : Network n m) (h : NonzeroRows net)
    (x : Fin n → ℝ) (wp wn : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ)
    (hrow : ∀ i, rowDiscount wp wn i ≠ 0) (i : Fin k) :
    continuation wp wn b (signedValue net x (-x)).1 (signedValue net x (-x)).2 i =
      ((wp-wn).mulVec (net.eval x)+b) i := by
  rw [signedValue_eq_network net h x, continuation_recovery _ _ _ _ _ _ (hrow i)]
  rw [sub_mulVec, mulVec_neg]
  rfl

/-- Both players continue exactly at positive preactivations; ties stop. -/
theorem common_stopping_rule (z : ℝ) :
    (if 0 < z then z else 0) = max z 0 ∧
    (if 0 < z then -z else 0) = min (-z) 0 := by
  by_cases h : 0 < z
  · simp [h, max_eq_left h.le, min_eq_left (neg_nonpos.mpr h.le)]
  · have hz : z ≤ 0 := le_of_not_gt h
    simp [h, max_eq_right hz, min_eq_right (neg_nonneg.mpr hz)]

/-- Strict positive/negative preactivations uniquely determine the optimal action. -/
theorem maximizing_action_characterization (z : ℝ) (cont : Bool) :
    (if cont then z else 0) = max z 0 ↔
      (cont = true → 0 ≤ z) ∧ (cont = false → z ≤ 0) := by
  cases cont <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ite_true,
    ite_false, false_implies, true_implies, and_true, true_and]
  · constructor
    · intro h; have := le_max_left z 0; linarith
    · intro h; exact (max_eq_right h).symm
  · constructor
    · intro h; have := le_max_right z 0; linarith
    · intro h; exact (max_eq_left h).symm

end Thesis.ReLUNetGame
