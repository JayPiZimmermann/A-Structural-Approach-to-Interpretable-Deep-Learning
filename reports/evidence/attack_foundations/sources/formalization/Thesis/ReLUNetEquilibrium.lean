import Thesis.ReLUNetGame

/-! Actual randomized policy evaluation and pure subgame-perfect optimality on
the same varying-width Network as the ReLU forward theorem. -/
noncomputable section
namespace Thesis.ReLUNetGame
open Finset Matrix HiddenMonotonicity

/-- A player's continuation probability at each neuron, with stop probability 1-p.
The player uses this strategy at its own signed states. -/
def Strategy {n m} : Network n m → Type
  | .output _ => Unit
  | .layer (k := k) _ _ _ _ tail => (Fin k → Set.Icc (0 : ℝ) 1) × Strategy tail

def gateProbability (z : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨if 0 < z then 1 else 0, by split_ifs <;> constructor <;> norm_num⟩

/-- Both players use the same pure stopping rule, computed from original preactivations. -/
def optimalStrategy {n m} : (net : Network n m) → (Fin n → ℝ) → Strategy net
  | .output _, _ => ()
  | .layer wp wn bp bn tail, x =>
      (fun i => gateProbability (((wp-wn).mulVec x+(bp-bn)) i),
       optimalStrategy tail (fun i => relu (((wp-wn).mulVec x+(bp-bn)) i)))

/-- Expected payoff under independent randomized actions at every signed state.
Stop pays zero; continuation includes signed bias and discounted transition. -/
def policyValue {n m} : (net : Network n m) → Strategy net → Strategy net →
    (Fin n → ℝ) → (Fin n → ℝ) → (Fin m → ℝ) × (Fin m → ℝ)
  | .output _, _, _, p, q => (p,q)
  | .layer wp wn bp bn tail, plus, minus, p, q =>
      policyValue tail plus.2 minus.2
        (fun i => (plus.1 i).val * continuation wp wn (bp-bn) p q i)
        (fun i => (minus.1 i).val * continuation wn wp (bn-bp) p q i)

theorem gateProbability_pure (z : ℝ) :
    (gateProbability z).val = 0 ∨ (gateProbability z).val = 1 := by
  unfold gateProbability; split_ifs <;> simp

theorem gateProbability_value (z : ℝ) :
    (gateProbability z).val*z = relu z ∧
    (gateProbability z).val*(-z) = -relu z := by
  by_cases h : 0 < z
  · simp [gateProbability,h,relu,max_eq_left h.le]
  · simp [gateProbability,h,relu,max_eq_right (le_of_not_gt h)]

theorem randomized_stop_bounds (z : ℝ) (p : Set.Icc (0 : ℝ) 1) :
    min z 0 ≤ p.val*z ∧ p.val*z ≤ max z 0 := by
  rcases le_total 0 z with hz | hz
  · rw [min_eq_right hz,max_eq_left hz]
    exact ⟨mul_nonneg p.property.1 hz,by nlinarith [p.property.2]⟩
  · rw [min_eq_left hz,max_eq_right hz]
    exact ⟨by nlinarith [p.property.2],mul_nonpos_of_nonneg_of_nonpos p.property.1 hz⟩

theorem continuation_mono {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (b : Fin k → ℝ) (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j)
    (hrow : ∀ i, rowDiscount wp wn i ≠ 0)
    {p q p' q' : Fin n → ℝ} (hp : p ≤ p') (hq : q ≤ q') (i : Fin k) :
    continuation wp wn b p q i ≤ continuation wp wn b p' q' i := by
  rw [continuation_recovery _ _ _ _ _ _ (hrow i),
      continuation_recovery _ _ _ _ _ _ (hrow i)]
  exact add_le_add (add_le_add (positive_matrix_monotone wp hwp hp i)
    (positive_matrix_monotone wn hwn hq i)) le_rfl

theorem continuation_signed {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Fin k → ℝ) (x : Fin n → ℝ) (i : Fin k)
    (hrow : rowDiscount wp wn i ≠ 0) :
    continuation wp wn (bp-bn) x (-x) i = ((wp-wn).mulVec x+(bp-bn)) i ∧
    continuation wn wp (bn-bp) x (-x) i = -(((wp-wn).mulVec x+(bp-bn)) i) := by
  have hn : rowDiscount wn wp i ≠ 0 := by simpa [rowDiscount,add_comm] using hrow
  constructor
  · rw [continuation_recovery _ _ _ _ _ _ hrow,sub_mulVec,mulVec_neg]; rfl
  · rw [continuation_recovery _ _ _ _ _ _ hn]
    simp only [sub_mulVec,mulVec_neg,Pi.add_apply,Pi.sub_apply,Pi.neg_apply]
    ring

/-- With the maximizing player's optimal strategy fixed, any randomized opponent
can only increase both signed-state values. The stronger boundary comparison is
what makes the induction valid across arbitrary widths and depths. -/
theorem optimal_lower_pair {n m} (net : Network n m) (hn : net.Nonnegative)
    (hr : NonzeroRows net) (x p q : Fin n → ℝ) (hp : x ≤ p) (hq : -x ≤ q)
    (minus : Strategy net) :
    net.eval x ≤ (policyValue net (optimalStrategy net x) minus p q).1 ∧
    -net.eval x ≤ (policyValue net (optimalStrategy net x) minus p q).2 := by
  induction net with
  | output n => exact ⟨hp,hq⟩
  | layer wp wn bp bn tail ih =>
      rcases hn with ⟨hwp,hwn,ht⟩
      rcases hr with ⟨hrow,htr⟩
      have hrow' : ∀ i, rowDiscount wn wp i ≠ 0 := by
        intro i; simpa [rowDiscount,add_comm] using hrow i
      apply ih ht htr _ _ _ _ _ minus.2
      · intro i
        have he := (continuation_signed wp wn bp bn x i (hrow i)).1
        have hm := continuation_mono wp wn (bp-bn) hwp hwn hrow hp hq i
        have hg := (gateProbability_value (((wp-wn).mulVec x+(bp-bn)) i)).1
        change relu _ ≤ (gateProbability _).val * continuation wp wn (bp-bn) p q i
        rw [← hg]
        exact mul_le_mul_of_nonneg_left (by rwa [he] at hm) (gateProbability _).property.1
      · intro i
        have he := (continuation_signed wp wn bp bn x i (hrow i)).2
        have hm := continuation_mono wn wp (bn-bp) hwn hwp hrow' hp hq i
        have hb := (randomized_stop_bounds (-(((wp-wn).mulVec x+(bp-bn)) i)) (minus.1 i)).1
        have hmin : min (-(((wp-wn).mulVec x+(bp-bn)) i)) 0 =
            -relu (((wp-wn).mulVec x+(bp-bn)) i) := by
          rcases le_total (((wp-wn).mulVec x+(bp-bn)) i) 0 with hz | hz
          · simp only [relu,max_eq_right hz,min_eq_right (neg_nonneg.mpr hz),neg_zero]
          · simp only [relu,max_eq_left hz,min_eq_left (neg_nonpos.mpr hz)]
        change -relu _ ≤ (minus.1 i).val * continuation wn wp (bn-bp) p q i
        rw [hmin] at hb
        exact hb.trans (mul_le_mul_of_nonneg_left (by rwa [he] at hm) (minus.1 i).property.1)

/-- With the minimizing player's pure optimal strategy fixed, arbitrary maximizing
randomization can only decrease either signed-state value. -/
theorem optimal_upper_pair {n m} (net : Network n m) (hn : net.Nonnegative)
    (hr : NonzeroRows net) (x p q : Fin n → ℝ) (hp : p ≤ x) (hq : q ≤ -x)
    (plus : Strategy net) :
    (policyValue net plus (optimalStrategy net x) p q).1 ≤ net.eval x ∧
    (policyValue net plus (optimalStrategy net x) p q).2 ≤ -net.eval x := by
  induction net with
  | output n => exact ⟨hp,hq⟩
  | layer wp wn bp bn tail ih =>
      rcases hn with ⟨hwp,hwn,ht⟩
      rcases hr with ⟨hrow,htr⟩
      have hrow' : ∀ i, rowDiscount wn wp i ≠ 0 := by
        intro i; simpa [rowDiscount,add_comm] using hrow i
      apply ih ht htr _ _ _ _ _ plus.2
      · intro i
        have he := (continuation_signed wp wn bp bn x i (hrow i)).1
        have hm := continuation_mono wp wn (bp-bn) hwp hwn hrow hp hq i
        have hb := (randomized_stop_bounds (((wp-wn).mulVec x+(bp-bn)) i) (plus.1 i)).2
        change (plus.1 i).val * continuation wp wn (bp-bn) p q i ≤ relu _
        exact (mul_le_mul_of_nonneg_left (by rwa [he] at hm) (plus.1 i).property.1).trans hb
      · intro i
        have he := (continuation_signed wp wn bp bn x i (hrow i)).2
        have hm := continuation_mono wn wp (bn-bp) hwn hwp hrow' hp hq i
        have hg := (gateProbability_value (((wp-wn).mulVec x+(bp-bn)) i)).2
        change (gateProbability _).val * continuation wn wp (bn-bp) p q i ≤ -relu _
        rw [← hg]
        exact mul_le_mul_of_nonneg_left (by rwa [he] at hm) (gateProbability _).property.1

/-- Full thm:relu_net_game_value: the common pure gate strategy is a saddle
against every randomized strategy; its actual expected payoff equals the forward
network at plus states and its negative at mirrored states. Applies to every prefix,
hence to every subgame of the feedforward graph. -/
theorem relu_net_game_equilibrium {n m} (net : Network n m) (hn : net.Nonnegative)
    (hr : NonzeroRows net) (x : Fin n → ℝ) (plus minus : Strategy net) :
    (policyValue net plus (optimalStrategy net x) x (-x)).1 ≤ net.eval x ∧
    (policyValue net plus (optimalStrategy net x) x (-x)).2 ≤ -net.eval x ∧
    policyValue net (optimalStrategy net x) (optimalStrategy net x) x (-x) =
      (net.eval x,-net.eval x) ∧
    net.eval x ≤ (policyValue net (optimalStrategy net x) minus x (-x)).1 ∧
    -net.eval x ≤ (policyValue net (optimalStrategy net x) minus x (-x)).2 := by
  have hl := optimal_lower_pair net hn hr x x (-x) le_rfl le_rfl minus
  have hu := optimal_upper_pair net hn hr x x (-x) le_rfl le_rfl plus
  have hl' := optimal_lower_pair net hn hr x x (-x) le_rfl le_rfl (optimalStrategy net x)
  have hu' := optimal_upper_pair net hn hr x x (-x) le_rfl le_rfl (optimalStrategy net x)
  refine ⟨hu.1,hu.2,?_,hl.1,hl.2⟩
  exact Prod.ext (le_antisymm hu'.1 hl'.1) (le_antisymm hu'.2 hl'.2)

/-- The source theorem with its forced affine output state: actual policy payoffs
satisfy the saddle inequalities around the original signed affine logit. -/
theorem relu_net_game_affine_equilibrium {n m k} (net : Network n m)
    (hn : net.Nonnegative) (hr : NonzeroRows net) (x : Fin n → ℝ)
    (plus minus : Strategy net) (wp wn : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j)
    (hrow : ∀ i, rowDiscount wp wn i ≠ 0) (i : Fin k) :
    let read := fun v : (Fin m → ℝ) × (Fin m → ℝ) => continuation wp wn b v.1 v.2 i
    let logit := ((wp-wn).mulVec (net.eval x)+b) i
    read (policyValue net plus (optimalStrategy net x) x (-x)) ≤ logit ∧
    read (policyValue net (optimalStrategy net x) (optimalStrategy net x) x (-x)) = logit ∧
    logit ≤ read (policyValue net (optimalStrategy net x) minus x (-x)) := by
  dsimp only
  have hs := relu_net_game_equilibrium net hn hr x plus minus
  have hread : continuation wp wn b (net.eval x) (-net.eval x) i =
      ((wp-wn).mulVec (net.eval x)+b) i := by
    rw [continuation_recovery _ _ _ _ _ _ (hrow i),sub_mulVec,mulVec_neg]
    rfl
  refine ⟨?_,?_,?_⟩
  · rw [← hread]
    exact continuation_mono wp wn b hwp hwn hrow hs.1 hs.2.1 i
  · rw [hs.2.2.1]
    exact hread
  · rw [← hread]
    exact continuation_mono wp wn b hwp hwn hrow hs.2.2.2.1 hs.2.2.2.2 i

end Thesis.ReLUNetGame
