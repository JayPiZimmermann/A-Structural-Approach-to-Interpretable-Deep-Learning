import Thesis.StoppingRegions
import HiddenMonotonicity.PoolingCircuit

noncomputable section
namespace Thesis.StoppingCircuit
open HiddenMonotonicity Thesis.StoppingDecomposition

/-- The stopping/WTA expression pass. At max(a,0) a tie chooses the zero branch,
so this is exactly stopPair; general pools forward one shared winning pair. -/
def stoppingExpr {n} : SignedExpr (Fin n) → PairVec n → ℝ × ℝ
  | .input i, x => (x.1 i,x.2 i)
  | .constant c, _ => (max c 0,max (-c) 0)
  | .add a b, x => stoppingExpr a x + stoppingExpr b x
  | .scale c a, x =>
      (max c 0*(stoppingExpr a x).1+max (-c) 0*(stoppingExpr a x).2,
       max c 0*(stoppingExpr a x).2+max (-c) 0*(stoppingExpr a x).1)
  | .mul a b, x =>
      ((stoppingExpr a x).1*(stoppingExpr b x).1+(stoppingExpr a x).2*(stoppingExpr b x).2,
       (stoppingExpr a x).1*(stoppingExpr b x).2+(stoppingExpr a x).2*(stoppingExpr b x).1)
  | .maximum a b, x => winnerPair (stoppingExpr b x) (stoppingExpr a x)

theorem stoppingExpr_recovery {n} (e : SignedExpr (Fin n)) (x : PairVec n) :
    (stoppingExpr e x).1-(stoppingExpr e x).2 = e.eval (x.1-x.2) := by
  induction e with
  | input i => rfl
  | constant c => exact (canonical_weight_split c).1
  | add a b ha hb =>
      simp only [stoppingExpr,SignedExpr.eval,Prod.fst_add,Prod.snd_add]
      linarith
  | scale c a ha =>
      simp only [stoppingExpr,SignedExpr.eval]
      calc
        _ = (max c 0-max (-c) 0)*((stoppingExpr a x).1-(stoppingExpr a x).2) := by ring
        _ = _ := by rw [(canonical_weight_split c).1,ha]
  | mul a b ha hb =>
      simp only [stoppingExpr,SignedExpr.eval]
      rw [multiplicative_split_correct,ha,hb]
  | maximum a b ha hb =>
      simp only [stoppingExpr,winnerPair_recovery,SignedExpr.eval,ha,hb,max_comm]

theorem stoppingExpr_nonnegative {n} (e : SignedExpr (Fin n)) (x : PairVec n) (hx : 0≤x) :
    0≤stoppingExpr e x := by
  induction e with
  | input i => exact ⟨hx.1 i,hx.2 i⟩
  | constant c => exact ⟨le_max_right _ _,le_max_right _ _⟩
  | add a b ha hb => exact ⟨add_nonneg ha.1 hb.1,add_nonneg ha.2 hb.2⟩
  | scale c a ha => exact ⟨add_nonneg (mul_nonneg (le_max_right _ _) ha.1)
        (mul_nonneg (le_max_right _ _) ha.2),
      add_nonneg (mul_nonneg (le_max_right _ _) ha.2) (mul_nonneg (le_max_right _ _) ha.1)⟩
  | mul a b ha hb => exact ⟨add_nonneg (mul_nonneg ha.1 hb.1) (mul_nonneg ha.2 hb.2),
      add_nonneg (mul_nonneg ha.1 hb.2) (mul_nonneg ha.2 hb.1)⟩
  | maximum a b ha hb => exact winnerPair_nonnegative _ _ hb ha

/-- Explicit bridge from the graph's ReLU representation to the thesis stopPair. -/
theorem stoppingExpr_relu {n} (a : SignedExpr (Fin n)) (x : PairVec n) :
    stoppingExpr (.maximum a (.constant 0)) x = stopPair (stoppingExpr a x) := by
  simp only [stoppingExpr,neg_zero,max_self]
  unfold winnerPair stopPair
  by_cases h : (stoppingExpr a x).2 < (stoppingExpr a x).1
  · have hn : ¬ (stoppingExpr a x).1-(stoppingExpr a x).2≤0-0 := by linarith
    simp [h,hn]
  · have hn : (stoppingExpr a x).1-(stoppingExpr a x).2≤0-0 := by linarith
    simp [h,hn]

/-- Actual stopping decomposition on the existing shared computation DAG.
Every outgoing branch reads the same earlier-node stream values. -/
def stoppingCircuit {d n} : Circuit d n → PairVec d → PairVec n
  | .inputs, x => x
  | .node prior op, x =>
      let s := stoppingCircuit prior x
      let out := stoppingExpr op s
      (Fin.snoc s.1 out.1,Fin.snoc s.2 out.2)

theorem stoppingCircuit_recovery {d n} (c : Circuit d n) (x : PairVec d) :
    (stoppingCircuit c x).1-(stoppingCircuit c x).2 = c.eval (x.1-x.2) := by
  induction c with
  | inputs => rfl
  | node prior op ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [stoppingCircuit,Circuit.eval,Fin.snoc_last,Pi.sub_apply]
        rw [stoppingExpr_recovery,ih]
      · simpa only [stoppingCircuit,Circuit.eval,Fin.snoc_castSucc,Pi.sub_apply] using congrFun ih j

theorem stoppingCircuit_nonnegative {d n} (c : Circuit d n) (x : PairVec d) (hx : 0≤x) :
    0≤stoppingCircuit c x := by
  induction c with
  | inputs => exact hx
  | node prior op ih =>
      have h := stoppingExpr_nonnegative op _ ih
      constructor <;> intro i <;> refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [stoppingCircuit,Fin.snoc_last,Prod.fst_zero,Pi.zero_apply] using h.1
      · simpa only [stoppingCircuit,Fin.snoc_castSucc,Prod.fst_zero,Pi.zero_apply] using ih.1 j
      · simpa only [stoppingCircuit,Fin.snoc_last,Prod.snd_zero,Pi.zero_apply] using h.2
      · simpa only [stoppingCircuit,Fin.snoc_castSucc,Prod.snd_zero,Pi.zero_apply] using ih.2 j

/-- The addition oracle is an actual normalized two-successor probability law. -/
def additionProbability (_ : Bool) : ℝ := 1/2

theorem addition_probability_law :
    (∀ b, 0≤additionProbability b) ∧ (∑ b : Bool, additionProbability b)=1 := by
  norm_num [additionProbability,Fintype.sum_bool]

/-- Discount 2 cancels the oracle's half probability at each operand. -/
theorem addition_discounted_occupation (left right : ℝ) :
    2*(additionProbability false*left+additionProbability true*right)=left+right := by
  simp only [additionProbability]
  ring

/-- Actual local addition derivative with the oracle's probabilities/discount. -/
theorem addition_derivative_occupation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (Df Dg : E →L[ℝ] ℝ) (x : E)
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x) :
    HasFDerivAt (fun y => f y+g y)
      ((2 : ℝ) • (additionProbability false • Df+additionProbability true • Dg)) x := by
  have he : (2 : ℝ) • (additionProbability false • Df+additionProbability true • Dg) = Df+Dg := by
    ext v
    simp only [additionProbability,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,smul_eq_mul]
    ring
  rw [he]
  exact hf.add hg

/-- Actual WTA derivative on an open unique-winner cell. The same selected
argument is used for both streams; no derivative is claimed at pooling ties. -/
theorem winner_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ × ℝ) (Df Dg : E →L[ℝ] ℝ × ℝ) (x : E)
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
    (hne : (f x).1-(f x).2 ≠ (g x).1-(g x).2) :
    HasFDerivAt (fun y => winnerPair (g y) (f y))
      (if (g x).1-(g x).2 < (f x).1-(f x).2 then Df else Dg) x := by
  have hfc := hf.continuousAt.fst.sub hf.continuousAt.snd
  have hgc := hg.continuousAt.fst.sub hg.continuousAt.snd
  by_cases h : (g x).1-(g x).2 < (f x).1-(f x).2
  · simp only [h,ite_true]
    apply hf.congr_of_eventuallyEq
    filter_upwards [hgc.eventually_lt hfc h] with y hy
    change (g y).1-(g y).2 < (f y).1-(f y).2 at hy
    simp only [winnerPair,if_neg (not_le_of_gt hy)]
  · simp only [h,ite_false]
    have hlt : (f x).1-(f x).2 < (g x).1-(g x).2 := lt_of_le_of_ne (le_of_not_gt h) hne
    apply hg.congr_of_eventuallyEq
    filter_upwards [hfc.eventually_lt hgc hlt] with y hy
    change (f y).1-(f y).2 < (g y).1-(g y).2 at hy
    simp only [winnerPair,if_pos hy.le]

/-- A maxpool oracle follows exactly one selected successor, with unit discount. -/
def winnerProbability (leftWins selectedLeft : Bool) : ℝ := if selectedLeft=leftWins then 1 else 0

theorem winner_probability_law (leftWins : Bool) :
    (∀ b,0≤winnerProbability leftWins b) ∧ (∑ b : Bool,winnerProbability leftWins b)=1 := by
  cases leftWins <;> norm_num [winnerProbability,Fintype.sum_bool]

theorem winner_discounted_occupation (leftWins : Bool) (left right : ℝ) :
    (1 : ℝ)*(winnerProbability leftWins true*left+winnerProbability leftWins false*right) =
      if leftWins then left else right := by
  cases leftWins <;> simp [winnerProbability]

/-- The actual WTA differential is the normalized deterministic pooling
occupation pullback, with its unit discount and the same computed winner. -/
theorem winner_derivative_occupation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ × ℝ) (Df Dg : E →L[ℝ] ℝ × ℝ) (x : E)
    (hf : HasFDerivAt f Df x) (hg : HasFDerivAt g Dg x)
    (hne : (f x).1-(f x).2 ≠ (g x).1-(g x).2) :
    HasFDerivAt (fun y => winnerPair (g y) (f y))
      ((1 : ℝ) •
        (winnerProbability (decide ((g x).1-(g x).2 < (f x).1-(f x).2)) true • Df +
         winnerProbability (decide ((g x).1-(g x).2 < (f x).1-(f x).2)) false • Dg)) x := by
  have hd := winner_derivative f g Df Dg x hf hg hne
  by_cases h : (g x).1-(g x).2 < (f x).1-(f x).2 <;>
    simpa [winnerProbability,h] using hd

end Thesis.StoppingCircuit
