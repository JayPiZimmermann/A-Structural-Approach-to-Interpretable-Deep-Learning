import Thesis.StoppingCircuit

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit
open scoped BigOperators

def score {n} (e : SignedExpr (Fin n)) (x : PairVec n) : ℝ := e.eval (x.1-x.2)

theorem score_continuous {n} (e : SignedExpr (Fin n)) : Continuous (score e) := by
  have he : Continuous e.eval := by
    induction e with
    | input i => exact continuous_apply i
    | constant c => exact continuous_const
    | add a b ha hb => exact ha.add hb
    | scale c a ha => exact continuous_const.mul ha
    | mul a b ha hb => exact ha.mul hb
    | maximum a b ha hb => exact ha.max hb
  exact he.comp (continuous_fst.sub continuous_snd)

/-- Local signed edge coefficients computed from the actual expression and its
selected maxima. Products are outside the additive theorem's scope. -/
def expressionKernel {n} : SignedExpr (Fin n) → PairVec n → PairVec n
  | .input i, _ => (Pi.single i 1,0)
  | .constant _, _ => (0,0)
  | .add a b, x => expressionKernel a x + expressionKernel b x
  | .scale c a, x =>
      (max c 0 • (expressionKernel a x).1 + max (-c) 0 • (expressionKernel a x).2,
       max c 0 • (expressionKernel a x).2 + max (-c) 0 • (expressionKernel a x).1)
  | .mul _ _, _ => (0,0)
  | .maximum a b, x => if score b x < score a x then expressionKernel a x else expressionKernel b x

/-- Only the selected subtree must be regular inside a pool. Strict comparisons
on irrelevant losing subtrees are not assumed. -/
def ExpressionRegular {n} : SignedExpr (Fin n) → PairVec n → Prop
  | .input _, _ => True
  | .constant _, _ => True
  | .add a b, x => ExpressionRegular a x ∧ ExpressionRegular b x
  | .scale _ a, x => ExpressionRegular a x
  | .mul _ _, _ => False
  | .maximum a b, x => score a x ≠ score b x ∧
      (if score b x < score a x then ExpressionRegular a x else ExpressionRegular b x)

def kernelMap {n} (k : PairVec n) : PairVec n →L[ℝ] ℝ × ℝ :=
  (assemble (coefficientRow k.1,coefficientRow k.2)).prod
    (assemble (coefficientRow k.2,coefficientRow k.1))

theorem coefficientRow_add {n} (p q : Vec n) : coefficientRow (p+q)=coefficientRow p+coefficientRow q := by
  simp only [coefficientRow,Pi.add_apply,add_smul,Finset.sum_add_distrib]

theorem coefficientRow_smul {n} (c : ℝ) (p : Vec n) : coefficientRow (c • p)=c • coefficientRow p := by
  simp only [coefficientRow,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

theorem coefficientRow_zero {n} : coefficientRow (0 : Vec n)=0 := by simp [coefficientRow]

theorem coefficientRow_single {n} (i : Fin n) : coefficientRow (Pi.single i 1)=ContinuousLinearMap.proj i := by
  ext x
  simp [coefficientRow_apply,Pi.single_apply]

theorem kernelMap_apply {n} (k x : PairVec n) :
    kernelMap k x = (coefficientRow k.1 x.1+coefficientRow k.2 x.2,
      coefficientRow k.2 x.1+coefficientRow k.1 x.2) := rfl

theorem kernelMap_add {n} (k l : PairVec n) : kernelMap (k+l)=kernelMap k+kernelMap l := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [kernelMap_apply,Prod.fst_add,Prod.snd_add,coefficientRow_add,
    ContinuousLinearMap.add_apply,Prod.mk_add_mk]
  apply Prod.ext <;> dsimp only <;> ring

theorem kernelMap_zero {n} : kernelMap (0 : PairVec n)=0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp [kernelMap_apply,coefficientRow_zero]

def scalarSplitMap (c : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (max c 0 • ContinuousLinearMap.fst ℝ ℝ ℝ + max (-c) 0 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (max c 0 • ContinuousLinearMap.snd ℝ ℝ ℝ + max (-c) 0 • ContinuousLinearMap.fst ℝ ℝ ℝ)

theorem kernelMap_scale {n} (c : ℝ) (k : PairVec n) :
    kernelMap (max c 0 • k.1+max (-c) 0 • k.2,max c 0 • k.2+max (-c) 0 • k.1) =
      (scalarSplitMap c).comp (kernelMap k) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [kernelMap_apply,coefficientRow_add,coefficientRow_smul,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply]
  apply Prod.ext <;> simp [scalarSplitMap,kernelMap_apply] <;> ring

theorem stoppingExpr_maximum {n} (a b : SignedExpr (Fin n)) (x : PairVec n) :
    stoppingExpr (.maximum a b) x = if score b x < score a x then stoppingExpr a x else stoppingExpr b x := by
  simp only [stoppingExpr,winnerPair,stoppingExpr_recovery,score]
  by_cases h : b.eval (x.1-x.2)<a.eval (x.1-x.2)
  · simp [h,not_le_of_gt h]
  · simp [h,le_of_not_gt h]

theorem expressionKernel_nonnegative {n} (e : SignedExpr (Fin n)) (he : e.Additive) (x : PairVec n) :
    0≤expressionKernel e x := by
  induction e with
  | input i =>
      constructor
      · intro j
        change (0 : ℝ) ≤ (Pi.single i 1 : Vec n) j
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · intro j
        exact le_rfl
  | constant c => exact le_rfl
  | add a b ha hb => exact ⟨add_nonneg (ha he.1).1 (hb he.2).1,add_nonneg (ha he.1).2 (hb he.2).2⟩
  | scale c a ha =>
      have h := ha he
      constructor <;> intro i
      · exact add_nonneg (mul_nonneg (le_max_right _ _) (h.1 i)) (mul_nonneg (le_max_right _ _) (h.2 i))
      · exact add_nonneg (mul_nonneg (le_max_right _ _) (h.2 i)) (mul_nonneg (le_max_right _ _) (h.1 i))
  | mul a b ha hb => exact False.elim he
  | maximum a b ha hb =>
      simp only [expressionKernel]
      split_ifs
      · exact ha he.1
      · exact hb he.2

/-- Actual local stopping/WTA derivative, computed from expression coefficients.
The only regularity hypothesis is the explicitly selected strict-cell condition. -/
theorem stoppingExpr_hasFDerivAt {n} (e : SignedExpr (Fin n)) (he : e.Additive)
    (x : PairVec n) (hx : ExpressionRegular e x) :
    HasFDerivAt (stoppingExpr e) (kernelMap (expressionKernel e x)) x := by
  induction e with
  | input i =>
      have h := (kernelMap (Pi.single i 1,0)).hasFDerivAt (x := x)
      convert h using 1
      · funext y
        simp [stoppingExpr,kernelMap_apply,coefficientRow_single,coefficientRow_zero]
      · rfl
  | constant c =>
      change HasFDerivAt (fun _ : PairVec n => (max c 0,max (-c) 0)) (kernelMap (0 : PairVec n)) x
      rw [kernelMap_zero]
      exact hasFDerivAt_const _ x
  | add a b ha hb =>
      rw [show expressionKernel (.add a b) x=expressionKernel a x+expressionKernel b x from rfl,kernelMap_add]
      exact (ha he.1 hx.1).add (hb he.2 hx.2)
  | scale c a ha =>
      rw [show expressionKernel (.scale c a) x =
        (max c 0 • (expressionKernel a x).1+max (-c) 0 • (expressionKernel a x).2,
         max c 0 • (expressionKernel a x).2+max (-c) 0 • (expressionKernel a x).1) from rfl,
        kernelMap_scale]
      have h := (scalarSplitMap c).hasFDerivAt.comp x (ha he hx)
      simpa [stoppingExpr,scalarSplitMap,Function.comp_def] using h
  | mul a b ha hb => exact False.elim he
  | maximum a b ha hb =>
      by_cases h : score b x<score a x
      · simp only [expressionKernel,h,ite_true]
        apply (ha he.1 (by simpa only [ExpressionRegular,h,ite_true] using hx.2)).congr_of_eventuallyEq
        filter_upwards [(score_continuous b).continuousAt.eventually_lt (score_continuous a).continuousAt h] with y hy
        rw [stoppingExpr_maximum,if_pos hy]
      · simp only [expressionKernel,h,ite_false]
        have ht : score a x<score b x := lt_of_le_of_ne (le_of_not_gt h) hx.1
        apply (hb he.2 (by simpa only [ExpressionRegular,h,ite_false] using hx.2)).congr_of_eventuallyEq
        filter_upwards [(score_continuous a).continuousAt.eventually_lt (score_continuous b).continuousAt ht] with y hy
        rw [stoppingExpr_maximum,if_neg (not_lt_of_ge hy.le)]

end Thesis.StoppingDAG
