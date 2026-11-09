import Thesis.StoppingDAGPayoff

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Matrix
open scoped BigOperators

theorem expressionKernel_sum {n} (es : List (SignedExpr (Fin n))) (x : PairVec n) :
    expressionKernel (SignedExpr.sum es) x=(es.map (fun e => expressionKernel e x)).sum := by
  induction es <;> simp_all [SignedExpr.sum,expressionKernel]

theorem expressionOffset_sum {n} (es : List (SignedExpr (Fin n))) (x : PairVec n) :
    expressionOffset (SignedExpr.sum es) x=(es.map (fun e => expressionOffset e x)).sum := by
  induction es <;> simp_all [SignedExpr.sum,expressionOffset]

/-- On the existing affine syntax, the selected local kernel is exactly the
canonical positive/negative edge split; the affine bias does not enter fan-in. -/
theorem expressionKernel_affine {n} (w : Vec n) (b : ℝ) (x : PairVec n) :
    expressionKernel (SignedExpr.affine w b) x=(fun i => max (w i) 0,fun i => max (-w i) 0) := by
  simp only [SignedExpr.affine,expressionKernel,expressionKernel_sum,List.map_ofFn,List.sum_ofFn]
  apply Prod.ext <;> funext j <;>
    simp [expressionKernel,Prod.fst_sum,Prod.snd_sum,Finset.sum_apply,Pi.single_apply,Function.comp_def]

theorem expressionOffset_affine {n} (w : Vec n) (b : ℝ) (x : PairVec n) :
    expressionOffset (SignedExpr.affine w b) x=(max b 0,max (-b) 0) := by
  simp [SignedExpr.affine,expressionOffset,expressionOffset_sum,List.map_ofFn,List.sum_ofFn,
    scalarSplitMap,Function.comp_def]

theorem ExpressionRegular_affine {n} (w : Vec n) (b : ℝ) (x : PairVec n) :
    ExpressionRegular (SignedExpr.affine w b) x := by
  have hs : ∀ es : List (SignedExpr (Fin n)),
      (∀ e∈es,ExpressionRegular e x) → ExpressionRegular (SignedExpr.sum es) x := by
    intro es
    induction es with
    | nil => intro _; trivial
    | cons e es ih => intro he; exact ⟨he e (by simp),ih (fun a ha => he a (by simp [ha]))⟩
  constructor
  · trivial
  · apply hs
    intro e he
    simp only [List.mem_ofFn] at he
    rcases he with ⟨i,rfl⟩
    trivial

theorem affine_discount {n} (w : Vec n) (b : ℝ) (x : PairVec n) :
    localDiscount (expressionKernel (SignedExpr.affine w b) x)=∑ i,|w i| := by
  rw [expressionKernel_affine]
  exact Finset.sum_congr rfl (fun i _ => (canonical_weight_split (w i)).2)

theorem constant_cemetery {n} (b : ℝ) (x : PairVec n) :
    localDiscount (expressionKernel (.constant b) x)=0 ∧
    localProbability (expressionKernel (.constant b) x) none=1 ∧
    expressionOffset (.constant b) x=(max b 0,max (-b) 0) := by
  simp [expressionKernel,localDiscount,localProbability,expressionOffset]

theorem addition_discount {n} (i j : Fin n) (x : PairVec n) :
    localDiscount (expressionKernel (.add (.input i) (.input j)) x)=2 := by
  norm_num [localDiscount,expressionKernel,Finset.sum_add_distrib,Pi.single_apply]

/-- The source's fair addition oracle pushes forward to the graph predecessor
law. This also handles repeated predecessors by adding their two probabilities. -/
theorem addition_probability {n} (i j k : Fin n) (x : PairVec n) :
    localProbability (expressionKernel (.add (.input i) (.input j)) x) (some (k,false)) =
      additionProbability false*(if k=i then 1 else 0)+
      additionProbability true*(if k=j then 1 else 0) := by
  unfold localProbability
  rw [addition_discount]
  simp [expressionKernel,additionProbability,Pi.single_apply,eq_comm,add_div]
  split_ifs <;> norm_num

theorem pool_kernel {n} (i j : Fin n) (x : PairVec n) :
    expressionKernel (.maximum (.input i) (.input j)) x =
      (Pi.single (if x.1 j-x.2 j<x.1 i-x.2 i then i else j) 1,0) := by
  simp only [expressionKernel,score,SignedExpr.eval,Pi.sub_apply]
  by_cases h : x.1 j-x.2 j<x.1 i-x.2 i <;> simp [h]

theorem pool_discount {n} (i j : Fin n) (x : PairVec n) :
    localDiscount (expressionKernel (.maximum (.input i) (.input j)) x)=1 := by
  rw [pool_kernel]
  simp [localDiscount,Pi.single_apply]

theorem relu_kernel {n} (i : Fin n) (x : PairVec n) :
    expressionKernel (.maximum (.input i) (.constant 0)) x =
      if x.2 i<x.1 i then (Pi.single i 1,0) else (0,0) := by
  simp only [expressionKernel,score,SignedExpr.eval,Pi.sub_apply]
  congr 1
  exact propext (sub_pos)

end Thesis.StoppingDAG
