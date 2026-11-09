import Thesis.SoftplusCircuitRows

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.Regularization Thesis.StoppingDAG Matrix
open scoped BigOperators

theorem matrixCLM_apply {d n} (M : Matrix (Fin n) (Fin d) ℝ) (v : Vec d) :
    matrixCLM M v=M *ᵥ v := rfl

theorem rowMap_comp {d n} (P N : Matrix (Fin n) (Fin d) ℝ) (k : PairVec n) :
    rowMap (combineKernel P N k)=(rowMap k).comp (matrixCLM (P-N)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [rowMap,combineKernel,coefficientRow_add,_root_.sub_apply,
    _root_.add_apply,ContinuousLinearMap.comp_apply,coefficientRow_vecMul,
    matrixCLM_apply,Matrix.sub_mulVec,map_sub]
  ring

def appendMatrix {d n} (M : Matrix (Fin n) (Fin d) ℝ) (v : Vec d) :
    Matrix (Fin (n+1)) (Fin d) ℝ := fun j i => Fin.snoc (α := fun _ => ℝ) (fun h => M h i) (v i) j

def graphKernel {d n} (θ : ℝ) : (c : Circuit d n) → Plan c → Vec d →
    Matrix (Fin n) (Fin d) ℝ × Matrix (Fin n) (Fin d) ℝ
  | .inputs, _, _ => (1,0)
  | .node prior _, plan, x =>
      let K := graphKernel θ prior plan.1 x
      let k := combineKernel K.1 K.2 (selectedWeights θ plan.2 (graphSoft θ prior plan.1 x))
      (appendMatrix K.1 k.1,appendMatrix K.2 k.2)

theorem matrixCLM_snoc_apply {d n} (P N : Matrix (Fin n) (Fin d) ℝ)
    (k : PairVec d) (v : Vec d) :
    matrixCLM (appendMatrix P k.1-appendMatrix N k.2) v =
      Fin.snoc (matrixCLM (P-N) v) (rowMap k v) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  all_goals simp [matrixCLM,Matrix.toLin'_apply,appendMatrix,Matrix.mulVec,dotProduct,Fin.snoc,rowMap,coefficientRow_apply,
    sub_mul,Finset.sum_sub_distrib]


theorem snoc_hasFDerivAt {d n} (f : Vec d → Vec n) (g : Vec d → ℝ)
    (P N : Matrix (Fin n) (Fin d) ℝ) (k : PairVec d) (x : Vec d)
    (hf : HasFDerivAt f (matrixCLM (P-N)) x) (hg : HasFDerivAt g (rowMap k) x) :
    HasFDerivAt (fun y => Fin.snoc (f y) (g y))
      (matrixCLM (appendMatrix P k.1-appendMatrix N k.2)) x := by
  apply hasFDerivAt_pi'.mpr
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · convert hg using 1
    · funext y; simp
    · apply ContinuousLinearMap.ext
      intro v
      change (matrixCLM (appendMatrix P k.1-appendMatrix N k.2) v) (Fin.last n)=rowMap k v
      rw [matrixCLM_snoc_apply]
      simp

  · convert (ContinuousLinearMap.proj i : Row n).hasFDerivAt.comp x hf using 1
    · funext y; simp
    · apply ContinuousLinearMap.ext
      intro v
      change (matrixCLM (appendMatrix P k.1-appendMatrix N k.2) v) i.castSucc=(matrixCLM (P-N) v) i
      rw [matrixCLM_snoc_apply]
      simp

/-- Actual end-to-end ordinary Softplus DAG derivative, with shared residual
predecessors and unique hard-pool winners. No strict activation gate assumption. -/
theorem graphSoft_hasFDerivAt {d n} (c : Circuit d n) (plan : Plan c)
    (θ : ℝ) (hθ : 0<θ) (x : Vec d) (hx : Regular θ c plan x) :
    HasFDerivAt (graphSoft θ c plan)
      (matrixCLM ((graphKernel θ c plan x).1-(graphKernel θ c plan x).2)) x := by
  induction c with
  | inputs =>
      have he : matrixCLM (1 : Matrix (Fin d) (Fin d) ℝ)=ContinuousLinearMap.id ℝ (Vec d) := by
        apply ContinuousLinearMap.ext
        intro v
        simp [matrixCLM_apply]
      change HasFDerivAt id (matrixCLM (1-0)) x
      rw [sub_zero,he]
      exact hasFDerivAt_id x
  | node prior op ih =>
      have hf := ih plan.1 hx.1
      have hg := (nodeWith_hasFDerivAt θ hθ plan.2 (graphSoft θ prior plan.1 x) hx.2).comp x hf
      rw [← rowMap_comp] at hg
      exact snoc_hasFDerivAt _ _ _ _ _ x hf hg

theorem selectedWeights_nonnegative {n e} (θ : ℝ) (spec : NodeSpec (n := n) e) (x : Vec n) :
    0≤selectedWeights θ spec x := by
  have hk := nodeWeights_nonnegative spec x
  have hg := (continuationProbability_mem θ spec x).1
  exact ⟨fun i => mul_nonneg hg (hk.1 i),fun i => mul_nonneg hg (hk.2 i)⟩

theorem graphKernel_nonnegative {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (x : Vec d) :
    (∀ j i,0≤(graphKernel θ c plan x).1 j i) ∧ (∀ j i,0≤(graphKernel θ c plan x).2 j i) := by
  induction c with
  | inputs => constructor <;> intro j i <;> simp [graphKernel,Matrix.one_apply]; split_ifs <;> norm_num
  | node prior op ih =>
      have hp := ih plan.1
      have hk := combineKernel_nonnegative _ _ hp.1 hp.2 _
        (selectedWeights_nonnegative θ plan.2 (graphSoft θ prior plan.1 x))
      constructor <;> intro j i <;> refine Fin.lastCases ?_ (fun h => ?_) j
      · simpa [graphKernel,appendMatrix,Fin.snoc] using hk.1 i
      · simpa [graphKernel,appendMatrix,Fin.snoc] using hp.1 h i
      · simpa [graphKernel,appendMatrix,Fin.snoc] using hk.2 i
      · simpa [graphKernel,appendMatrix,Fin.snoc] using hp.2 h i

end Thesis.SoftplusCircuit
