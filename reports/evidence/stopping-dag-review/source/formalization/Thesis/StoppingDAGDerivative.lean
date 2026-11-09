import Thesis.StoppingExpressionKernel

noncomputable section
namespace Thesis.StoppingDAG
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Matrix
open scoped BigOperators

def combineKernel {d n} (P N : Matrix (Fin n) (Fin d) ℝ) (k : PairVec n) : PairVec d :=
  (k.1 ᵥ* P+k.2 ᵥ* N,k.1 ᵥ* N+k.2 ᵥ* P)

theorem coefficientRow_vecMul {d n} (v : Vec n) (M : Matrix (Fin n) (Fin d) ℝ) (x : Vec d) :
    coefficientRow (v ᵥ* M) x = coefficientRow v (M *ᵥ x) := by
  simp only [coefficientRow_apply]
  exact (Matrix.dotProduct_mulVec v M x).symm

theorem kernelMap_comp_pairMap {d n} (P N : Matrix (Fin n) (Fin d) ℝ) (k : PairVec n) :
    kernelMap (combineKernel P N k) = (kernelMap k).comp (pairMap P N) := by
  apply ContinuousLinearMap.ext
  intro x
  change kernelMap (combineKernel P N k) x = kernelMap k (P *ᵥ x.1 + N *ᵥ x.2, N *ᵥ x.1 + P *ᵥ x.2)
  simp only [combineKernel,kernelMap_apply,coefficientRow_add,
    ContinuousLinearMap.add_apply,coefficientRow_vecMul,map_add]
  apply Prod.ext <;> dsimp only <;> ring

def snocPair {n} (x : PairVec n) (v : ℝ × ℝ) : PairVec (n+1) :=
  (Fin.snoc x.1 v.1,Fin.snoc x.2 v.2)

theorem pairMap_snoc_apply {d n} (P N : Matrix (Fin n) (Fin d) ℝ) (k : PairVec d) (x : PairVec d) :
    pairMap (Fin.snoc P k.1) (Fin.snoc N k.2) x = snocPair (pairMap P N x) (kernelMap k x) := by
  change ((Fin.snoc P k.1) *ᵥ x.1 + (Fin.snoc N k.2) *ᵥ x.2,
      (Fin.snoc N k.2) *ᵥ x.1 + (Fin.snoc P k.1) *ᵥ x.2) = _
  apply Prod.ext <;> funext i <;> refine Fin.lastCases ?_ (fun j => ?_) i
  all_goals
    simp [pairMap,preN,preP_apply,snocPair,kernelMap_apply,Matrix.mulVec,dotProduct,coefficientRow_apply,Fin.snoc]

def dagKernel {d n} : Circuit d n → PairVec d →
    Matrix (Fin n) (Fin d) ℝ × Matrix (Fin n) (Fin d) ℝ
  | .inputs, _ => (1,0)
  | .node prior op, x =>
      let K := dagKernel prior x
      let k := combineKernel K.1 K.2 (expressionKernel op (stoppingCircuit prior x))
      (Fin.snoc K.1 k.1,Fin.snoc K.2 k.2)

/-- Every original recorded node is regular; a pool only checks its winning
subtree, as in ExpressionRegular. This is a concrete forward-pass condition. -/
def CircuitRegular {d n} : Circuit d n → PairVec d → Prop
  | .inputs, _ => True
  | .node prior op, x => CircuitRegular prior x ∧ ExpressionRegular op (stoppingCircuit prior x)

theorem snocPair_hasFDerivAt {d n} (f : PairVec d → PairVec n) (g : PairVec d → ℝ × ℝ)
    (P N : Matrix (Fin n) (Fin d) ℝ) (k : PairVec d) (x : PairVec d)
    (hf : HasFDerivAt f (pairMap P N) x) (hg : HasFDerivAt g (kernelMap k) x) :
    HasFDerivAt (fun y => snocPair (f y) (g y))
      (pairMap (Fin.snoc P k.1) (Fin.snoc N k.2)) x := by
  have hp : HasFDerivAt (fun y => (snocPair (f y) (g y)).1)
      (preP (Fin.snoc P k.1) (Fin.snoc N k.2)) x := by
    apply hasFDerivAt_pi'.mpr
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · convert hg.fst using 1
      · funext y; simp [snocPair]
      · apply ContinuousLinearMap.ext
        intro v
        change (pairMap (Fin.snoc P k.1) (Fin.snoc N k.2) v).1 (Fin.last n)=(kernelMap k v).1
        rw [pairMap_snoc_apply]
        simp [snocPair]
    · convert (ContinuousLinearMap.proj i : Vec n →L[ℝ] ℝ).hasFDerivAt.comp x hf.fst using 1
      · funext y; simp [snocPair]
      · apply ContinuousLinearMap.ext
        intro v
        change (pairMap (Fin.snoc P k.1) (Fin.snoc N k.2) v).1 i.castSucc=(pairMap P N v).1 i
        rw [pairMap_snoc_apply]
        simp [snocPair]
  have hn : HasFDerivAt (fun y => (snocPair (f y) (g y)).2)
      (preN (Fin.snoc P k.1) (Fin.snoc N k.2)) x := by
    apply hasFDerivAt_pi'.mpr
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · convert hg.snd using 1
      · funext y; simp [snocPair]
      · apply ContinuousLinearMap.ext
        intro v
        change (pairMap (Fin.snoc P k.1) (Fin.snoc N k.2) v).2 (Fin.last n)=(kernelMap k v).2
        rw [pairMap_snoc_apply]
        simp [snocPair]
    · convert (ContinuousLinearMap.proj i : Vec n →L[ℝ] ℝ).hasFDerivAt.comp x hf.snd using 1
      · funext y; simp [snocPair]
      · apply ContinuousLinearMap.ext
        intro v
        change (pairMap (Fin.snoc P k.1) (Fin.snoc N k.2) v).2 i.castSucc=(pairMap P N v).2 i
        rw [pairMap_snoc_apply]
        simp [snocPair]
  exact hp.prodMk hn

/-- Actual end-to-end stopping-stream Jacobian on the shared DAG. All earlier
node values are retained, so residual paths and fanout are handled by the same
chain rule rather than by independent copies of a network. -/
theorem stoppingCircuit_hasFDerivAt {d n} (c : Circuit d n) (hc : c.Additive)
    (x : PairVec d) (hx : CircuitRegular c x) :
    HasFDerivAt (stoppingCircuit c) (pairMap (dagKernel c x).1 (dagKernel c x).2) x := by
  induction c with
  | inputs =>
      have he : pairMap (1 : Matrix (Fin d) (Fin d) ℝ) 0=ContinuousLinearMap.id ℝ (PairVec d) := by
        apply ContinuousLinearMap.ext
        intro v
        simp [pairMap,preN,preP_apply]
      change HasFDerivAt id (pairMap 1 0) x
      rw [he]
      exact hasFDerivAt_id x
  | node prior op ih =>
      have hf := ih hc.1 hx.1
      have hg := (stoppingExpr_hasFDerivAt op hc.2 (stoppingCircuit prior x) hx.2).comp x hf
      rw [← kernelMap_comp_pairMap] at hg
      exact snocPair_hasFDerivAt _ _ _ _ _ x hf hg

theorem combineKernel_nonnegative {d n} (P N : Matrix (Fin n) (Fin d) ℝ)
    (hP : ∀ j i,0≤P j i) (hN : ∀ j i,0≤N j i) (k : PairVec n) (hk : 0≤k) :
    0≤combineKernel P N k := by
  have hv (v : Vec n) (M : Matrix (Fin n) (Fin d) ℝ) (hv : 0≤v) (hM : ∀ j i,0≤M j i) : 0≤v ᵥ* M := by
    intro i
    change 0 ≤ ∑ j, v j * M j i
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hv j) (hM j i))
  exact ⟨add_nonneg (hv k.1 P hk.1 hP) (hv k.2 N hk.2 hN),
    add_nonneg (hv k.1 N hk.1 hN) (hv k.2 P hk.2 hP)⟩

theorem dagKernel_nonnegative {d n} (c : Circuit d n) (hc : c.Additive) (x : PairVec d) :
    (∀ j i,0≤(dagKernel c x).1 j i) ∧ (∀ j i,0≤(dagKernel c x).2 j i) := by
  induction c with
  | inputs => constructor <;> intro j i <;> simp [dagKernel,Matrix.one_apply]; split_ifs <;> norm_num
  | node prior op ih =>
      have h := ih hc.1
      have hk := combineKernel_nonnegative _ _ h.1 h.2 _
        (expressionKernel_nonnegative op hc.2 (stoppingCircuit prior x))
      constructor <;> intro j i <;> refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [dagKernel,Fin.snoc] using hk.1 i
      · simpa [dagKernel,Fin.snoc] using h.1 k i
      · simpa [dagKernel,Fin.snoc] using hk.2 i
      · simpa [dagKernel,Fin.snoc] using h.2 k i

end Thesis.StoppingDAG
