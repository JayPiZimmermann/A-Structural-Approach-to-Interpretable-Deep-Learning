import HiddenMonotonicity.MaxoutProductSize
noncomputable section
open HiddenMonotonicity Matrix

-- Actual empty product and degree zero are nonvacuous, including dimension zero.
def emptyProduct : MaxoutProductGate 0 := .monomial 0 Fin.elim0 Fin.elim0
example : emptyProduct.totalDegree=0 := by simp [emptyProduct,MaxoutProductGate.totalDegree]
example : emptyProduct.expandedTerms=1 := by simp [emptyProduct,MaxoutProductGate.expandedTerms]
example : emptyProduct.eval 0=1 := by simp [emptyProduct,MaxoutProductGate.eval]
def emptyGraph : MaxoutProductDAG 0 1 := .node .inputs emptyProduct
example : emptyGraph.BoundedRankDegree 1 0 := by
  simp [emptyGraph,emptyProduct,MaxoutProductDAG.BoundedRankDegree,MaxoutProductGate.rank,MaxoutProductGate.totalDegree]
example : emptyGraph.compile.graphSize=2 := by
  norm_num [emptyGraph,emptyProduct,MaxoutProductDAG.compile,MaxoutProductDAG.toCircuit,
    MaxoutProductGate.toExpr,repeatedParents,productInputs,Circuit.compileSplitDAG,SignedExpr.split,
    SplitDAG.graphSize,SplitDAG.vertices,SplitDAG.arcs,PositiveExpr.vertices,PositiveExpr.arcs]

-- Literal local-tree vertices plus arcs, with two retained shared input vertices.
def squareGate : MaxoutProductGate 1 := .monomial 1 (fun _ => 0) (fun _ => 2)
def squareGraph : MaxoutProductDAG 1 2 := .node .inputs squareGate
example : squareGraph.graphSize=3 := rfl
example : squareGraph.BoundedRankDegree 1 2 := by
  simp [squareGraph,squareGate,MaxoutProductDAG.BoundedRankDegree,MaxoutProductGate.rank,MaxoutProductGate.totalDegree]
example : squareGraph.compile.graphSize=88 := by
  norm_num [squareGraph,squareGate,MaxoutProductDAG.compile,MaxoutProductDAG.toCircuit,
    MaxoutProductGate.toExpr,repeatedParents,productInputs,Circuit.compileSplitDAG,SignedExpr.split,
    SplitDAG.graphSize,SplitDAG.vertices,SplitDAG.arcs,PositiveExpr.vertices,PositiveExpr.arcs,
    List.ofFn_succ]
example : squareGate.eval (fun _ => -3)=9 := by
  norm_num [squareGate,MaxoutProductGate.eval]

-- Zero-fan-in biased maxout preserves negative maxima, not accidental padding by zero.
def negativeBiasPool : MaxoutProductGate 0 :=
  .maxout 0 1 Fin.elim0 (fun _ => Fin.elim0) ![-3,-5]
example : negativeBiasPool.eval 0=(-3 : ℝ) := by
  apply le_antisymm
  · apply Thesis.Tropical.finiteMax_le
    intro i
    fin_cases i <;> norm_num [negativeBiasPool,MaxoutProductGate.eval]
  · exact le_trans (by norm_num) (Thesis.Tropical.le_finiteMax (fun j : Fin 2 => ![-3,-5] j + ∑ i : Fin 0, (0 : ℝ)) 0)

-- A fixed fan-in does not supply the theorem's degree bound.
example : (MaxoutProductGate.monomial 1 (fun _ => (0 : Fin 1)) (fun _ => 100)).fanIn=1 ∧
    (MaxoutProductGate.monomial 1 (fun _ => (0 : Fin 1)) (fun _ => 100)).totalDegree=100 := by
  simp [MaxoutProductGate.fanIn,MaxoutProductGate.totalDegree]
end
