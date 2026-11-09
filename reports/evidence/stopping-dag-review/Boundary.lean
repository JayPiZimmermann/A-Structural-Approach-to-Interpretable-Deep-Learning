import Thesis.StoppingDAGIntermediate

noncomputable section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDecomposition Thesis.StoppingDAG
open scoped BigOperators

def tiedInputs : PairVec 2 := (![2,1],![1,0])
def twoPool : SignedExpr (Fin 2) := .maximum (.input 0) (.input 1)

-- Both represented operands equal positive one. Generic binary pool picks the
-- right operand, whereas the source smallest-index rule picks input zero.
example : tiedInputs.1 0-tiedInputs.2 0=tiedInputs.1 1-tiedInputs.2 1 := by
  norm_num [tiedInputs]
example : (expressionKernel twoPool tiedInputs).1 0=0 ∧
    (expressionKernel twoPool tiedInputs).1 1=1 := by
  norm_num [twoPool,pool_kernel,tiedInputs,Pi.single_apply]
example : stoppingExpr twoPool tiedInputs=(1,0) := by
  norm_num [twoPool,tiedInputs,stoppingExpr,HiddenMonotonicity.winnerPair]
example : stoppingExpr twoPool tiedInputs ≠ (tiedInputs.1 0,tiedInputs.2 0) := by
  norm_num [twoPool,tiedInputs,stoppingExpr,HiddenMonotonicity.winnerPair]
example : ¬ExpressionRegular twoPool tiedInputs := by
  norm_num [twoPool,tiedInputs,ExpressionRegular,score,SignedExpr.eval]

def constantGraph : Circuit 0 1 := .node .inputs (.constant (-5))
example : constantGraph.Additive := by trivial
example : CircuitRegular constantGraph (0,0) := by trivial
example : expectedPayoff constantGraph (0,0) 0 true=5 := by
  rw [expectedPayoff_eq_stoppingCircuit constantGraph (by trivial)]
  norm_num [constantGraph,stoppingCircuit,stoppingExpr,streamValue,Fin.snoc]
example : (∑ path : DAGPaths constantGraph,pathProbability constantGraph (0,0) 0 path)=1 :=
  pathProbability_normalized _ _ _
example : localProbability (expressionKernel (.constant (-5) : SignedExpr (Fin 0)) (0,0)) none=1 := by
  simp [expressionKernel,localProbability,localDiscount]

example (x : PairVec 1) : localDiscount (expressionKernel (.add (.input 0) (.input 0)) x)=2 :=
  addition_discount 0 0 x
example (x : PairVec 1) :
    localProbability (expressionKernel (.add (.input 0) (.input 0)) x) (some (0,false))=1 := by
  rw [addition_probability]
  norm_num [additionProbability]

example : ExpressionRegular
    (.maximum (.maximum (.input 0) (.constant 0)) (.constant 2)) ((0,0) : PairVec 1) := by
  norm_num [ExpressionRegular,score,SignedExpr.eval]

example : expressionKernel (.maximum (.input 0) (.constant 0))
    (((fun _ => 1),(fun _ => 1)) : PairVec 1)=(0,0) := by
  rw [relu_kernel]
  simp
end
