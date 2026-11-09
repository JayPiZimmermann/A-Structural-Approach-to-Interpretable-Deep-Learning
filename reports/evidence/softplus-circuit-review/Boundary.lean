import Thesis.SoftplusCircuitUniqueness
import Thesis.SoftplusCircuitVisits
import Thesis.SoftplusCircuitPayoff
set_option autoImplicit false
open HiddenMonotonicity Thesis.SoftplusCircuit Thesis.StoppingDAG Thesis.StoppingCircuit Thesis.Regularization
open scoped BigOperators
noncomputable section
namespace SoftCircuitReview

def zeroAct : NodeSpec (n := 0) (.maximum (SignedExpr.affine 0 (-2)) (.constant 0)) := .activation 0 (-2)
example (x : Vec 0) : nodeDiscount zeroAct x=0 := by
  simp [nodeDiscount,nodeWeights,baseExpr,zeroAct,expressionKernel_affine,localDiscount]
example (θ : ℝ) (x : Vec 0) : nodeProbability θ zeroAct x none=1 := by
  simp [nodeProbability,nodeWeights,baseExpr,zeroAct,expressionKernel_affine,localProbability,localDiscount]
example (x : Vec 0) : NodeRegular zeroAct x := trivial
example (θ : ℝ) (x : Vec 0) : nodeWith (softplus θ) zeroAct x=softplus θ (-2) := by
  simp [nodeWith,zeroAct,SignedExpr.affine_eval]

def affineOut : NodeSpec (SignedExpr.affine (![2,-1] : Vec 2) (-5)) := .affine ![2,-1] (-5)
example (x : Vec 2) : nodeDiscount affineOut x=3 := by
  norm_num [nodeDiscount,nodeWeights,baseExpr,affineOut,expressionKernel_affine,localDiscount,Fin.sum_univ_two]
example (θ : ℝ) (x : Vec 2) : nodeProbability θ affineOut x (some (1,true))=1/3 := by
  norm_num [nodeProbability,continuationProbability,nodeWeights,baseExpr,affineOut,expressionKernel_affine,localProbability,localDiscount,Fin.sum_univ_two]
example (θ : ℝ) : nodeWith (softplus θ) affineOut ![0,0]=(-5 : ℝ) := by
  norm_num [nodeWith,affineOut,SignedExpr.affine_eval,Fin.sum_univ_two]

def zeroScore : NodeSpec (SignedExpr.maximum (SignedExpr.affine (![1] : Vec 1) 0) (.constant 0)) := .activation ![1] 0
example : nodeDiscount zeroScore ![0]=1 := by
  norm_num [nodeDiscount,nodeWeights,baseExpr,zeroScore,expressionKernel_affine,localDiscount]
example : nodeProbability 1 zeroScore ![0] (some (0,false))=(1/2 : ℝ) := by
  norm_num [nodeProbability,continuationProbability,nodeWeights,baseExpr,zeroScore,expressionKernel_affine,localProbability,localDiscount,SignedExpr.affine_eval,gate,Real.sigmoid]

-- Earliest operand position is preserved even when graph references are reversed.
def reorderedPool : NodeSpec (orderedInputPool (![1,0] : Fin 2 → Fin 2)) := .pool ![1,0]
example : earliestWinner (fun i : Fin 2 => (![4,4] : Vec 2) ((![1,0] : Fin 2 → Fin 2) i))=0 := by
  norm_num [earliestWinner]
example : nodeWith (softplus 1) reorderedPool ![4,4]=4 := by
  norm_num [nodeWith,reorderedPool,orderedInputPool,orderedPool,SignedExpr.eval]
example : ¬NodeRegular reorderedPool ![4,4] := by
  intro h
  have hh := h (1 : Fin 2) (by norm_num [earliestWinner])
  norm_num [NodeRegular,reorderedPool,earliestWinner] at hh

-- Losing-tail ties impose no false strictness on a unique winner.
def losingTie : NodeSpec (orderedInputPool (![0,1,2] : Fin 3 → Fin 3)) := .pool ![0,1,2]
example : NodeRegular losingTie ![5,2,2] := by
  norm_num [NodeRegular,losingTie,earliestWinner,Fin.forall_fin_succ]

def constantCircuit : Circuit 0 1 := .node .inputs (.maximum (SignedExpr.affine 0 (-2)) (.constant 0))
def constantPlan : Plan constantCircuit := ((),zeroAct)
example (θ : ℝ) : Regular θ constantCircuit constantPlan 0 := ⟨trivial,trivial⟩
example (θ : ℝ) (hθ : 0<θ) : SubgamePerfect θ constantCircuit constantPlan
    (canonicalStrategy θ constantCircuit constantPlan 0)
    (canonicalStrategy θ constantCircuit constantPlan 0) (0,-0) :=
  canonical_spne constantCircuit constantPlan θ hθ 0
example (θ : ℝ) (hθ : 0<θ) :
  (graphSplit θ constantCircuit constantPlan (0,0)).1-(graphSplit θ constantCircuit constantPlan (0,0)).2=
  graphSoft θ constantCircuit constantPlan 0 := by
  simpa using graphSplit_recovery constantCircuit constantPlan θ hθ (0,0)
end SoftCircuitReview
