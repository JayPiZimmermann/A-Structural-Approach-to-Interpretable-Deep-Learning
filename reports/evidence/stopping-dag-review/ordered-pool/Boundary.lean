import Thesis.StoppingOrderedPool
noncomputable section
open HiddenMonotonicity Thesis.StoppingCircuit Thesis.StoppingDAG

def tiedInputs : PairVec 2 := (![2,1],![1,0])
example : earliestWinner (![1,1] : Fin 2 → ℝ)=0 := by
  norm_num [earliestWinner]
example : stoppingExpr (orderedInputPool (id : Fin 2 → Fin 2)) tiedInputs=(2,1) := by
  rw [(orderedInputPool_source _ _).2.2.1]
  norm_num [earliestWinner,tiedInputs]
example : (expressionKernel (orderedInputPool (id : Fin 2 → Fin 2)) tiedInputs).1 0=1 ∧
    (expressionKernel (orderedInputPool (id : Fin 2 → Fin 2)) tiedInputs).1 1=0 := by
  rw [(orderedInputPool_source _ _).2.2.2]
  norm_num [earliestWinner,tiedInputs,Pi.single_apply]

-- Singleton pools work, without fabricating an extra operand or tie.
example (x : PairVec 1) : ExpressionRegular (orderedInputPool (fun _ : Fin 1 => (0 : Fin 1))) x := by
  apply orderedInputPool_regular _ _ 0
  intro i hi
  exact False.elim (hi (Fin.eq_zero i))

-- Minimum operand position does not silently mean minimum graph index under
-- an unsorted enumeration: permutation deliberately changes the tie choice.
example : stoppingExpr (orderedInputPool (![1,0] : Fin 2 → Fin 2)) tiedInputs=(1,0) := by
  rw [(orderedInputPool_source _ _).2.2.1]
  norm_num [earliestWinner,tiedInputs]

-- Tied losing tail, with a genuinely unique maximum, is regular.
def uniqueInputs : PairVec 3 := (![2,1,1],0)
example : ExpressionRegular (orderedInputPool (id : Fin 3 → Fin 3)) uniqueInputs := by
  apply orderedInputPool_regular _ _ 0
  intro i hi
  fin_cases i <;> norm_num [uniqueInputs] at *

-- Concrete source-ordered shared DAG global row and all-point occupation.
def pooled : Circuit 2 3 := .node .inputs (orderedInputPool (id : Fin 2 → Fin 2))
example : pooled.Additive := by
  constructor
  · trivial
  · exact orderedPool_additive _ (fun _ => by trivial)
example : occupation pooled tiedInputs (Fin.last 2) false 0 false=1 := by
  rw [occupation_eq_kernel pooled (by constructor; trivial; exact orderedPool_additive _ (fun _ => by trivial))]
  have h := (orderedInputPool_dag_row (Circuit.inputs : Circuit 2 2) (id : Fin 2 → Fin 2) tiedInputs).1
  change (dagKernel (.node Circuit.inputs (orderedInputPool id)) tiedInputs).1 (Fin.last 2) 0=1
  rw [h]
  norm_num [stoppingCircuit,earliestWinner,tiedInputs,dagKernel,Matrix.one_apply]
end
