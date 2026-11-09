import HiddenMonotonicity.DifferentiableBackward
import HiddenMonotonicity.PoolingCircuit
open HiddenMonotonicity
namespace HiddenRecheck

noncomputable def zeroNet : Network 1 1 := .layer 0 0 0 0 (.output 1)

theorem zeroNet_never_strict (x : Vec 1) : ¬zeroNet.Strict x := by
  simp [zeroNet, Network.Strict, affineLayer, matrixCLM]

theorem zeroNet_nonvacuous_new_head (x : Vec 1) :
    HasFDerivAt (fun y => (zeroNet.affineHeads (ContinuousLinearMap.proj 0) 0 3 7
      (balancedLift 1 y)).1)
      (unified ((zeroNet.originalTrace x).run (fun _ => 0)
        (affineReadoutSeed (ContinuousLinearMap.proj 0) 0 0 true))) x := by
  apply zeroNet.affine_symmetric_derivative_of_differentiable
    (by simp [zeroNet, Network.Nonnegative]) x (ContinuousLinearMap.proj 0) 0
    (fun _ _ h => h 0) (fun _ _ _ => le_rfl) 3 7 true
  have he : (fun y => (zeroNet.affineHeads (ContinuousLinearMap.proj 0) 0 3 7
      (balancedLift 1 y)).1) = fun _ => (3 : ℝ) := by
    funext y
    simp [zeroNet, Network.affineHeads, Network.split]
  change DifferentiableAt ℝ _ x
  simp only [ite_true, he]
  exact differentiableAt_const 3

noncomputable def repeated : Network 1 1 :=
  .layer (fun _ _ : Fin 1 => (1 : ℝ)) 0 0 0 (.layer (fun _ _ : Fin 1 => (1 : ℝ)) 0 0 0 (.output 1))

theorem repeated_tied_on_negative_halfline (x : Vec 1) (hx : x 0 < 0) :
    ¬repeated.Strict x := by
  simp [repeated, Network.Strict, affineLayer, reluLayer, matrixCLM, Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.zero_apply, relu,
    max_eq_right (le_of_lt hx)]
  intro _ _ _
  change ((1 : ℝ)-0)*x 0 ≤ 0
  simpa using hx.le

-- This support conclusion is global despite persistent second-layer zero ties.
theorem repeated_support (x y : PairVec 1) :
    repeated.split x.1 x.2 + repeated.jacobian x (y-x) ≤ repeated.split y.1 y.2 := by
  exact repeated.split_affine_support (by simp [repeated, Network.Nonnegative]) x y

theorem signed_readout_is_ungated :
    ((Network.output 1).affineHeads 0 (ContinuousLinearMap.proj 0) 3 7
      ((fun _ => 2),(fun _ => 0))).1 = 3 ∧
    ((Network.output 1).affineHeads 0 (ContinuousLinearMap.proj 0) 3 7
      ((fun _ => 2),(fun _ => 0))).2 = 9 ∧
    (Network.output 1).affineLogit 0 (ContinuousLinearMap.proj 0) 3 7 (fun _ => 2) = -6 := by
  norm_num [Network.affineHeads, Network.affineLogit, Network.split, Network.eval]

def poolExpr : SignedExpr (Fin 3) := .maximum (.input 0) (.maximum (.input 1) (.input 2))
noncomputable def poolInput (i : Fin 3 × Bool) : ℝ := if i.2 then ![9,0,99] i.1 else ![10,2,100] i.1

theorem nested_pool_forwards_actual_pair : poolExpr.poolTreeSplit poolInput = (2,0) := by
  norm_num [poolExpr, SignedExpr.poolTreeSplit, SignedExpr.split, PositiveExpr.eval, poolInput, winnerPair]

theorem tied_pool_uses_one_pair : winnerPair (3,1) (2,0) = (3,1) := by
  norm_num [winnerPair]

noncomputable def mixedCircuit : Circuit 3 5 :=
  .node (.node .inputs poolExpr) (.scale (-1) (.input 3))

theorem mixed_policies_actual_values :
    (mixedCircuit.splitWithPolicy (fun i => if i=3 then .winner else .convex)
      (fun i => i=4) poolInput).1 4 = 0 ∧
    (mixedCircuit.splitWithPolicy (fun i => if i=3 then .winner else .convex)
      (fun i => i=4) poolInput).2 4 = 2 := by
  norm_num [mixedCircuit, Circuit.splitWithPolicy, SignedExpr.splitAtNode, poolExpr,
    SignedExpr.poolTreeSplit, SignedExpr.split, PositiveExpr.eval, poolInput,
    winnerPair, recenterPair, Fin.snoc]

#print axioms zeroNet_nonvacuous_new_head
#print axioms repeated_support
#print axioms signed_readout_is_ungated
#print axioms nested_pool_forwards_actual_pair
#print axioms mixed_policies_actual_values
end HiddenRecheck
