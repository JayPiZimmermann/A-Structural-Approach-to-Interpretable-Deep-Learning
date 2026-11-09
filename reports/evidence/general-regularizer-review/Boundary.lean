import Thesis.GeneralRegularization

noncomputable section
open Set Filter HiddenMonotonicity Matrix Thesis.GeneralRegularization

-- A source-admissible cost with nonzero endpoint values: no unstated normalization.
def shiftedCost : Regularizer where
  cost := fun _ => -2
  closed := continuous_const.continuousOn.lowerSemicontinuousOn
  convex := convexOn_const (-2) (convex_Icc 0 1)
  nonpos := by intro p hp; norm_num

theorem shifted_optimal (z : ℝ) :
    hardGate z ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (objective shiftedCost z) (Icc 0 1) (hardGate z) := by
  refine ⟨(hardGate_optimal z).1,?_⟩
  intro p hp
  have h := (hardGate_optimal z).2 hp
  dsimp [objective,zeroRegularizer,shiftedCost] at h ⊢
  linarith

example (z : ℝ) : activation shiftedCost z=relu z+2 := by
  have he : objective shiftedCost z (hardGate z)=activation shiftedCost z :=
    le_antisymm (objective_le _ _ _ (shifted_optimal z).1)
      ((shifted_optimal z).2 (gate_mem _ _))
  rw [← he]
  by_cases hz : 0<z
  · simp [objective,shiftedCost,hardGate,hz,relu,max_eq_left hz.le]
  · simp [objective,shiftedCost,hardGate,hz,relu,max_eq_right (le_of_not_gt hz)]

-- The source tie example: both policies maximize, but the two streams differ.
example : IsMaxOn (objective zeroRegularizer 0) (Icc 0 1) 0 := by
  intro p hp
  simp [objective,zeroRegularizer]
example : IsMaxOn (objective zeroRegularizer 0) (Icc 0 1) 1 := by
  intro p hp
  simp [objective,zeroRegularizer]
example : pairWith zeroRegularizer (fun _ => 0) (1,1)=(0,0) := by
  norm_num [pairWith,zeroRegularizer]
example : pairWith zeroRegularizer (fun _ => 1) (1,1)=(1,1) := by
  norm_num [pairWith,zeroRegularizer]
example : pairWith zeroRegularizer hardGate (1,1)=(0,0) := by
  norm_num [pairWith,zeroRegularizer,hardGate]

-- A valid global maximizing selection is always available from the actual compact maximum.
example (R : Regularizer) :
    ∀ z, gate R z ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (objective R z) (Icc 0 1) (gate R z) :=
  fun z => ⟨gate_mem R z,gate_optimal R z⟩

-- Every admissible activation is nonnegative. Nonconvex signed activations are
-- not silently identified with this maximum-over-probabilities construction.
example (R : Regularizer) (z : ℝ) : 0≤activation R z := by
  have h := objective_le R z 0 (by simp)
  have hc := R.nonpos 0 (by simp)
  dsimp [objective] at h
  linarith

-- The arbitrarily chosen entropy optimizer itself is the sigmoid: uniqueness
-- follows from the actual derivative theorem and proved softplus specialization.
example (θ : ℝ) (hθ : 0<θ) (z : ℝ) :
    gate (entropyRegularizer θ hθ) z=Thesis.Regularization.gate θ z := by
  have he : activation (entropyRegularizer θ hθ)=Thesis.Regularization.softplus θ :=
    funext (entropy_activation θ hθ)
  have hd : DifferentiableAt ℝ (activation (entropyRegularizer θ hθ)) z := by
    rw [he]
    exact (Thesis.Regularization.hasDerivAt_softplus θ z hθ).differentiableAt
  have h := optimizer_eq_deriv (entropyRegularizer θ hθ) z
    (gate (entropyRegularizer θ hθ) z) (gate_mem _ _) (gate_optimal _ _) hd
  rw [he,Thesis.Regularization.deriv_softplus θ z hθ] at h
  exact h

-- An actual ungated affine terminal may have a negative output and bias.
example :
    preP (0 : Matrix (Fin 1) (Fin 1) ℝ) (Matrix.of (fun _ _ => 3))
      ((fun _ => 2),(fun _ => 0)) + (0 : Vec 1) -
      (preN (0 : Matrix (Fin 1) (Fin 1) ℝ) (Matrix.of (fun _ _ => 3))
        ((fun _ => 2),(fun _ => 0)) + (fun _ => 1)) = (fun _ => -7) := by
  funext i
  norm_num [preP,preN,matrixCLM,Matrix.mulVec,dotProduct]

end
