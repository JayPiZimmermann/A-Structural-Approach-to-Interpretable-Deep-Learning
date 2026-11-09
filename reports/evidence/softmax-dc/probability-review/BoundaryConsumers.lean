import HiddenMonotonicity.SoftmaxProbability

set_option autoImplicit false
open scoped BigOperators
open HiddenMonotonicity.SoftmaxDC

example (w : Fin 1 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    -(w 0) ≤ 0 ∧ (0 : ℝ) ≤ w 0 := by
  have h := probability_second_bounds (fun _ : Fin 1 => (1 : ℝ))
    (by intro i; norm_num) (by simp) w hw 0
  simpa using h

example : plusCoeff (fun _ : Fin 1 => (1 : ℝ)) 0 0 = 1 / 2 ∧
    minusCoeff (fun _ : Fin 1 => (1 : ℝ)) 0 0 = 1 / 2 := by
  norm_num [plusCoeff, minusCoeff]

example : ∀ i j : Fin 2,
    0 ≤ plusCoeff ![(0 : ℝ), 1] i j ∧ plusCoeff ![(0 : ℝ), 1] i j ≤ 1 / 2 := by
  intro i j
  apply plusCoeff_bounds
  · intro k; fin_cases k <;> norm_num
  · norm_num [Fin.sum_univ_two]

example : ∀ i j : Fin 2,
    0 ≤ minusCoeff ![(0 : ℝ), 1] i j ∧ minusCoeff ![(0 : ℝ), 1] i j ≤ 1 / 2 := by
  intro i j
  apply minusCoeff_bounds
  · intro k; fin_cases k <;> norm_num
  · norm_num [Fin.sum_univ_two]

example : plusCoeff ![(1 / 2 : ℝ), 1 / 2] 0 0 = 3 / 8 ∧
    plusCoeff ![(1 / 2 : ℝ), 1 / 2] 0 1 = 1 / 8 ∧
    minusCoeff ![(1 / 2 : ℝ), 1 / 2] 0 0 = 1 / 8 ∧
    minusCoeff ![(1 / 2 : ℝ), 1 / 2] 0 1 = 3 / 8 := by
  norm_num [plusCoeff, minusCoeff]

example : -(2 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 2 := by
  have h := probability_second_bounds ![(1 / 2 : ℝ), 1 / 2]
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_two]) ![(4 : ℝ), 0]
    (by intro i; fin_cases i <;> norm_num) 0
  convert h using 1 <;> norm_num [Fin.sum_univ_two]

example : (∑ j : Fin 2, plusCoeff ![(1 / 2 : ℝ), 1 / 2] 0 j * (![-3, 5] j)) =
    (-1 : ℝ) / 2 := by
  rw [plusCoeff_sum]
  norm_num [Fin.sum_univ_two]

example : (∑ j : Fin 2, minusCoeff ![(1 / 2 : ℝ), 1 / 2] 0 j * (![-3, 5] j)) =
    (3 : ℝ) / 2 := by
  rw [minusCoeff_sum]
  norm_num [Fin.sum_univ_two]

example : (0 : ℝ) ≤ ∑ _j : Fin 0, (1 / 2 : ℝ) * (0 : ℝ) ∧
    (∑ _j : Fin 0, (1 / 2 : ℝ) * (0 : ℝ)) ≤ (∑ _j : Fin 0, (0 : ℝ)) / 2 := by
  exact coeff_direction_bounds (fun _ : Fin 0 => (1 / 2 : ℝ)) (fun _ => 0)
    (by intro j; exact ⟨by norm_num, le_rfl⟩) (by intro j; exact le_rfl)
