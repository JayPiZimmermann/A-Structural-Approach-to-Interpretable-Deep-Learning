import HiddenMonotonicity.SoftmaxLineCalculus

set_option autoImplicit false
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators

example (x : ℝ) : softmax (fun _ : Fin 1 => x) 0 = 1 := by
  simp [softmax, expSum, Real.exp_ne_zero]

example : HasDerivAt
    (fun r : ℝ => softmax (affineLine (0 : Fin 2 → ℝ) ![1,-1] r) 0)
    (1 / 2) 0 := by
  convert softmax_line_derivative (0 : Fin 2 → ℝ) ![1,-1] 0 0 using 1
  all_goals norm_num [affineLine, softmax, expSum, mean, Fin.sum_univ_two]

example : HasDerivAt
    (fun r : ℝ => logSumExp (affineLine (0 : Fin 2 → ℝ) ![1,-1] r)) 0 0 := by
  convert logSumExp_line_derivative (0 : Fin 2 → ℝ) ![1,-1] 0 using 1
  all_goals norm_num [affineLine, softmax, expSum, mean, Fin.sum_univ_two]

example : HasDerivAt
    (fun r : ℝ => mean (affineLine (0 : Fin 2 → ℝ) ![1,-1] r) ![1,-1]) 1 0 := by
  convert mean_line_derivative (0 : Fin 2 → ℝ) ![1,-1] 0 using 1
  all_goals norm_num [affineLine, softmax, expSum, mean, variance, Fin.sum_univ_two]

example : HasDerivAt
    (fun r : ℝ => softmax (affineLine (0 : Fin 2 → ℝ) ![1,-1] r) 0 *
      (1 - mean (affineLine (0 : Fin 2 → ℝ) ![1,-1] r) ![1,-1])) 0 0 := by
  convert softmaxFirst_line_derivative (0 : Fin 2 → ℝ) ![1,-1] 0 0 using 1
  all_goals norm_num [affineLine, softmax, expSum, mean, variance, Fin.sum_univ_two]
