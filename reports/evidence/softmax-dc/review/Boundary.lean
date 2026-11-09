import HiddenMonotonicity.ExplicitSoftmax

set_option autoImplicit false
open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators

example (x y : ℝ) :
    softmaxSplitFirst (0 : Fin 1) (fun _ => x, fun _ => y) = x / 2 + 1 := by
  rw [softmaxSplitFirst_formula]
  simp only [Fin.sum_univ_one, Fintype.card_fin, Nat.cast_one, Real.log_one,
    Real.log_exp, div_self (Real.exp_ne_zero _)]
  ring

example (x y : ℝ) :
    softmaxSplitSecond (0 : Fin 1) (fun _ => x, fun _ => y) = x / 2 := by
  rw [softmaxSplitSecond_formula]
  simp only [Fin.sum_univ_one, Fintype.card_fin, Nat.cast_one, Real.log_one,
    Real.log_exp, div_self (Real.exp_ne_zero _)]
  ring

example : softmaxSplitFirst (0 : Fin 2) 0 = 1 / 2 := by simp
example : softmaxSplitSecond (0 : Fin 3) 0 = 0 := by simp

example : softmaxPFirst (0 : Fin 2) 0 ![1,0] = 3 / 8 := by
  norm_num [softmaxPFirst, mean, softmax_zero, Fin.sum_univ_two]

example : softmaxQFirst (0 : Fin 2) 0 ![1,0] = 1 / 8 := by
  norm_num [softmaxQFirst, mean, softmax_zero, Fin.sum_univ_two]

example : softmaxPFirst (0 : Fin 2) 0 ![0,1] = 1 / 8 := by
  norm_num [softmaxPFirst, mean, softmax_zero, Fin.sum_univ_two]

example : softmaxQFirst (0 : Fin 2) 0 ![0,1] = 3 / 8 := by
  norm_num [softmaxQFirst, mean, softmax_zero, Fin.sum_univ_two]

example : softmaxPFirst (0 : Fin 3) 0 ![1,0,0] = 5 / 18 := by
  norm_num [softmaxPFirst, mean, softmax_zero, Fin.sum_univ_succ]

example : softmaxQFirst (0 : Fin 3) 0 ![1,0,0] = 1 / 18 := by
  norm_num [softmaxQFirst, mean, softmax_zero, Fin.sum_univ_succ]

example : softmaxSplitFirst (0 : Fin 2) (![-2,1], ![3,-4]) -
    softmaxSplitSecond (0 : Fin 2) (![-2,1], ![3,-4]) =
    Real.exp (-5) / (Real.exp (-5) + Real.exp 5) := by
  rw [softmaxSplit_difference]
  norm_num [softmax, expSum, Fin.sum_univ_two]

example : softmaxSplitFirst (0 : Fin 2) (![-2,1], ![3,-4]) ≤
    softmaxSplitFirst (0 : Fin 2) (![1,2], ![4,-3]) := by
  apply softmaxSplitFirst_monotone
  constructor <;> intro j <;> fin_cases j <;> norm_num

example : softmaxSplitSecond (0 : Fin 2) (![-2,1], ![3,-4]) ≤
    softmaxSplitSecond (0 : Fin 2) (![1,2], ![4,-3]) := by
  apply softmaxSplitSecond_monotone
  constructor <;> intro j <;> fin_cases j <;> norm_num

example : 0 ≤ softmaxSplitFirst (1 : Fin 3) (![0,1,4], ![3,0,2]) ∧
    0 ≤ softmaxSplitSecond (1 : Fin 3) (![0,1,4], ![3,0,2]) := by
  have hz : (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ)) ≤ (![0,1,4], ![3,0,2]) := by
    constructor <;> intro j <;> fin_cases j <;> norm_num
  exact ⟨softmaxSplitFirst_nonnegative _ _ hz, softmaxSplitSecond_nonnegative _ _ hz⟩

example : ConvexOn ℝ Set.univ (softmaxSplitFirst (2 : Fin 3)) :=
  (softmax_split_properties (2 : Fin 3)).1

example : ConvexOn ℝ Set.univ (softmaxSplitSecond (1 : Fin 2)) :=
  (softmax_split_properties (1 : Fin 2)).2.1
