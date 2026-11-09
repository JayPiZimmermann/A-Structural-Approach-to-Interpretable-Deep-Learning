import HiddenMonotonicity.ExplicitSoftplus
import HiddenMonotonicity.MonotoneDCLift

example : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h
