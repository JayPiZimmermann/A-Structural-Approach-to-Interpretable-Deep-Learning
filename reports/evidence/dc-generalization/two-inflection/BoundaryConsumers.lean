import HiddenMonotonicity.TwoInflectionDC
import HiddenMonotonicity.GELUInflectionBounds

open Set
open HiddenMonotonicity.SmoothDC

/- Threshold equality, interval boundary, signed-input and nonlinear
nonvacuity consumers. -/

example (f d : ℝ → ℝ) (a b : ℝ) :
    centralConvexP f d a b a = f a - d a * a := by
  simp [centralConvexP]

example (f d : ℝ → ℝ) (a b : ℝ) (hab : a < b) :
    centralConvexP f d a b b = f b - d a * b := by
  simp [centralConvexP, not_le.mpr hab]

example (d : ℝ → ℝ) (a b : ℝ) : centralConvexPFirst d a b a = 0 := by
  simp [centralConvexPFirst]

example (d : ℝ → ℝ) (a b : ℝ) (hab : a < b) :
    centralConvexPFirst d a b b = d b - d a := by
  simp [centralConvexPFirst, not_le.mpr hab]

example :
    let a := -Real.sqrt 2
    let b := Real.sqrt 2
    let L := gaussianGeluFirst b - gaussianGeluFirst a
    let P := centralConvexP gaussianGelu gaussianGeluFirst a b
    let Q := centralConvexQ gaussianGelu gaussianGeluFirst a b
    ConvexOn ℝ univ (asymmetricLift P L) ∧
    ConvexOn ℝ univ (asymmetricLift Q L) ∧
    Monotone (asymmetricLift P L) ∧ Monotone (asymmetricLift Q L) ∧
    ∀ z : ℝ × ℝ, asymmetricLift P L z - asymmetricLift Q L z = gaussianGelu (z.1 - z.2) := by
  dsimp
  apply centralConvex_asymmetric_split gaussianGelu gaussianGeluFirst
    (-Real.sqrt 2) (Real.sqrt 2)
  · have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    linarith
  · exact gaussianGelu_hasDerivAt
  · exact gaussianGeluFirst_antitone_left
  · exact gaussianGeluFirst_monotone_middle
  · exact gaussianGeluFirst_antitone_right
  · exact fun _ hx => (gaussianGeluFirst_left_bounds hx).2
  · exact fun _ hx => (gaussianGeluFirst_right_bounds hx).1

example (f d : ℝ → ℝ) (a b : ℝ) :
    asymmetricLift (centralConvexP f d a b) (d b - d a) (-3, 2) -
      asymmetricLift (centralConvexQ f d a b) (d b - d a) (-3, 2) = f (-5) := by
  convert asymmetricLift_difference _ _ _ _ (centralConvexP_sub_Q f d a b) (-3, 2) using 1
  norm_num
