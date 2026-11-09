import HiddenMonotonicity.SoftmaxLineCalculus
import HiddenMonotonicity.SoftmaxProbability
import HiddenMonotonicity.MultivariateMonotoneDCLift

namespace HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
open Set
variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def softmaxP (i : ι) (z : ι → ℝ) : ℝ :=
  (logSumExp z + softmax z i) / 2

noncomputable def softmaxQ (i : ι) (z : ι → ℝ) : ℝ :=
  (logSumExp z - softmax z i) / 2

noncomputable def softmaxPFirst (i : ι) (z v : ι → ℝ) : ℝ :=
  (mean z v + softmax z i * (v i - mean z v)) / 2

noncomputable def softmaxQFirst (i : ι) (z v : ι → ℝ) : ℝ :=
  (mean z v - softmax z i * (v i - mean z v)) / 2

theorem softmaxP_line_derivative (i : ι) (a v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => softmaxP i (affineLine a v t))
      (softmaxPFirst i (affineLine a v t) v) t :=
  ((logSumExp_line_derivative a v t).add (softmax_line_derivative a v t i)).div_const 2

theorem softmaxQ_line_derivative (i : ι) (a v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => softmaxQ i (affineLine a v t))
      (softmaxQFirst i (affineLine a v t) v) t :=
  ((logSumExp_line_derivative a v t).sub (softmax_line_derivative a v t i)).div_const 2

theorem softmaxPFirst_line_derivative (i : ι) (a v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => softmaxPFirst i (affineLine a v t) v)
      ((variance (affineLine a v t) v + softmax (affineLine a v t) i *
        ((v i - mean (affineLine a v t) v)^2 - variance (affineLine a v t) v)) / 2) t :=
  ((mean_line_derivative a v t).add (softmaxFirst_line_derivative a v t i)).div_const 2

theorem softmaxQFirst_line_derivative (i : ι) (a v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => softmaxQFirst i (affineLine a v t) v)
      ((variance (affineLine a v t) v - softmax (affineLine a v t) i *
        ((v i - mean (affineLine a v t) v)^2 - variance (affineLine a v t) v)) / 2) t :=
  ((mean_line_derivative a v t).sub (softmaxFirst_line_derivative a v t i)).div_const 2

theorem softmax_second_bounds (i : ι) (z v : ι → ℝ) :
    -variance z v ≤ softmax z i * ((v i - mean z v)^2 - variance z v) ∧
      softmax z i * ((v i - mean z v)^2 - variance z v) ≤ variance z v :=
  probability_second_bounds (softmax z) (softmax_nonneg z) (softmax_sum z)
    (fun j => (v j - mean z v)^2) (fun _ => sq_nonneg _) i

theorem softmaxPFirst_direction_bounds (i : ι) (z v : ι → ℝ)
    (hv : ∀ j, 0 ≤ v j) :
    0 ≤ softmaxPFirst i z v ∧ softmaxPFirst i z v ≤ (∑ j, v j) / 2 := by
  classical
  simpa only [plusCoeff_sum, softmaxPFirst, mean] using
    coeff_direction_bounds (plusCoeff (softmax z) i) v
      (plusCoeff_bounds (softmax z) (softmax_nonneg z) (softmax_sum z) i) hv

theorem softmaxQFirst_direction_bounds (i : ι) (z v : ι → ℝ)
    (hv : ∀ j, 0 ≤ v j) :
    0 ≤ softmaxQFirst i z v ∧ softmaxQFirst i z v ≤ (∑ j, v j) / 2 := by
  classical
  simpa only [minusCoeff_sum, softmaxQFirst, mean] using
    coeff_direction_bounds (minusCoeff (softmax z) i) v
      (minusCoeff_bounds (softmax z) (softmax_nonneg z) (softmax_sum z) i) hv

theorem softmaxP_line_convex (i : ι) (a v : ι → ℝ) :
    ConvexOn ℝ univ (fun t => softmaxP i (affineLine a v t)) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun t => (softmaxP_line_derivative i a v t).differentiableAt)
  have hm : Monotone (fun t => softmaxPFirst i (affineLine a v t) v) := by
    apply monotone_of_deriv_nonneg
    · exact fun t => (softmaxPFirst_line_derivative i a v t).differentiableAt
    · intro t
      rw [(softmaxPFirst_line_derivative i a v t).deriv]
      have h := (softmax_second_bounds i (affineLine a v t) v).1
      linarith
  intro x y hxy
  rw [(softmaxP_line_derivative i a v x).deriv, (softmaxP_line_derivative i a v y).deriv]
  exact hm hxy

theorem softmaxQ_line_convex (i : ι) (a v : ι → ℝ) :
    ConvexOn ℝ univ (fun t => softmaxQ i (affineLine a v t)) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun t => (softmaxQ_line_derivative i a v t).differentiableAt)
  have hm : Monotone (fun t => softmaxQFirst i (affineLine a v t) v) := by
    apply monotone_of_deriv_nonneg
    · exact fun t => (softmaxQFirst_line_derivative i a v t).differentiableAt
    · intro t
      rw [(softmaxQFirst_line_derivative i a v t).deriv]
      have h := (softmax_second_bounds i (affineLine a v t) v).2
      linarith
  intro x y hxy
  rw [(softmaxQ_line_derivative i a v x).deriv, (softmaxQ_line_derivative i a v y).deriv]
  exact hm hxy

theorem softmaxP_convex (i : ι) : ConvexOn ℝ univ (softmaxP i) :=
  convex_from_affine_lines (softmaxP i) (softmaxP_line_convex i)

theorem softmaxQ_convex (i : ι) : ConvexOn ℝ univ (softmaxQ i) :=
  convex_from_affine_lines (softmaxQ i) (softmaxQ_line_convex i)

theorem softmaxP_monotone (i : ι) : Monotone (softmaxP i) :=
  monotone_from_affine_line_deriv (softmaxP i) (softmaxPFirst i)
    (softmaxP_line_derivative i) (fun z v hv => (softmaxPFirst_direction_bounds i z v hv).1)

theorem softmaxQ_monotone (i : ι) : Monotone (softmaxQ i) :=
  monotone_from_affine_line_deriv (softmaxQ i) (softmaxQFirst i)
    (softmaxQ_line_derivative i) (fun z v hv => (softmaxQFirst_direction_bounds i z v hv).1)

omit [Nonempty ι] in
theorem sum_line_derivative (a v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∑ j, affineLine a v t j) (∑ j, v j) t := by
  simpa only [affineLine, id_eq, one_mul] using HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (((hasDerivAt_id t).mul_const (v j)).const_add (a j)))

theorem softmaxP_complement_monotone (i : ι) :
    Monotone (fun z : ι → ℝ => (1 / 2 : ℝ) * (∑ j, z j) - softmaxP i z) := by
  apply monotone_from_affine_line_deriv _
    (fun z v => (1 / 2 : ℝ) * (∑ j, v j) - softmaxPFirst i z v)
  · intro a v t
    exact ((sum_line_derivative a v t).const_mul (1 / 2)).sub
      (softmaxP_line_derivative i a v t)
  · intro z v hv
    have h := (softmaxPFirst_direction_bounds i z v hv).2
    linarith

theorem softmaxQ_complement_monotone (i : ι) :
    Monotone (fun z : ι → ℝ => (1 / 2 : ℝ) * (∑ j, z j) - softmaxQ i z) := by
  apply monotone_from_affine_line_deriv _
    (fun z v => (1 / 2 : ℝ) * (∑ j, v j) - softmaxQFirst i z v)
  · intro a v t
    exact ((sum_line_derivative a v t).const_mul (1 / 2)).sub
      (softmaxQ_line_derivative i a v t)
  · intro z v hv
    have h := (softmaxQFirst_direction_bounds i z v hv).2
    linarith

noncomputable def softmaxNormalization (ι : Type*) [Fintype ι] : ℝ :=
  (Real.log (Fintype.card ι) - 1 / Fintype.card ι) / 2

noncomputable def softmaxSplitFirst (i : ι) (z : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  multivariateLift (softmaxP i) (1 / 2) (softmaxNormalization ι) z

noncomputable def softmaxSplitSecond (i : ι) (z : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  multivariateLift (softmaxQ i) (1 / 2) (softmaxNormalization ι) z

omit [Nonempty ι] in
theorem softmaxSplitFirst_formula (i : ι) (x y : ι → ℝ) :
    softmaxSplitFirst i (x, y) =
      (Real.log (∑ j, Real.exp (x j - y j)) +
        Real.exp (x i - y i) / (∑ j, Real.exp (x j - y j)) + ∑ j, y j) / 2 -
        (Real.log (Fintype.card ι) - 1 / Fintype.card ι) / 2 := by
  simp only [softmaxSplitFirst, multivariateLift, softmaxP, softmaxNormalization,
    logSumExp, softmax, expSum, Pi.sub_apply]
  ring

omit [Nonempty ι] in
theorem softmaxSplitSecond_formula (i : ι) (x y : ι → ℝ) :
    softmaxSplitSecond i (x, y) =
      (Real.log (∑ j, Real.exp (x j - y j)) -
        Real.exp (x i - y i) / (∑ j, Real.exp (x j - y j)) + ∑ j, y j) / 2 -
        (Real.log (Fintype.card ι) - 1 / Fintype.card ι) / 2 := by
  simp only [softmaxSplitSecond, multivariateLift, softmaxQ, softmaxNormalization,
    logSumExp, softmax, expSum, Pi.sub_apply]
  ring

theorem softmaxSplitFirst_convex (i : ι) : ConvexOn ℝ univ (softmaxSplitFirst i) :=
  multivariateLift_convex _ _ _ (softmaxP_convex i)

theorem softmaxSplitSecond_convex (i : ι) : ConvexOn ℝ univ (softmaxSplitSecond i) :=
  multivariateLift_convex _ _ _ (softmaxQ_convex i)

theorem softmaxSplitFirst_monotone (i : ι) : Monotone (softmaxSplitFirst i) :=
  multivariateLift_monotone _ _ _ (softmaxP_monotone i) (softmaxP_complement_monotone i)

theorem softmaxSplitSecond_monotone (i : ι) : Monotone (softmaxSplitSecond i) :=
  multivariateLift_monotone _ _ _ (softmaxQ_monotone i) (softmaxQ_complement_monotone i)

omit [Nonempty ι] in
theorem softmaxSplit_difference (i : ι) (z : (ι → ℝ) × (ι → ℝ)) :
    softmaxSplitFirst i z - softmaxSplitSecond i z = softmax (z.1 - z.2) i := by
  dsimp [softmaxSplitFirst, softmaxSplitSecond, multivariateLift, softmaxP, softmaxQ]
  ring

omit [Nonempty ι] in
@[simp] theorem softmaxSplitFirst_zero (i : ι) :
    softmaxSplitFirst i 0 = 1 / Fintype.card ι := by
  simp [softmaxSplitFirst, multivariateLift, softmaxP, softmaxNormalization]
  ring

omit [Nonempty ι] in
@[simp] theorem softmaxSplitSecond_zero (i : ι) : softmaxSplitSecond i 0 = 0 := by
  simp [softmaxSplitSecond, multivariateLift, softmaxQ, softmaxNormalization]

theorem softmaxSplitFirst_nonnegative (i : ι) (z : (ι → ℝ) × (ι → ℝ)) (hz : 0 ≤ z) :
    0 ≤ softmaxSplitFirst i z := by
  have h := softmaxSplitFirst_monotone i hz
  rw [softmaxSplitFirst_zero] at h
  exact le_trans (by positivity) h

theorem softmaxSplitSecond_nonnegative (i : ι) (z : (ι → ℝ) × (ι → ℝ)) (hz : 0 ≤ z) :
    0 ≤ softmaxSplitSecond i z := by
  have h := softmaxSplitSecond_monotone i hz
  simpa only [softmaxSplitSecond_zero] using h

/-- The explicit coupled softmax heads are convex and coordinatewise monotone on
the whole expanded space, and nonnegative on its nonnegative orthant. -/
theorem softmax_split_properties (i : ι) :
    ConvexOn ℝ univ (softmaxSplitFirst i) ∧
    ConvexOn ℝ univ (softmaxSplitSecond i) ∧
    Monotone (softmaxSplitFirst i) ∧ Monotone (softmaxSplitSecond i) ∧
    (∀ z, softmaxSplitFirst i z - softmaxSplitSecond i z = softmax (z.1 - z.2) i) ∧
    (∀ z, 0 ≤ z → 0 ≤ softmaxSplitFirst i z ∧ 0 ≤ softmaxSplitSecond i z) :=
  ⟨softmaxSplitFirst_convex i, softmaxSplitSecond_convex i,
   softmaxSplitFirst_monotone i, softmaxSplitSecond_monotone i,
   softmaxSplit_difference i, fun z hz =>
     ⟨softmaxSplitFirst_nonnegative i z hz, softmaxSplitSecond_nonnegative i z hz⟩⟩

end HiddenMonotonicity.SoftmaxDC
