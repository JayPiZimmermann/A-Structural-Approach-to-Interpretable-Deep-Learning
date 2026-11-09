import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

namespace HiddenMonotonicity.SoftmaxDC
open scoped BigOperators
open Set
variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def expSum (z : ι → ℝ) : ℝ := ∑ j, Real.exp (z j)
noncomputable def softmax (z : ι → ℝ) (i : ι) : ℝ := Real.exp (z i) / expSum z
noncomputable def logSumExp (z : ι → ℝ) : ℝ := Real.log (expSum z)
def affineLine (a v : ι → ℝ) (t : ℝ) : ι → ℝ := fun j => a j + t * v j
noncomputable def mean (z v : ι → ℝ) : ℝ := ∑ j, softmax z j * v j
noncomputable def variance (z v : ι → ℝ) : ℝ := ∑ j, softmax z j * (v j - mean z v) ^ 2
noncomputable def secondMoment (z v : ι → ℝ) : ℝ := ∑ j, softmax z j * (v j) ^ 2

theorem expSum_pos (z : ι → ℝ) : 0 < expSum z := by
  classical
  exact Finset.sum_pos (fun j _ => Real.exp_pos (z j)) Finset.univ_nonempty

theorem softmax_pos (z : ι → ℝ) (i : ι) : 0 < softmax z i :=
  div_pos (Real.exp_pos _) (expSum_pos z)

theorem softmax_sum (z : ι → ℝ) : ∑ j, softmax z j = 1 := by
  simp only [softmax, ← Finset.sum_div]
  exact div_self (ne_of_gt (expSum_pos z))

theorem softmax_le_one (z : ι → ℝ) (i : ι) : softmax z i ≤ 1 := by
  classical
  have h := Finset.single_le_sum (f := softmax z) (fun j _ => (softmax_pos z j).le)
    (Finset.mem_univ i)
  simpa only [softmax_sum] using h

omit [Nonempty ι] in
theorem mean_eq_quotient (z v : ι → ℝ) :
    mean z v = (∑ j, Real.exp (z j) * v j) / expSum z := by
  simp only [mean, softmax, div_mul_eq_mul_div, Finset.sum_div]

omit [Nonempty ι] in
theorem secondMoment_eq_quotient (z v : ι → ℝ) :
    secondMoment z v = (∑ j, Real.exp (z j) * (v j)^2) / expSum z := by
  simp only [secondMoment, softmax, div_mul_eq_mul_div, Finset.sum_div]

theorem variance_eq_secondMoment_sub_sq (z v : ι → ℝ) :
    variance z v = secondMoment z v - (mean z v)^2 := by
  calc
    variance z v = (∑ j, softmax z j * (v j)^2) -
        2 * mean z v * (∑ j, softmax z j * v j) +
        (mean z v)^2 * (∑ j, softmax z j) := by
      simp only [variance, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = secondMoment z v - (mean z v)^2 := by
      rw [softmax_sum]
      change secondMoment z v - 2 * mean z v * mean z v + mean z v ^ 2 * 1 = _
      ring

omit [Fintype ι] [Nonempty ι] in
theorem exp_affineLine_derivative (a v : ι → ℝ) (t : ℝ) (j : ι) :
    HasDerivAt (fun t => Real.exp (affineLine a v t j))
      (Real.exp (affineLine a v t j) * v j) t := by
  convert (((hasDerivAt_id t).mul_const (v j)).const_add (a j)).exp using 1
  <;> simp [affineLine]

omit [Nonempty ι] in
theorem expSum_line_derivative (a v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => expSum (affineLine a v t))
      (∑ j, Real.exp (affineLine a v t j) * v j) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => exp_affineLine_derivative a v t j)

theorem logSumExp_line_derivative (a v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => logSumExp (affineLine a v t))
      (mean (affineLine a v t) v) t := by
  simpa only [logSumExp, mean_eq_quotient] using
    (expSum_line_derivative a v t).log (ne_of_gt (expSum_pos _))

theorem softmax_line_derivative (a v : ι → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt (fun t => softmax (affineLine a v t) i)
      (softmax (affineLine a v t) i * (v i - mean (affineLine a v t) v)) t := by
  convert (exp_affineLine_derivative a v t i).div (expSum_line_derivative a v t)
    (ne_of_gt (expSum_pos _)) using 1
  · rfl
  · rw [mean_eq_quotient]
    unfold softmax
    field_simp [ne_of_gt (expSum_pos (affineLine a v t))]

theorem mean_line_derivative (a v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => mean (affineLine a v t) v)
      (variance (affineLine a v t) v) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (softmax_line_derivative a v t j).mul_const (v j))
  convert h using 1
  · rfl
  · rw [variance_eq_secondMoment_sub_sq]
    calc
      secondMoment (affineLine a v t) v - mean (affineLine a v t) v ^ 2 =
          (∑ j, softmax (affineLine a v t) j * v j ^ 2) -
          mean (affineLine a v t) v * (∑ j, softmax (affineLine a v t) j * v j) := by
        change secondMoment _ v - mean _ v ^ 2 = secondMoment _ v - mean _ v * mean _ v
        ring
      _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring

theorem softmaxFirst_line_derivative (a v : ι → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt
      (fun t => softmax (affineLine a v t) i * (v i - mean (affineLine a v t) v))
      (softmax (affineLine a v t) i *
        ((v i - mean (affineLine a v t) v)^2 - variance (affineLine a v t) v)) t := by
  convert (softmax_line_derivative a v t i).mul
    ((mean_line_derivative a v t).const_sub (v i)) using 1
  ring

theorem softmax_nonneg (z : ι → ℝ) (i : ι) : 0 ≤ softmax z i :=
  (softmax_pos z i).le

theorem softmax_sum_one (z : ι → ℝ) : ∑ j, softmax z j = 1 := softmax_sum z

omit [Nonempty ι] in
@[simp] theorem expSum_zero : expSum (0 : ι → ℝ) = Fintype.card ι := by
  simp [expSum]

omit [Nonempty ι] in
@[simp] theorem softmax_zero (i : ι) : softmax (0 : ι → ℝ) i = 1 / Fintype.card ι := by
  simp [softmax]

omit [Nonempty ι] in
@[simp] theorem logSumExp_zero : logSumExp (0 : ι → ℝ) = Real.log (Fintype.card ι) := by
  simp [logSumExp]

end HiddenMonotonicity.SoftmaxDC
