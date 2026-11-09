import HiddenMonotonicity.PositiveExpressions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

namespace HiddenMonotonicity

noncomputable def PositivePolynomial.toMvPolynomial {ι} : PositivePolynomial ι → MvPolynomial ι ℝ
  | .input i => MvPolynomial.X i
  | .constant c _ => MvPolynomial.C c
  | .add a b => a.toMvPolynomial+b.toMvPolynomial
  | .mul a b => a.toMvPolynomial*b.toMvPolynomial

/-- The syntactic polynomial witnesses are ordinary multivariate polynomials. -/
theorem PositivePolynomial.toMvPolynomial_eval {ι} (p : PositivePolynomial ι) (x : ι → ℝ) :
    MvPolynomial.eval x p.toMvPolynomial=p.eval x := by
  induction p <;> simp_all [toMvPolynomial,PositivePolynomial.eval]

/-- Every actual multivariate coefficient is nonnegative. Natural exponents
are built into the Finsupp-Nat monomial type of MvPolynomial. -/
theorem PositivePolynomial.coefficients_nonnegative {ι} (p : PositivePolynomial ι)
    (d : ι →₀ ℕ) : 0≤p.toMvPolynomial.coeff d := by
  classical
  induction p generalizing d with
  | input i => simp only [toMvPolynomial,MvPolynomial.coeff_X]; split_ifs <;> norm_num
  | constant c hc =>
      simp only [toMvPolynomial,MvPolynomial.coeff_C]
      split_ifs <;> simp_all
  | add a b ha hb => simpa only [toMvPolynomial,MvPolynomial.coeff_add] using add_nonneg (ha d) (hb d)
  | mul a b ha hb =>
      rw [toMvPolynomial,MvPolynomial.coeff_mul]
      apply Finset.sum_nonneg
      intro d hd
      exact mul_nonneg (ha _) (hb _)

end HiddenMonotonicity
