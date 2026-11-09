import HiddenMonotonicity.Decomposition

namespace HiddenMonotonicity

/-- Downstream nonnegative-weight arithmetic: max, sum, scaling, and products.
Inputs are the nonnegative split variables. No convexity is asserted for products. -/
inductive PositiveExpr (ι : Type*)
  | input (i : ι)
  | constant (c : ℝ) (hc : 0≤c)
  | add (a b : PositiveExpr ι)
  | scale (c : ℝ) (hc : 0≤c) (a : PositiveExpr ι)
  | mul (a b : PositiveExpr ι)
  | maximum (a b : PositiveExpr ι)

noncomputable def PositiveExpr.eval {ι} : PositiveExpr ι → (ι → ℝ) → ℝ
  | .input i, x => x i
  | .constant c _, _ => c
  | .add a b, x => a.eval x+b.eval x
  | .scale c _ a, x => c*a.eval x
  | .mul a b, x => a.eval x*b.eval x
  | .maximum a b, x => max (a.eval x) (b.eval x)

def PositiveExpr.Additive {ι} : PositiveExpr ι → Prop
  | .input _ | .constant _ _ => True
  | .add a b | .maximum a b => a.Additive ∧ b.Additive
  | .scale _ _ a => a.Additive
  | .mul _ _ => False

theorem PositiveExpr.nonnegative {ι} (e : PositiveExpr ι) (x : ι → ℝ) (hx : 0≤x) :
    0≤e.eval x := by
  induction e with
  | input i => exact hx i
  | constant c hc => exact hc
  | add a b ha hb => exact add_nonneg ha hb
  | scale c hc a ha => exact mul_nonneg hc ha
  | mul a b ha hb => exact mul_nonneg ha hb
  | maximum a b ha hb => exact le_trans ha (le_max_left _ _)

theorem PositiveExpr.monotone_nonnegative {ι} (e : PositiveExpr ι) (x y : ι → ℝ)
    (hx : 0≤x) (hy : 0≤y) (hxy : x≤y) : e.eval x≤e.eval y := by
  induction e with
  | input i => exact hxy i
  | constant c hc => exact le_rfl
  | add a b ha hb => exact add_le_add ha hb
  | scale c hc a ha => exact mul_le_mul_of_nonneg_left ha hc
  | mul a b ha hb =>
      exact mul_le_mul ha hb (b.nonnegative x hx) (a.nonnegative y hy)
  | maximum a b ha hb => exact max_le_max ha hb

/-- In the absence of products, the expression is globally monotone, not just
monotone on the positive orthant. -/
theorem PositiveExpr.monotone_additive {ι} (e : PositiveExpr ι) (he : e.Additive)
    (x y : ι → ℝ) (hxy : x≤y) : e.eval x≤e.eval y := by
  induction e with
  | input i => exact hxy i
  | constant c hc => exact le_rfl
  | add a b ha hb => exact add_le_add (ha he.1) (hb he.2)
  | scale c hc a ha => exact mul_le_mul_of_nonneg_left (ha he) hc
  | mul a b ha hb => exact False.elim he
  | maximum a b ha hb => exact max_le_max (ha he.1) (hb he.2)

/-- Every additive expression is Jensen convex in all input coordinates. -/
theorem PositiveExpr.convex_additive {ι} (e : PositiveExpr ι) (he : e.Additive)
    (x y : ι → ℝ) (t : ℝ) (ht : 0≤t) (ht' : t≤1) :
    e.eval (fun i => t*x i+(1-t)*y i)≤t*e.eval x+(1-t)*e.eval y := by
  induction e with
  | input i => exact le_rfl
  | constant c hc => simp only [eval]; nlinarith
  | add a b ha hb =>
      have h := add_le_add (ha he.1) (hb he.2)
      simp only [eval]
      linarith
  | scale c hc a ha =>
      have h := mul_le_mul_of_nonneg_left (ha he) hc
      simp only [eval]
      nlinarith
  | mul a b ha hb => exact False.elim he
  | maximum a b ha hb =>
      exact le_trans (max_le_max (ha he.1) (hb he.2)) (max_jensen _ _ _ _ t ht ht')

/-- A polynomial built using only nonnegative constants, variables, addition
and multiplication. Thus its exponents are natural and its coefficients nonnegative. -/
inductive PositivePolynomial (ι : Type*)
  | input (i : ι)
  | constant (c : ℝ) (hc : 0≤c)
  | add (a b : PositivePolynomial ι)
  | mul (a b : PositivePolynomial ι)

noncomputable def PositivePolynomial.eval {ι} : PositivePolynomial ι → (ι → ℝ) → ℝ
  | .input i, x => x i
  | .constant c _, _ => c
  | .add a b, x => a.eval x+b.eval x
  | .mul a b, x => a.eval x*b.eval x

theorem PositivePolynomial.nonnegative {ι} (p : PositivePolynomial ι) (x : ι → ℝ) (hx : 0≤x) :
    0≤p.eval x := by
  induction p with
  | input i => exact hx i
  | constant c hc => exact hc
  | add a b ha hb => exact add_nonneg ha hb
  | mul a b ha hb => exact mul_nonneg ha hb

/-- A finite, nonempty maximum of ordinary nonnegative-coefficient polynomials. -/
inductive MaxPolynomial (ι : Type*)
  | polynomial (p : PositivePolynomial ι)
  | maximum (a b : MaxPolynomial ι)

noncomputable def MaxPolynomial.eval {ι} : MaxPolynomial ι → (ι → ℝ) → ℝ
  | .polynomial p, x => p.eval x
  | .maximum a b, x => max (a.eval x) (b.eval x)

noncomputable def MaxPolynomial.mapPoly {ι} (f : PositivePolynomial ι → PositivePolynomial ι) :
    MaxPolynomial ι → MaxPolynomial ι
  | .polynomial p => .polynomial (f p)
  | .maximum a b => .maximum (a.mapPoly f) (b.mapPoly f)

noncomputable def MaxPolynomial.bind {ι} (f : PositivePolynomial ι → MaxPolynomial ι) :
    MaxPolynomial ι → MaxPolynomial ι
  | .polynomial p => f p
  | .maximum a b => .maximum (a.bind f) (b.bind f)

noncomputable def MaxPolynomial.add {ι} (a b : MaxPolynomial ι) : MaxPolynomial ι :=
  a.bind (fun p => b.mapPoly (fun q => .add p q))

noncomputable def MaxPolynomial.mul {ι} (a b : MaxPolynomial ι) : MaxPolynomial ι :=
  a.bind (fun p => b.mapPoly (fun q => .mul p q))

theorem MaxPolynomial.nonnegative {ι} (a : MaxPolynomial ι) (x : ι → ℝ) (hx : 0≤x) :
    0≤a.eval x := by
  induction a with
  | polynomial p => exact p.nonnegative x hx
  | maximum a b ha hb => exact le_trans ha (le_max_left _ _)

theorem MaxPolynomial.add_eval {ι} (a b : MaxPolynomial ι) (x : ι → ℝ) :
    (a.add b).eval x=a.eval x+b.eval x := by
  induction a with
  | polynomial p =>
      induction b with
      | polynomial q => rfl
      | maximum b c hb hc =>
          simp only [add, bind, mapPoly, eval] at *
          rw [hb,hc]
          exact max_add_add_left _ _ _
  | maximum a c ha hc =>
      simp only [add, bind, eval] at *
      rw [ha,hc]
      exact max_add_add_right _ _ _

theorem MaxPolynomial.mul_eval {ι} (a b : MaxPolynomial ι) (x : ι → ℝ) (hx : 0≤x) :
    (a.mul b).eval x=a.eval x*b.eval x := by
  induction a with
  | polynomial p =>
      induction b with
      | polynomial q => rfl
      | maximum b c hb hc =>
          simp only [mul, bind, mapPoly, eval] at *
          rw [hb,hc]
          exact (mul_max_of_nonneg _ _ (p.nonnegative x hx)).symm
  | maximum a c ha hc =>
      simp only [mul, bind, eval] at *
      rw [ha,hc]
      exact (max_mul_of_nonneg _ _ (b.nonnegative x hx)).symm

noncomputable def PositiveExpr.polynomialMaximum {ι} : PositiveExpr ι → MaxPolynomial ι
  | .input i => .polynomial (.input i)
  | .constant c hc => .polynomial (.constant c hc)
  | .add a b => a.polynomialMaximum.add b.polynomialMaximum
  | .scale c hc a => (MaxPolynomial.polynomial (.constant c hc)).mul a.polynomialMaximum
  | .mul a b => a.polynomialMaximum.mul b.polynomialMaximum
  | .maximum a b => .maximum a.polynomialMaximum b.polynomialMaximum

/-- Hidden-monotonicity thm:monotone_maxout_main, as a constructive exact
finite maximum of polynomials, with the positive-orthant hypothesis explicit. -/
theorem PositiveExpr.max_polynomial_representation {ι} (e : PositiveExpr ι)
    (x : ι → ℝ) (hx : 0≤x) : e.polynomialMaximum.eval x=e.eval x := by
  induction e with
  | input i => rfl
  | constant c hc => rfl
  | add a b ha hb => simp only [polynomialMaximum, MaxPolynomial.add_eval, eval, ha, hb]
  | scale c hc a ha => simp only [polynomialMaximum, MaxPolynomial.mul_eval _ _ x hx,
      MaxPolynomial.eval, PositivePolynomial.eval, eval, ha]
  | mul a b ha hb => simp only [polynomialMaximum, MaxPolynomial.mul_eval _ _ x hx, eval, ha,hb]
  | maximum a b ha hb => simp only [polynomialMaximum, MaxPolynomial.eval, eval, ha,hb]

end HiddenMonotonicity
