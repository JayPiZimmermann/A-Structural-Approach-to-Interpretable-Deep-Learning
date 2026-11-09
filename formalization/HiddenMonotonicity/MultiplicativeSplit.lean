import HiddenMonotonicity.PositiveExpressions

namespace HiddenMonotonicity

/-- Signed affine/max/multiplication expressions. Powers with natural exponents
and finite-rank Maxout are obtained by finite repeated multiplication/maxima. -/
inductive SignedExpr (ι : Type*)
  | input (i : ι)
  | constant (c : ℝ)
  | add (a b : SignedExpr ι)
  | scale (c : ℝ) (a : SignedExpr ι)
  | mul (a b : SignedExpr ι)
  | maximum (a b : SignedExpr ι)

noncomputable def SignedExpr.eval {ι} : SignedExpr ι → (ι → ℝ) → ℝ
  | .input i, x => x i
  | .constant c, _ => c
  | .add a b, x => a.eval x+b.eval x
  | .scale c a, x => c*a.eval x
  | .mul a b, x => a.eval x*b.eval x
  | .maximum a b, x => max (a.eval x) (b.eval x)

/-- Constructive sign split, using only nonnegative downstream coefficients.
The Boolean input coordinate records the positive/negative input stream. -/
noncomputable def SignedExpr.split {ι} : SignedExpr ι → PositiveExpr (ι × Bool) × PositiveExpr (ι × Bool)
  | .input i => (.input (i,false),.input (i,true))
  | .constant c => (.constant (max c 0) (le_max_right _ _),
      .constant (max (-c) 0) (le_max_right _ _))
  | .add a b => (.add a.split.1 b.split.1,.add a.split.2 b.split.2)
  | .scale c a =>
      (.add (.scale (max c 0) (le_max_right _ _) a.split.1)
        (.scale (max (-c) 0) (le_max_right _ _) a.split.2),
       .add (.scale (max c 0) (le_max_right _ _) a.split.2)
        (.scale (max (-c) 0) (le_max_right _ _) a.split.1))
  | .mul a b =>
      (.add (.mul a.split.1 b.split.1) (.mul a.split.2 b.split.2),
       .add (.mul a.split.1 b.split.2) (.mul a.split.2 b.split.1))
  | .maximum a b =>
      (.maximum (.add a.split.1 b.split.2) (.add b.split.1 a.split.2),
       .add a.split.2 b.split.2)

theorem max_two_split_pairs (p n q r : ℝ) :
    max (p+r) (q+n)-(n+r)=max (p-n) (q-r) := by
  rcases le_total (p-n) (q-r) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : p+r≤q+n)]
    ring
  · rw [max_eq_left h, max_eq_left (by linarith : q+n≤p+r)]
    ring

/-- Exact splitting for all signed inputs, without a convexity claim. -/
theorem SignedExpr.split_correct {ι} (e : SignedExpr ι) (z : ι × Bool → ℝ) :
    e.split.1.eval z-e.split.2.eval z=e.eval (fun i => z (i,false)-z (i,true)) := by
  induction e with
  | input i => rfl
  | constant c => exact (canonical_weight_split c).1
  | add a b ha hb =>
      simp only [split, PositiveExpr.eval, eval]
      linarith
  | scale c a ha =>
      simp only [split, PositiveExpr.eval, eval]
      calc
        _ = (max c 0-max (-c) 0)*(a.split.1.eval z-a.split.2.eval z) := by ring
        _ = _ := by rw [(canonical_weight_split c).1,ha]
  | mul a b ha hb =>
      simp only [split, PositiveExpr.eval, eval]
      rw [multiplicative_split_correct,ha,hb]
  | maximum a b ha hb =>
      simp only [split, PositiveExpr.eval, eval]
      rw [max_two_split_pairs,ha,hb]

noncomputable def canonicalSplitInput {ι} (x : ι → ℝ) : ι × Bool → ℝ :=
  fun i => if i.2 then max (-x i.1) 0 else max (x i.1) 0

theorem canonicalSplitInput_nonnegative {ι} (x : ι → ℝ) : 0≤canonicalSplitInput x := by
  intro i
  change (0 : ℝ) ≤ if i.2 then max (-x i.1) 0 else max (x i.1) 0
  cases i.2 <;> exact le_max_right _ (0 : ℝ)

theorem canonicalSplitInput_difference {ι} (x : ι → ℝ) (i : ι) :
    canonicalSplitInput x (i,false)-canonicalSplitInput x (i,true)=x i :=
  (canonical_weight_split (x i)).1

/-- Hidden-monotonicity thm:main/main_simplified: the original expression is
the exact difference of two downstream monotone nonnegative-weight expressions. -/
theorem SignedExpr.monotone_split_representation {ι} (e : SignedExpr ι) (x : ι → ℝ) :
    e.eval x=e.split.1.eval (canonicalSplitInput x)-e.split.2.eval (canonicalSplitInput x) := by
  rw [e.split_correct]
  congr 1
  funext i
  exact (canonicalSplitInput_difference x i).symm

/-- Constructive maximum-of-polynomials representation of both exact streams.
Each maximum is finite, and every polynomial has nonnegative coefficients and
natural exponents. The positive-orthant restriction is explicit in the evaluation. -/
theorem SignedExpr.max_polynomial_split {ι} (e : SignedExpr ι) (x : ι → ℝ) :
    e.eval x=e.split.1.polynomialMaximum.eval (canonicalSplitInput x)-
      e.split.2.polynomialMaximum.eval (canonicalSplitInput x) := by
  rw [PositiveExpr.max_polynomial_representation _ _ (canonicalSplitInput_nonnegative x),
    PositiveExpr.max_polynomial_representation _ _ (canonicalSplitInput_nonnegative x)]
  exact e.monotone_split_representation x

/-- Both constructed streams are monotone in the nonnegative split inputs. -/
theorem SignedExpr.split_streams_monotone {ι} (e : SignedExpr ι)
    (x y : ι × Bool → ℝ) (hx : 0≤x) (hy : 0≤y) (hxy : x≤y) :
    e.split.1.eval x≤e.split.1.eval y ∧ e.split.2.eval x≤e.split.2.eval y :=
  ⟨e.split.1.monotone_nonnegative x y hx hy hxy,
   e.split.2.monotone_nonnegative x y hx hy hxy⟩

end HiddenMonotonicity
