import HiddenMonotonicity.Circuit
import HiddenMonotonicity.PolynomialSemantics

namespace HiddenMonotonicity

/-- Source thm:cnn_split_correct, all nodes of the actual topological split
pass, including optional common min re-centering. -/
theorem Circuit.cnn_split_correct {d n} (c : Circuit d n) (center : Bool)
    (x : Fin d × Bool → ℝ) (hx : 0≤x) :
    (0≤(c.split center x).1 ∧ 0≤(c.split center x).2) ∧
    ∀ i, (c.split center x).1 i-(c.split center x).2 i=
      c.eval (fun j => x (j,false)-x (j,true)) i := by
  refine ⟨c.split_nonnegative center x hx,?_⟩
  intro i
  exact congrFun (c.split_correct center x) i

/-- The additional convexity/monotonicity conclusion in the corrected CNN
statement, explicitly excluding both multiplication and re-centering. -/
theorem Circuit.cnn_stream_properties {d n} (c : Circuit d n) (hc : c.Additive) :
    (∀ x y : Fin d × Bool → ℝ, x≤y → ∀ i,
      (c.split false x).1 i≤(c.split false y).1 i ∧
      (c.split false x).2 i≤(c.split false y).2 i) ∧
    (∀ (x y : Fin d × Bool → ℝ) (t : ℝ), 0≤t → t≤1 → ∀ i,
      (c.split false (fun a => t*x a+(1-t)*y a)).1 i≤
        t*(c.split false x).1 i+(1-t)*(c.split false y).1 i ∧
      (c.split false (fun a => t*x a+(1-t)*y a)).2 i≤
        t*(c.split false x).2 i+(1-t)*(c.split false y).2 i) :=
  ⟨fun x y hxy i => c.cnn_split_monotone hc x y hxy i,
    fun x y t ht ht' i => c.cnn_split_convex hc x y t ht ht' i⟩

/-- Source thm:main/main_simplified, with DAG sharing, residual access to old
nodes and natural product operations. The witnesses use only rank-2 maxima
and nonnegative arithmetic. This theorem does not claim convexity or a size bound. -/
theorem Circuit.maxout_multiplication_split_correct {d n} (c : Circuit d n)
    (x : Vec d) (i : Fin n) :
    c.eval x i=(c.positiveExpressions.1 i).polynomialMaximum.eval (canonicalSplitInput x)-
      (c.positiveExpressions.2 i).polynomialMaximum.eval (canonicalSplitInput x) := by
  have hd := congrFun (c.split_correct false (canonicalSplitInput x)) i
  have he : (fun j => canonicalSplitInput x (j,false)-canonicalSplitInput x (j,true))=x := by
    funext j
    exact canonicalSplitInput_difference x j
  rw [he] at hd
  have hp := c.max_polynomial_streams (canonicalSplitInput x) (canonicalSplitInput_nonnegative x) i
  simp only [Pi.sub_apply] at hd
  rw [hp.1,hp.2] at hd
  exact hd.symm

/-- Both split DAG streams remain monotone on nonnegative split inputs even
when multiplication is present. -/
theorem Circuit.multiplicative_streams_monotone {d n} (c : Circuit d n)
    (x y : Fin d × Bool → ℝ) (hx : 0≤x) (hy : 0≤y) (hxy : x≤y) (i : Fin n) :
    (c.split false x).1 i≤(c.split false y).1 i ∧
    (c.split false x).2 i≤(c.split false y).2 i := by
  have hg := (c.positiveExpressions.1 i).monotone_nonnegative x y hx hy hxy
  have hh := (c.positiveExpressions.2 i).monotone_nonnegative x y hx hy hxy
  simp only [congrFun (c.positiveExpressions_eval _).1 i,
    congrFun (c.positiveExpressions_eval _).2 i] at hg hh
  exact ⟨hg,hh⟩

noncomputable def SignedExpr.pow {ι} (e : SignedExpr ι) : ℕ → SignedExpr ι
  | 0 => .constant 1
  | n+1 => .mul (e.pow n) e

theorem SignedExpr.pow_eval {ι} (e : SignedExpr ι) (n : ℕ) (x : ι → ℝ) :
    (e.pow n).eval x=e.eval x ^ n := by
  induction n with
  | zero => simp [SignedExpr.pow,SignedExpr.eval]
  | succ n ih => simp [SignedExpr.pow,SignedExpr.eval,ih,pow_succ]

noncomputable def SignedExpr.maxList {ι} (first : SignedExpr ι) : List (SignedExpr ι) → SignedExpr ι
  | [] => first
  | e::es => .maximum e (SignedExpr.maxList first es)

theorem SignedExpr.maxList_eval {ι} (first : SignedExpr ι) (es : List (SignedExpr ι)) (x : ι → ℝ) :
    (SignedExpr.maxList first es).eval x=es.foldr (fun e a => max (e.eval x) a) (first.eval x) := by
  induction es <;> simp_all [SignedExpr.maxList,SignedExpr.eval]

/-- Finite matrix/Hadamard products are ordinary supported graph operations. -/
noncomputable def SignedExpr.dot {ι k} (a b : Fin k → SignedExpr ι) : SignedExpr ι :=
  SignedExpr.sum (List.ofFn (fun i => .mul (a i) (b i)))

theorem SignedExpr.dot_eval {ι k} (a b : Fin k → SignedExpr ι) (x : ι → ℝ) :
    (SignedExpr.dot a b).eval x=∑ i,(a i).eval x*(b i).eval x := by
  simp [SignedExpr.dot,SignedExpr.sum_eval,List.map_ofFn,List.sum_ofFn,Function.comp_def,SignedExpr.eval]

end HiddenMonotonicity
