import HiddenMonotonicity.PolynomialSemantics
import HiddenMonotonicity.CircuitStatements

namespace HiddenMonotonicity

noncomputable def MaxPolynomial.leaves {ι} : MaxPolynomial ι → List (PositivePolynomial ι)
  | .polynomial p => [p]
  | .maximum a b => a.leaves++b.leaves

theorem MaxPolynomial.leaves_nonempty {ι} (e : MaxPolynomial ι) : e.leaves≠[] := by
  induction e with
  | polynomial p => simp [leaves]
  | maximum a b ha hb => simp [leaves,ha]

noncomputable def foldMax (xs : List ℝ) : ℝ := xs.foldr max 0

theorem foldMax_nonnegative (xs : List ℝ) : 0≤foldMax xs := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact le_trans ih (le_max_right _ _)

theorem foldMax_append (xs ys : List ℝ) : foldMax (xs++ys)=max (foldMax xs) (foldMax ys) := by
  induction xs with
  | nil => simpa [foldMax] using (max_eq_right (foldMax_nonnegative ys)).symm
  | cons x xs ih => simpa only [List.cons_append,foldMax,List.foldr_cons] using
      (show max x (foldMax (xs++ys))=max (max x (foldMax xs)) (foldMax ys) by rw [ih,max_assoc])

theorem MaxPolynomial.eval_leaves {ι} (e : MaxPolynomial ι) (x : ι → ℝ) (hx : 0≤x) :
    e.eval x=foldMax (e.leaves.map (fun p => p.eval x)) := by
  induction e with
  | polynomial p =>
      simpa [leaves,foldMax,MaxPolynomial.eval] using (max_eq_left (p.nonnegative x hx)).symm
  | maximum a b ha hb => simp only [leaves,List.map_append,foldMax_append,MaxPolynomial.eval,ha,hb]

/-- An explicit nonempty finite list of ordinary MvPolynomials witnesses the
maximum representation, with every coefficient nonnegative. -/
theorem MaxPolynomial.ordinary_finite_polynomial_witness {ι} (e : MaxPolynomial ι) :
    ∃ ps : List (MvPolynomial ι ℝ), ps≠[] ∧
      (∀ p∈ps, ∀ d : ι →₀ ℕ, 0≤p.coeff d) ∧
      ∀ x : ι → ℝ, 0≤x → e.eval x=foldMax (ps.map (MvPolynomial.eval x)) := by
  refine ⟨e.leaves.map PositivePolynomial.toMvPolynomial, ?_, ?_, ?_⟩
  · simpa using e.leaves_nonempty
  · intro p hp d
    simp only [List.mem_map] at hp
    rcases hp with ⟨q,hq,rfl⟩
    exact q.coefficients_nonnegative d
  · intro x hx
    rw [e.eval_leaves x hx]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro p hp
    exact (p.toMvPolynomial_eval x).symm

/-- Both streams of the actual split computation graph have ordinary finite
polynomial witnesses; the same graph correctness theorem links their difference
to the original model. -/
theorem Circuit.ordinary_polynomial_stream_witnesses {d n} (c : Circuit d n) (i : Fin n) :
    (∃ ps : List (MvPolynomial (Fin d × Bool) ℝ), ps≠[] ∧
      (∀ p∈ps, ∀ a : (Fin d × Bool) →₀ ℕ, 0≤p.coeff a) ∧
      ∀ x : Fin d × Bool → ℝ, 0≤x →
        (c.split false x).1 i=foldMax (ps.map (MvPolynomial.eval x))) ∧
    (∃ ps : List (MvPolynomial (Fin d × Bool) ℝ), ps≠[] ∧
      (∀ p∈ps, ∀ a : (Fin d × Bool) →₀ ℕ, 0≤p.coeff a) ∧
      ∀ x : Fin d × Bool → ℝ, 0≤x →
        (c.split false x).2 i=foldMax (ps.map (MvPolynomial.eval x))) := by
  rcases (c.positiveExpressions.1 i).polynomialMaximum.ordinary_finite_polynomial_witness with
    ⟨ps,hps,hcoeff,hvalue⟩
  rcases (c.positiveExpressions.2 i).polynomialMaximum.ordinary_finite_polynomial_witness with
    ⟨qs,hqs,hqcoeff,hqvalue⟩
  refine ⟨⟨ps,hps,hcoeff,?_⟩,⟨qs,hqs,hqcoeff,?_⟩⟩
  · intro x hx
    rw [(c.max_polynomial_streams x hx i).1]
    exact hvalue x hx
  · intro x hx
    rw [(c.max_polynomial_streams x hx i).2]
    exact hqvalue x hx

end HiddenMonotonicity
