import HiddenMonotonicity.AffineReadout

namespace HiddenMonotonicity

/-- Hidden-monotonicity thm:closed_formula, with the literal absolute Q-tail,
canonical sign parts, arbitrary widths, and actual Q derivatives. -/
theorem Network.plain_backward_absolute_Q_closed_form {n m} (net : Network n m)
    (hc : net.Canonical) (x : Vec n) (hx : net.Strict x) (r : Row m) :
    (∀ q ∈ net.absoluteQSources x (fun _ => 0), HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).stabilized (fun _ => 0) r true) =
      (1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x (fun _ => 0)) r).sum) ∧
    unified ((net.originalTrace x).stabilized (fun _ => 0) r false) =
      (-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x (fun _ => 0)) r).sum) :=
  net.stabilized_backward_absolute_Q_closed_form hc x hx (fun _ => 0) r

/-- Cor:backward_invariant and eq:backward_invariant: both separate identities,
with the actual target derivative supplied in the same theorem. -/
theorem Network.backward_partial_invariants {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ) (r : Row m) :
    HasFDerivAt (fun y => r (net.eval y)) (r.comp (net.originalTrace x).originalJac) x ∧
    ((net.originalTrace x).stabilized α r true).1-
      ((net.originalTrace x).stabilized α r false).1 = r.comp (net.originalTrace x).originalJac ∧
    ((net.originalTrace x).stabilized α r true).2-
      ((net.originalTrace x).stabilized α r false).2 = -(r.comp (net.originalTrace x).originalJac) := by
  exact ⟨r.hasFDerivAt.comp x (net.hasFDerivAt_originalTrace x hx),
    MaskedTrace.stabilized_partial_invariants _ _ _⟩

/-- The plain g/h finite-sum expressions are themselves actual head derivatives
under the symmetric input split, not merely quantities satisfying a recursion. -/
theorem Network.plain_head_gradient_formulas {n m} (net : Network n m)
    (hc : net.Canonical) (x : Vec n) (hx : net.Strict x) (r : Row m) :
    HasFDerivAt (fun y : Vec n => r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).1)
      ((1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac-
        (sourceRows (net.absoluteQSources x (fun _ => 0)) r).sum)) x ∧
    HasFDerivAt (fun y : Vec n => r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).2)
      ((-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac+
        (sourceRows (net.absoluteQSources x (fun _ => 0)) r).sum)) x := by
  have hg := net.symmetric_head_derivative x hx r true
  have hh := net.symmetric_head_derivative x hx r false
  have hcform := net.plain_backward_absolute_Q_closed_form hc x hx r
  rw [hcform.2.1] at hg
  rw [hcform.2.2] at hh
  exact ⟨hg,hh⟩

end HiddenMonotonicity
