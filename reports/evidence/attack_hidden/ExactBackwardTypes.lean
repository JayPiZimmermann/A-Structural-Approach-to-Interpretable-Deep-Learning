import HiddenMonotonicity.BackwardStatements

open HiddenMonotonicity

-- Expected types independently reviewed against the unfolded objects.
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ) (r : Row m),
    (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).stabilized α r true) =
      (1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x α) r).sum) ∧
    unified ((net.originalTrace x).stabilized α r false) =
      (-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x α) r).sum) :=
  @Network.stabilized_backward_absolute_Q_closed_form

example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (hx : net.Strict x) (r : Row m),
    HasFDerivAt (fun y : Vec n => r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).1)
      ((1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac-
        (sourceRows (net.absoluteQSources x (fun _ => 0)) r).sum)) x ∧
    HasFDerivAt (fun y : Vec n => r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).2)
      ((-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac+
        (sourceRows (net.absoluteQSources x (fun _ => 0)) r).sum)) x :=
  @Network.plain_head_gradient_formulas

example : ∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x)
    (α : ℕ → ℝ) (r : Row m),
    HasFDerivAt (fun y => r (net.eval y)) (r.comp (net.originalTrace x).originalJac) x ∧
    ((net.originalTrace x).stabilized α r true).1-
      ((net.originalTrace x).stabilized α r false).1 = r.comp (net.originalTrace x).originalJac ∧
    ((net.originalTrace x).stabilized α r true).2-
      ((net.originalTrace x).stabilized α r false).2 = -(r.comp (net.originalTrace x).originalJac) :=
  @Network.backward_partial_invariants

example : ∀ {n m : ℕ} (net : Network n m) (x : Vec n) (hx : net.Strict x)
    (α : ℕ → ℝ) (r : Row m),
    HasFDerivAt (fun y => r (net.eval y))
      (unified ((net.originalTrace x).stabilized α r true) -
       unified ((net.originalTrace x).stabilized α r false)) x :=
  @Network.stabilized_backward_invariant

example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ)
    (rPlus rMinus : Row m) (β : ℝ),
    (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β true)) =
      (1/2 : ℝ) • ((rPlus-rMinus).comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rPlus+rMinus))).sum) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β false)) =
      (-1/2 : ℝ) • ((rPlus-rMinus).comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rPlus+rMinus))).sum) :=
  @Network.affine_readout_closed_form

#check @Network.correct
#check @Network.shift
#check @Network.qSources_have_derivatives
#check @Network.qSources_eq_absolute
#check @Network.stabilized_backward_absolute_Q_closed_form
#check @Network.plain_head_gradient_formulas
#check @Network.backward_partial_invariants
#check @Network.stabilized_backward_invariant
#check @Network.affine_readout_closed_form
#check @Network.affine_logit_derivative
#check @MaskedTrace.run_zero_actual
#check @MaskedTrace.bulkCoefficient_product
#check @MaskedTrace.stabilized_partial_invariants
#print axioms Network.stabilized_backward_absolute_Q_closed_form
#print axioms Network.plain_head_gradient_formulas
#print axioms Network.backward_partial_invariants
#print axioms Network.stabilized_backward_invariant
#print axioms Network.affine_readout_closed_form
#print axioms Network.affine_logit_derivative
