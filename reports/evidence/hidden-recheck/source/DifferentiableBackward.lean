import HiddenMonotonicity.PrefixSources

namespace HiddenMonotonicity
open MeasureTheory

/-- The implemented shifted algorithm has these finite Q-row formulas at every
input. The theorem deliberately distinguishes selected rows from actual Q
derivatives; the following almost-everywhere theorem supplies that connection. -/
theorem Network.affine_Q_row_formulas {n m} (net : Network n m)
    (hc : net.Canonical) (x : Vec n) (α : ℕ → ℝ) (rp rn : Row m) (β : ℝ) :
    unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)) =
      (1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)) =
      (-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum) := by
  constructor
  · rw [MaskedTrace.run_unified]
    simp only [affineReadoutSeed, ite_true]
    rw [unified_shift, shiftPair_sum]
    simp only [unified]
    rw [← net.qSources_eq_absolute hc, net.qSources_sum]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul]
    ring
  · rw [MaskedTrace.run_unified]
    simp only [affineReadoutSeed, Bool.false_eq_true, ite_false]
    rw [unified_shift, shiftPair_sum]
    simp only [unified]
    rw [add_comm rn rp, ← net.qSources_eq_absolute hc, net.qSources_sum]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
    ring

/-- Actual plain-head gradient formulas at every point of head differentiability.
Q rows are selected derivatives here; actual individual Q derivatives are
certified simultaneously almost everywhere by affine_Q_closed_form_ae. -/
theorem Network.affine_plain_formulas_of_differentiable {n m} (net : Network n m)
    (hc : net.Canonical) (x : Vec n) (rp rn : Row m)
    (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ)
    (hg : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1) x)
    (hh : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2) x) :
    HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1)
      ((1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x ∧
    HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2)
      ((-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x := by
  have dg := net.affine_symmetric_derivative_of_differentiable (net.canonical_nonnegative hc)
    x rp rn hp hn bp bn true hg
  have dh := net.affine_symmetric_derivative_of_differentiable (net.canonical_nonnegative hc)
    x rp rn hp hn bp bn false hh
  have h := net.affine_Q_row_formulas hc x (fun _ => 0) rp rn 0
  simp only [mul_zero, sub_zero, one_smul] at h
  rw [h.1] at dg
  rw [h.2] at dh
  exact ⟨dg,dh⟩

/-- Full source-facing affine-logit Q theorem almost everywhere: each actual
auxiliary Q derivative, the actual signed-logit derivative, and both shifted
finite-sum formulas. The final affine readout contributes no minimum source. -/
theorem Network.affine_Q_closed_form_ae {n m} (net : Network n m)
    (hc : net.Canonical) (α : ℕ → ℝ) (rp rn : Row m) (bp bn β : ℝ) :
    ∀ᵐ x : Vec n,
      (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
      HasFDerivAt (net.affineLogit rp rn bp bn) ((rp-rn).comp (net.originalTrace x).originalJac) x ∧
      unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)) =
        (1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac -
          (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum) ∧
      unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)) =
        (-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac +
          (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum) := by
  filter_upwards [net.absoluteQSources_ae_derivatives hc α,
    net.originalTrace_ae_derivative (net.canonical_nonnegative hc)] with x hq hx
  exact ⟨hq, ((rp-rn).hasFDerivAt.comp x hx).add_const (bp-bn),
    net.affine_Q_row_formulas hc x α rp rn β⟩

/-- The plain closed formula simultaneously differentiates both actual heads
and every actual Q-network on a full-measure set, without strict gates. -/
theorem Network.affine_plain_Q_gradients_ae {n m} (net : Network n m)
    (hc : net.Canonical) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ) :
    ∀ᵐ x : Vec n,
      (∀ q ∈ net.absoluteQSources x (fun _ => 0), HasFDerivAt q.value q.jacobian x) ∧
      HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1)
        ((1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac -
          (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x ∧
      HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2)
        ((-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac +
          (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x := by
  filter_upwards [net.absoluteQSources_ae_derivatives hc (fun _ => 0),
    net.affine_heads_ae_derivatives (net.canonical_nonnegative hc) rp rn hp hn bp bn] with x hq hh
  exact ⟨hq, net.affine_plain_formulas_of_differentiable hc x rp rn hp hn bp bn
    (hh true).differentiableAt (hh false).differentiableAt⟩

end HiddenMonotonicity
