import HiddenMonotonicity.AffineReadout

namespace HiddenMonotonicity
open scoped BigOperators

/-- Actual ungated affine split heads, including both readout biases. -/
noncomputable def Network.affineHeads {n m} (net : Network n m)
    (rp rn : Row m) (bp bn : ℝ) (x : PairVec n) : ℝ × ℝ :=
  let s := net.split x.1 x.2
  (rp s.1 + rn s.2 + bp, rn s.1 + rp s.2 + bn)

noncomputable def Network.affineLogit {n m} (net : Network n m)
    (rp rn : Row m) (bp bn : ℝ) (x : Vec n) : ℝ :=
  (rp-rn) (net.eval x) + (bp-bn)

theorem Network.affine_heads_recovery {n m} (net : Network n m)
    (rp rn : Row m) (bp bn : ℝ) (x : PairVec n) :
    (net.affineHeads rp rn bp bn x).1 - (net.affineHeads rp rn bp bn x).2 =
      net.affineLogit rp rn bp bn (x.1-x.2) := by
  unfold affineHeads affineLogit
  rw [← net.correct x.1 x.2]
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  ring

/-- The zero-shift terminal seed differentiates the actual affine head. No
ReLU, gate, or minimum source is inserted after the final affine operation. -/
theorem Network.affine_head_derivative {n m} (net : Network n m)
    (x : PairVec n) (hx : net.Strict (x.1-x.2))
    (rp rn : Row m) (bp bn : ℝ) (head : Bool) :
    HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn y).1
      else (net.affineHeads rp rn bp bn y).2)
      (assemble ((net.originalTrace (x.1-x.2)).run (fun _ => 0)
        (affineReadoutSeed rp rn 0 head))) x := by
  have hd := net.hasFDerivAt_split x ((net.regular_iff_strict x).mpr hx)
  rw [net.jacobian_trace, net.trace_originalTrace] at hd
  rw [MaskedTrace.run_zero_actual]
  cases head
  · simpa [affineHeads, affineReadoutSeed, shiftPair, assemble, Function.comp_def]
      using ((assemble (rn,rp)).hasFDerivAt.comp x hd).add_const bn
  · simpa [affineHeads, affineReadoutSeed, shiftPair, assemble, Function.comp_def]
      using ((assemble (rp,rn)).hasFDerivAt.comp x hd).add_const bp

theorem Network.affine_symmetric_head_derivative {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (rp rn : Row m) (bp bn : ℝ) (head : Bool) :
    HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn (balancedLift n y)).1
      else (net.affineHeads rp rn bp bn (balancedLift n y)).2)
      (unified ((net.originalTrace x).run (fun _ => 0)
        (affineReadoutSeed rp rn 0 head))) x := by
  have hd := net.affine_head_derivative (balancedLift n x)
    (by simpa only [balancedLift_difference] using hx) rp rn bp bn head
  rw [balancedLift_difference] at hd
  simpa only [assemble_balancedLift, Function.comp_def] using hd.comp x (balancedLift n).hasFDerivAt

/-- Both affine-readout partial invariants, for arbitrary constant shifts. -/
theorem MaskedTrace.affine_partial_invariants {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (rp rn : Row m) (β : ℝ) :
    (tr.run α (affineReadoutSeed rp rn β true)).1 -
      (tr.run α (affineReadoutSeed rp rn β false)).1 = (rp-rn).comp tr.originalJac ∧
    (tr.run α (affineReadoutSeed rp rn β true)).2 -
      (tr.run α (affineReadoutSeed rp rn β false)).2 = -((rp-rn).comp tr.originalJac) := by
  have hs : (tr.run α (affineReadoutSeed rp rn β true)).1 +
      (tr.run α (affineReadoutSeed rp rn β true)).2 =
      (tr.run α (affineReadoutSeed rp rn β false)).1 +
      (tr.run α (affineReadoutSeed rp rn β false)).2 := by
    rw [tr.run_bulk, tr.run_bulk]
    simp only [affineReadoutSeed, ite_true, Bool.false_eq_true, ite_false, shiftPair_sum]
    rw [add_comm rn rp]
  have hu : unified (tr.run α (affineReadoutSeed rp rn β true)) -
      unified (tr.run α (affineReadoutSeed rp rn β false)) = (rp-rn).comp tr.originalJac := by
    rw [tr.run_unified, tr.run_unified]
    simp only [affineReadoutSeed, ite_true, Bool.false_eq_true, ite_false,
      unified_shift, shiftPair_sum]
    rw [add_comm rn rp]
    ext v
    simp only [unified, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  constructor <;> ext v
  · have hs' := congrArg (fun R : Row n => R v) hs
    have hu' := congrArg (fun R : Row n => R v) hu
    simp only [unified, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at hs' hu' ⊢
    linarith
  · have hs' := congrArg (fun R : Row n => R v) hs
    have hu' := congrArg (fun R : Row n => R v) hu
    simp only [unified, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul] at hs' hu' ⊢
    linarith

/-- The derivative and both partial identities refer to the same affine logit. -/
theorem Network.affine_backward_invariants {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ)
    (rp rn : Row m) (bp bn β : ℝ) :
    HasFDerivAt (net.affineLogit rp rn bp bn)
      ((rp-rn).comp (net.originalTrace x).originalJac) x ∧
    ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).1 -
      ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).1 =
        (rp-rn).comp (net.originalTrace x).originalJac ∧
    ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).2 -
      ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).2 =
        (rp-rn).comp (net.originalTrace x).originalJac := by
  refine ⟨net.affine_logit_derivative x hx rp rn (bp-bn), ?_, ?_⟩
  · exact ((net.originalTrace x).affine_partial_invariants α rp rn β).1
  · have h := ((net.originalTrace x).affine_partial_invariants α rp rn β).2
    rw [← neg_sub, h, neg_neg]

/-- Plain Q-source formulas are actual derivatives of the final affine heads.
The Q list contains only the ReLU backbone, never a final affine minimum. -/
theorem Network.affine_plain_head_formulas {n m} (net : Network n m)
    (hc : net.Canonical) (x : Vec n) (hx : net.Strict x)
    (rp rn : Row m) (bp bn : ℝ) :
    HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1)
      ((1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x ∧
    HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2)
      ((-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x := by
  have hg := net.affine_symmetric_head_derivative x hx rp rn bp bn true
  have hh := net.affine_symmetric_head_derivative x hx rp rn bp bn false
  have hf := net.affine_readout_closed_form hc x hx (fun _ => 0) rp rn 0
  simp only [mul_zero, sub_zero, one_smul] at hf
  rw [hf.2.1] at hg
  rw [hf.2.2] at hh
  exact ⟨hg, hh⟩

/-- A coefficient row, exposing the literal entrywise sign split at readout. -/
noncomputable def coefficientRow {m} (w : Vec m) : Row m :=
  ∑ i, w i • ContinuousLinearMap.proj i

@[simp] theorem coefficientRow_apply {m} (w x : Vec m) :
    coefficientRow w x = ∑ i, w i*x i := by
  simp [coefficientRow, ContinuousLinearMap.sum_apply]

theorem coefficientRow_sign_sum {m} (w : Vec m) :
    coefficientRow (fun i => max (w i) 0) + coefficientRow (fun i => max (-w i) 0) =
      coefficientRow (fun i => |w i|) := by
  ext x
  simp only [ContinuousLinearMap.add_apply, coefficientRow_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_mul, (canonical_weight_split (w i)).2]

theorem coefficientRow_sign_difference {m} (w : Vec m) :
    coefficientRow (fun i => max (w i) 0) - coefficientRow (fun i => max (-w i) 0) =
      coefficientRow w := by
  ext x
  simp only [ContinuousLinearMap.sub_apply, coefficientRow_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_mul, (canonical_weight_split (w i)).1]

theorem coefficientRow_nonnegative {m} (w x : Vec m) (hw : 0≤w) (hx : 0≤x) :
    0≤coefficientRow w x := by
  rw [coefficientRow_apply]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hx i))

/-- Literal absolute mass of the final canonical affine row and backbone. -/
theorem Network.affine_canonical_mass {n m} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (w : Vec m) (head : Bool) :
    ((net.originalTrace x).run (fun _ => 0)
      (affineReadoutSeed (coefficientRow (fun i => max (w i) 0))
        (coefficientRow (fun i => max (-w i) 0)) 0 head)).1 +
    ((net.originalTrace x).run (fun _ => 0)
      (affineReadoutSeed (coefficientRow (fun i => max (w i) 0))
        (coefficientRow (fun i => max (-w i) 0)) 0 head)).2 =
      (coefficientRow (fun i => |w i|)).comp net.absoluteMap := by
  rw [MaskedTrace.run_bulk, MaskedTrace.bulkCoefficient_zero,
    net.originalTrace_absCLM, net.absCLM_eq_absoluteMap hc]
  simp only [one_smul, affineReadoutSeed, shiftPair_sum, mul_zero, sub_zero]
  cases head <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · rw [add_comm, coefficientRow_sign_sum]
  · rw [coefficientRow_sign_sum]

end HiddenMonotonicity
