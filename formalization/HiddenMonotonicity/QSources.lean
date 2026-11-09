import HiddenMonotonicity.OriginalTrace

namespace HiddenMonotonicity

/-- A concrete auxiliary network Q, its computed differential, and the product
of the shifts above the layer at which its minimum replaces the original ReLU. -/
structure QSource (n m : ℕ) where
  value : Vec n → Vec m
  jacobian : Vec n →L[ℝ] Vec m
  coefficient : ℝ

noncomputable def QSource.pull {n k m} (q : QSource k m)
    (f : Vec n → Vec k) (D : Vec n →L[ℝ] Vec k) : QSource n m :=
  ⟨q.value ∘ f, q.jacobian.comp D, q.coefficient⟩

noncomputable def QSource.row {n m} (q : QSource n m) (r : Row m) : Row n :=
  q.coefficient • r.comp q.jacobian

/-- One Q-network for each ReLU layer. The original network prefix is retained;
at that layer a minimum is used; the remaining tail is linear with absolute
weights and no biases. This definition permits arbitrary prefix biases. -/
noncomputable def Network.qSources {n m} : Network n m → Vec n → (ℕ → ℝ) → List (QSource n m)
  | .output _, _, _ => []
  | .layer wp wn bp bn tail, x, α =>
      ⟨fun y => tail.absCLM (minLayer wp wn bp bn y),
       tail.absCLM.comp (MaskedTrace.deadMap wp wn (originalGate wp wn bp bn x)),
       (tail.originalTrace (reluLayer wp wn bp bn x)).bulkCoefficient (fun i => α (i+1))⟩ ::
      (tail.qSources (reluLayer wp wn bp bn x) (fun i => α (i+1))).map
        (fun q => q.pull (reluLayer wp wn bp bn)
          (MaskedTrace.signedMap wp wn (originalGate wp wn bp bn x)))

/-- Every source in the closed gradient formula is the actual derivative of
its explicitly defined auxiliary Q-network, not an arbitrary row parameter. -/
theorem Network.qSources_have_derivatives {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ) :
    ∀ q ∈ net.qSources x α, HasFDerivAt q.value q.jacobian x := by
  induction net generalizing α with
  | output n => simp [Network.qSources]
  | layer wp wn bp bn tail ih =>
      intro q hq
      simp only [Network.qSources, List.mem_cons, List.mem_map] at hq
      rcases hq with hq | ⟨q',hq',rfl⟩
      · subst q
        exact tail.absCLM.hasFDerivAt.comp x (minLayer_hasFDerivAt wp wn bp bn x hx.1)
      · exact (ih _ hx.2 _ q' hq').comp x (reluLayer_hasFDerivAt wp wn bp bn x hx.1)

@[simp] theorem QSource.row_pull {n k m} (q : QSource k m)
    (f : Vec n → Vec k) (D : Vec n →L[ℝ] Vec k) (r : Row m) :
    (q.pull f D).row r = (q.row r).comp D := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

noncomputable def sourceRows {n m} (qs : List (QSource n m)) (r : Row m) : List (Row n) :=
  qs.map (fun q => q.row r)

theorem sourceRows_pull {n k m} (qs : List (QSource k m))
    (f : Vec n → Vec k) (D : Vec n →L[ℝ] Vec k) (r : Row m) :
    sourceRows (qs.map (fun q => q.pull f D)) r = (sourceRows qs r).map (fun q => q.comp D) := by
  simp [sourceRows, List.map_map]

/-- The full finite list of correction rows coincides with the derivatives of
the Q-networks, with precisely the suffix products of the shift factors. -/
theorem Network.qSources_sum {n m} (net : Network n m) (x : Vec n)
    (α : ℕ → ℝ) (r : Row m) :
    (sourceRows (net.qSources x α) r).sum = (net.originalTrace x).correction α r := by
  induction net generalizing α with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      change (QSource.row _ r :: sourceRows
        ((tail.qSources _ _).map (fun q => q.pull (reluLayer wp wn bp bn)
          (MaskedTrace.signedMap wp wn (originalGate wp wn bp bn x)))) r).sum = _
      rw [List.sum_cons, sourceRows_pull, row_sum_comp, ih]
      simp only [Network.originalTrace, MaskedTrace.correction, QSource.row]
      rw [tail.originalTrace_absCLM]
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply]
      abel

/-- Thesis thm:closed_formula_shift and eq:closed_formula_g/h, now attached to
the complete varying-width shifted backward algorithm and actual Q derivatives. -/
theorem Network.stabilized_backward_Q_closed_form {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ) (r : Row m) :
    (∀ q ∈ net.qSources x α, HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).stabilized α r true) =
      (1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac -
        (sourceRows (net.qSources x α) r).sum) ∧
    unified ((net.originalTrace x).stabilized α r false) =
      (-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac +
        (sourceRows (net.qSources x α) r).sum) := by
  refine ⟨net.qSources_have_derivatives x hx α, ?_⟩
  rw [net.qSources_sum]
  exact ⟨MaskedTrace.stabilized_backward_closed_form_g _ _ _,
    MaskedTrace.stabilized_backward_closed_form_h _ _ _⟩

/-- Source-facing backward invariant: the difference of the actual stabilized
head sensitivities is a genuine derivative of the original target logit. -/
theorem Network.stabilized_backward_invariant {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ) (r : Row m) :
    HasFDerivAt (fun y => r (net.eval y))
      (unified ((net.originalTrace x).stabilized α r true) -
       unified ((net.originalTrace x).stabilized α r false)) x := by
  rw [MaskedTrace.stabilized_backward_invariant]
  exact r.hasFDerivAt.comp x (net.hasFDerivAt_originalTrace x hx)

/-- Hidden-monotonicity thm:closed_formula, the zero-shift special case. -/
theorem Network.plain_backward_Q_closed_form {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (r : Row m) :
    (∀ q ∈ net.qSources x (fun _ => 0), HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).stabilized (fun _ => 0) r true) =
      (1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac -
        (sourceRows (net.qSources x (fun _ => 0)) r).sum) ∧
    unified ((net.originalTrace x).stabilized (fun _ => 0) r false) =
      (-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac +
        (sourceRows (net.qSources x (fun _ => 0)) r).sum) :=
  net.stabilized_backward_Q_closed_form x hx (fun _ => 0) r

/-- The literal paper Q-networks, using entrywise |W| rather than the generalized
common-mode W++W- tail. They agree for the canonical sign split. -/
noncomputable def Network.absoluteQSources {n m} : Network n m → Vec n → (ℕ → ℝ) →
    List (QSource n m)
  | .output _, _, _ => []
  | .layer wp wn bp bn tail, x, α =>
      ⟨fun y => tail.absoluteMap (minLayer wp wn bp bn y),
       tail.absoluteMap.comp (MaskedTrace.deadMap wp wn (originalGate wp wn bp bn x)),
       (tail.originalTrace (reluLayer wp wn bp bn x)).bulkCoefficient (fun i => α (i+1))⟩ ::
      (tail.absoluteQSources (reluLayer wp wn bp bn x) (fun i => α (i+1))).map
        (fun q => q.pull (reluLayer wp wn bp bn)
          (MaskedTrace.signedMap wp wn (originalGate wp wn bp bn x)))

theorem Network.qSources_eq_absolute {n m} (net : Network n m) (hc : net.Canonical)
    (x : Vec n) (α : ℕ → ℝ) : net.qSources x α = net.absoluteQSources x α := by
  induction net generalizing α with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [Network.qSources, Network.absoluteQSources, tail.absCLM_eq_absoluteMap hc.2,
        ih hc.2]

/-- Exact source-facing closed formulas, including genuine derivatives of the
literal absolute-tail Q-networks. No derivative or recurrence is assumed. -/
theorem Network.stabilized_backward_absolute_Q_closed_form {n m} (net : Network n m)
    (hc : net.Canonical) (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ) (r : Row m) :
    (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).stabilized α r true) =
      (1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x α) r).sum) ∧
    unified ((net.originalTrace x).stabilized α r false) =
      (-1/2 : ℝ) • (r.comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x α) r).sum) := by
  rw [← net.qSources_eq_absolute hc]
  exact net.stabilized_backward_Q_closed_form x hx α r

noncomputable def balancedLift (n : ℕ) : Vec n →L[ℝ] PairVec n :=
  ((1/2 : ℝ) • ContinuousLinearMap.id ℝ (Vec n)).prod
    ((-1/2 : ℝ) • ContinuousLinearMap.id ℝ (Vec n))

theorem assemble_balancedLift {n} (s : Sensitivity n) :
    (assemble s).comp (balancedLift n) = unified s := by
  apply ContinuousLinearMap.ext
  intro v
  change s.1 ((1/2 : ℝ) • v)+s.2 ((-1/2 : ℝ) • v)=
    (1/2 : ℝ)*(s.1 v-s.2 v)
  simp only [map_smul, smul_eq_mul]
  ring

theorem balancedLift_difference {n} (x : Vec n) :
    (balancedLift n x).1-(balancedLift n x).2=x := by
  funext i
  change (1/2 : ℝ)*x i-(-1/2 : ℝ)*x i=x i
  ring

/-- Eq:unified_split_gradients as an actual vector-input derivative of the
head under the symmetric lift, for the whole MLP, in both streams. -/
theorem Network.symmetric_head_derivative {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (r : Row m) (head : Bool) :
    HasFDerivAt (fun y : Vec n => if head then
      r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).1 else
      r (net.split ((1/2 : ℝ) • y) ((-1/2 : ℝ) • y)).2)
      (unified ((net.originalTrace x).stabilized (fun _ => 0) r head)) x := by
  have hs : net.Regular (balancedLift n x) :=
    (net.regular_iff_strict _).mpr (by simpa [balancedLift_difference] using hx)
  have hd := net.local_sensitivities_correct (balancedLift n x) hs r head
  have ht : net.trace (balancedLift n x)=net.originalTrace x := by
    rw [net.trace_originalTrace, balancedLift_difference]
  rw [ht] at hd
  have hc := hd.comp x (balancedLift n).hasFDerivAt
  rw [assemble_balancedLift] at hc
  exact hc

end HiddenMonotonicity
