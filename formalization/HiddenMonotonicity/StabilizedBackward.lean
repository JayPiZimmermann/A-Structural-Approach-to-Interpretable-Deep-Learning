import HiddenMonotonicity.MaskedTrace

namespace HiddenMonotonicity
abbrev Row (n : ℕ) := Vec n →L[ℝ] ℝ
abbrev Sensitivity (n : ℕ) := Row n × Row n

noncomputable def assemble {n} (s : Sensitivity n) : PairVec n →L[ℝ] ℝ :=
  s.1.comp (ContinuousLinearMap.fst ℝ (Vec n) (Vec n)) +
  s.2.comp (ContinuousLinearMap.snd ℝ (Vec n) (Vec n))

noncomputable def partialPair {n} (D : PairVec n →L[ℝ] ℝ) : Sensitivity n :=
  (D.comp ((ContinuousLinearMap.id ℝ (Vec n)).prod 0),
   D.comp ((0 : Vec n →L[ℝ] Vec n).prod (ContinuousLinearMap.id ℝ (Vec n))))

noncomputable def shiftPair {n} (α : ℝ) (s : Sensitivity n) : Sensitivity n :=
  (s.1 - α • (s.1+s.2), s.2 - α • (s.1+s.2))

noncomputable def unified {n} (s : Sensitivity n) : Row n := (1/2 : ℝ) • (s.1-s.2)

namespace MaskedTrace

noncomputable def pull {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (gate : Fin k → Bool) (s : Sensitivity k) : Sensitivity n :=
  partialPair ((assemble s).comp (splitLayerJac wp wn gate))

noncomputable def absMap {n m} : MaskedTrace n m → (Vec n →L[ℝ] Vec m)
  | .output _ => ContinuousLinearMap.id ℝ _
  | .layer wp wn _ tail => tail.absMap.comp (matrixCLM (wp+wn))

/-- Every layer, including the output layer, is shifted once. α is indexed
from the input of this tail; shifting it by one supplies the next layer. -/
noncomputable def stabilized {n m} : MaskedTrace n m → (ℕ → ℝ) →
    Row m → Bool → Sensitivity n
  | .output _, α, r, head => shiftPair (α 0) (if head then (r,0) else (0,r))
  | .layer wp wn gate tail, α, r, head =>
      shiftPair (α 0) (pull wp wn gate (tail.stabilized (fun i => α (i+1)) r head))

def bulkCoefficient {n m} : MaskedTrace n m → (ℕ → ℝ) → ℝ
  | .output _, α => 1-2*α 0
  | .layer _ _ _ tail, α => (1-2*α 0)*tail.bulkCoefficient (fun i => α (i+1))

noncomputable def correction {n m} : MaskedTrace n m → (ℕ → ℝ) → Row m → Row n
  | .output _, _, _ => 0
  | .layer wp wn gate tail, α, r =>
      (tail.correction (fun i => α (i+1)) r).comp (signedMap wp wn gate) +
      tail.bulkCoefficient (fun i => α (i+1)) •
        ((r.comp tail.absMap).comp (deadMap wp wn gate))

end MaskedTrace

theorem assemble_partialPair {n} (D : PairVec n →L[ℝ] ℝ) : assemble (partialPair D) = D := by
  apply ContinuousLinearMap.ext
  intro x
  change D (x.1,0)+D (0,x.2)=D x
  rw [← map_add]
  congr 1
  simp

theorem shiftPair_sum {n} (α : ℝ) (s : Sensitivity n) :
    (shiftPair α s).1+(shiftPair α s).2 = (1-2*α) • (s.1+s.2) := by
  simp only [shiftPair]
  module

theorem unified_shift {n} (α : ℝ) (s : Sensitivity n) : unified (shiftPair α s) = unified s := by
  simp only [unified, shiftPair]
  congr 1
  abel

theorem MaskedTrace.splitLayer_common {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (gate : Fin k → Bool) (v : Vec n) :
    splitLayerJac wp wn gate (v,v) = (matrixCLM (wp+wn) v,matrixCLM (wp+wn) v) := by
  apply Prod.ext
  · funext i
    change (activeMap gate (preP wp wn (v,v))) i +
      (inactiveMap gate (preN wp wn (v,v))) i = _
    simp only [activeMap_apply, inactiveMap_apply, preP_apply, preN, Pi.add_apply]
    change (if gate i then (wp.mulVec v+wn.mulVec v) i else 0) +
      (if gate i then 0 else (wn.mulVec v+wp.mulVec v) i) = ((wp+wn).mulVec v) i
    rw [Matrix.add_mulVec]
    cases gate i <;> simp [add_comm]
  · change (wn.mulVec v+wp.mulVec v) = (wp+wn).mulVec v
    rw [Matrix.add_mulVec, add_comm]

theorem MaskedTrace.splitLayer_signed {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (gate : Fin k → Bool) (v : Vec n) :
    splitLayerJac wp wn gate (v,-v) =
      (signedMap wp wn gate v-deadMap wp wn gate v,
       -signedMap wp wn gate v-deadMap wp wn gate v) := by
  apply Prod.ext
  · funext i
    change (activeMap gate (preP wp wn (v,-v))) i +
      (inactiveMap gate (preN wp wn (v,-v))) i = _
    simp only [signedMap, deadMap, ContinuousLinearMap.comp_apply,
      activeMap_apply, inactiveMap_apply, Pi.sub_apply]
    change (if gate i then (wp.mulVec v+wn.mulVec (-v)) i else 0) +
      (if gate i then 0 else (wn.mulVec v+wp.mulVec (-v)) i) =
      (if gate i then ((wp-wn).mulVec v) i else 0) -
      (if gate i then 0 else ((wp-wn).mulVec v) i)
    simp only [Matrix.sub_mulVec, Matrix.mulVec_neg, Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
    cases gate i <;> simp <;> ring
  · funext i
    change (wn.mulVec v+wp.mulVec (-v)) i = _
    simp only [signedMap, deadMap, ContinuousLinearMap.comp_apply,
      activeMap_apply, inactiveMap_apply, Pi.sub_apply, Pi.neg_apply]
    change (wn.mulVec v+wp.mulVec (-v)) i =
      -(if gate i then ((wp-wn).mulVec v) i else 0) -
      (if gate i then 0 else ((wp-wn).mulVec v) i)
    simp only [Matrix.sub_mulVec, Matrix.mulVec_neg, Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
    cases gate i <;> simp <;> ring

theorem MaskedTrace.pull_sum {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (gate : Fin k → Bool) (s : Sensitivity k) :
    (pull wp wn gate s).1+(pull wp wn gate s).2 = (s.1+s.2).comp (matrixCLM (wp+wn)) := by
  apply ContinuousLinearMap.ext
  intro v
  change (assemble s) (splitLayerJac wp wn gate (v,0)) +
    (assemble s) (splitLayerJac wp wn gate (0,v)) = _
  rw [← map_add, ← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add, splitLayer_common]
  rfl

theorem MaskedTrace.pull_unified {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (gate : Fin k → Bool) (s : Sensitivity k) :
    unified (pull wp wn gate s) = (unified s).comp (signedMap wp wn gate) -
      (1/2 : ℝ) • ((s.1+s.2).comp (deadMap wp wn gate)) := by
  apply ContinuousLinearMap.ext
  intro v
  change (1/2 : ℝ) * ((assemble s) (splitLayerJac wp wn gate (v,0)) -
      (assemble s) (splitLayerJac wp wn gate (0,v))) = _
  rw [← map_sub, ← map_sub]
  simp only [Prod.mk_sub_mk, sub_zero, zero_sub, splitLayer_signed]
  change (1/2 : ℝ) *
      (s.1 (signedMap wp wn gate v-deadMap wp wn gate v)+
       s.2 (-signedMap wp wn gate v-deadMap wp wn gate v)) = _
  simp only [map_sub, map_neg]
  change (1/2 : ℝ) * ((s.1 (signedMap wp wn gate v)-s.1 (deadMap wp wn gate v))+
    (-s.2 (signedMap wp wn gate v)-s.2 (deadMap wp wn gate v))) =
    (1/2 : ℝ)*(s.1 (signedMap wp wn gate v)-s.2 (signedMap wp wn gate v)) -
    (1/2 : ℝ)*(s.1 (deadMap wp wn gate v)+s.2 (deadMap wp wn gate v))
  ring

/-- Exact layerwise bulk formula for the implemented shifted backward pass. -/
theorem MaskedTrace.stabilized_bulk {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (r : Row m) (head : Bool) :
    (tr.stabilized α r head).1+(tr.stabilized α r head).2 =
      tr.bulkCoefficient α • (r.comp tr.absMap) := by
  induction tr generalizing α with
  | output n =>
      cases head <;> simp only [MaskedTrace.stabilized, Bool.false_eq_true, ite_false,
        ite_true, MaskedTrace.bulkCoefficient, MaskedTrace.absMap,
        ContinuousLinearMap.comp_id, shiftPair_sum, add_zero, zero_add]
  | layer wp wn gate tail ih =>
      simp only [MaskedTrace.stabilized, shiftPair_sum, MaskedTrace.pull_sum, ih,
        MaskedTrace.bulkCoefficient, MaskedTrace.absMap,
        ContinuousLinearMap.smul_comp, smul_smul, ContinuousLinearMap.comp_assoc]

/-- Full varying-width closed recursion for the unified stabilized derivatives.
Both the algorithm and the common source term are instantiated, not assumed. -/
theorem MaskedTrace.stabilized_unified {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (r : Row m) (head : Bool) :
    unified (tr.stabilized α r head) =
      (if head then (1/2 : ℝ) else (-1/2 : ℝ)) • (r.comp tr.originalJac) -
      (1/2 : ℝ) • tr.correction α r := by
  induction tr generalizing α with
  | output n =>
      simp only [MaskedTrace.stabilized]
      rw [unified_shift]
      cases head <;> simp [unified, MaskedTrace.originalJac, MaskedTrace.correction]
      module
  | layer wp wn gate tail ih =>
      simp only [MaskedTrace.stabilized, unified_shift, MaskedTrace.pull_unified,
        ih, MaskedTrace.stabilized_bulk, MaskedTrace.originalJac, MaskedTrace.correction]
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
      ring

/-- Thesis thm:closed_formula_shift, g-head: the actual shifted recursion. -/
theorem MaskedTrace.stabilized_backward_closed_form_g {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (r : Row m) :
    unified (tr.stabilized α r true) =
      (1/2 : ℝ) • (r.comp tr.originalJac-tr.correction α r) := by
  rw [tr.stabilized_unified]
  simp only [ite_true, smul_sub]

/-- Thesis thm:closed_formula_shift, h-head. -/
theorem MaskedTrace.stabilized_backward_closed_form_h {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (r : Row m) :
    unified (tr.stabilized α r false) =
      (-1/2 : ℝ) • (r.comp tr.originalJac+tr.correction α r) := by
  rw [tr.stabilized_unified]
  simp only [Bool.false_eq_true, ite_false]
  module

/-- Thesis backward invariant at every tail, for the actual shifted algorithm. -/
theorem MaskedTrace.stabilized_backward_invariant {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (r : Row m) :
    unified (tr.stabilized α r true)-unified (tr.stabilized α r false) =
      r.comp tr.originalJac := by
  rw [tr.stabilized_backward_closed_form_g, tr.stabilized_backward_closed_form_h]
  module

noncomputable def headProjection {m} (r : Row m) (head : Bool) : PairVec m →L[ℝ] ℝ :=
  if head then r.comp (ContinuousLinearMap.fst ℝ (Vec m) (Vec m))
  else r.comp (ContinuousLinearMap.snd ℝ (Vec m) (Vec m))

/-- With zero shifts the complete implemented backward pass is exactly the
ordinary Fréchet differential of the corresponding split head. -/
theorem MaskedTrace.zero_shift_actual {n m} (tr : MaskedTrace n m)
    (r : Row m) (head : Bool) :
    assemble (tr.stabilized (fun _ => 0) r head) = (headProjection r head).comp tr.splitJac := by
  induction tr with
  | output n =>
      cases head <;> simp [MaskedTrace.stabilized, shiftPair, assemble, headProjection,
        MaskedTrace.splitJac]
  | layer wp wn gate tail ih =>
      simp only [MaskedTrace.stabilized, shiftPair, zero_smul, sub_zero,
        MaskedTrace.pull, assemble_partialPair, ih, MaskedTrace.splitJac,
        ContinuousLinearMap.comp_assoc]
      exact assemble_partialPair _

/-- Source-facing correctness of the local sensitivities: a genuine derivative
of the actual head, rather than a derivative assumed as a premise. -/
theorem Network.local_sensitivities_correct {n m} (net : Network n m)
    (x : PairVec n) (hx : net.Regular x) (r : Row m) (head : Bool) :
    HasFDerivAt (fun y : PairVec n => if head then r (net.split y.1 y.2).1
      else r (net.split y.1 y.2).2)
      (assemble ((net.trace x).stabilized (fun _ => 0) r head)) x := by
  rw [MaskedTrace.zero_shift_actual, ← Network.jacobian_trace]
  have hp := (headProjection r head).hasFDerivAt.comp x (net.hasFDerivAt_split x hx)
  cases head <;> exact hp

theorem MaskedTrace.bulkCoefficient_zero {n m} (tr : MaskedTrace n m) :
    tr.bulkCoefficient (fun _ => 0) = 1 := by
  induction tr with
  | output n => norm_num [MaskedTrace.bulkCoefficient]
  | layer wp wn gate tail ih => simpa [MaskedTrace.bulkCoefficient] using ih

/-- Thesis thm:delta_connection, for the actual unshifted head sensitivities. -/
theorem Network.sensitivity_complementarity {n m} (net : Network n m)
    (x : PairVec n) (r : Row m) (head : Bool) :
    ((net.trace x).stabilized (fun _ => 0) r head).1 +
      ((net.trace x).stabilized (fun _ => 0) r head).2 =
      r.comp (net.trace x).absMap := by
  rw [MaskedTrace.stabilized_bulk, MaskedTrace.bulkCoefficient_zero, one_smul]

noncomputable def MaskedTrace.correctionTerms {n m} : MaskedTrace n m → (ℕ → ℝ) →
    Row m → List (Row n)
  | .output _, _, _ => []
  | .layer wp wn gate tail, α, r =>
      (tail.bulkCoefficient (fun i => α (i+1)) •
        ((r.comp tail.absMap).comp (MaskedTrace.deadMap wp wn gate))) ::
      (tail.correctionTerms (fun i => α (i+1)) r).map
        (fun d => d.comp (MaskedTrace.signedMap wp wn gate))

theorem row_sum_comp {n k} (rs : List (Row k)) (D : Vec n →L[ℝ] Vec k) :
    (rs.map (fun r => r.comp D)).sum = rs.sum.comp D := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp [ih, ContinuousLinearMap.add_comp]

/-- A literal finite sum of individual layer source terms, valid for varying widths. -/
theorem MaskedTrace.correction_terms_sum {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (r : Row m) :
    (tr.correctionTerms α r).sum = tr.correction α r := by
  induction tr generalizing α with
  | output n => rfl
  | layer wp wn gate tail ih =>
      simp only [MaskedTrace.correctionTerms, List.sum_cons, row_sum_comp, ih,
        MaskedTrace.correction]
      exact add_comm _ _

/-- The complete implemented varying-width shifted backward algorithm equals
its original gradient minus an explicit finite sum of layer corrections. -/
theorem Network.stabilized_backward_closed_form {n m} (net : Network n m)
    (x : PairVec n) (α : ℕ → ℝ) (r : Row m) :
    unified ((net.trace x).stabilized α r true) =
      (1/2 : ℝ) • (r.comp (net.trace x).originalJac -
        ((net.trace x).correctionTerms α r).sum) ∧
    unified ((net.trace x).stabilized α r false) =
      (-1/2 : ℝ) • (r.comp (net.trace x).originalJac +
        ((net.trace x).correctionTerms α r).sum) := by
  rw [MaskedTrace.correction_terms_sum]
  exact ⟨MaskedTrace.stabilized_backward_closed_form_g _ _ _,
    MaskedTrace.stabilized_backward_closed_form_h _ _ _⟩

def MaskedTrace.depth {n m} : MaskedTrace n m → ℕ
  | .output _ => 0
  | .layer _ _ _ tail => tail.depth+1

/-- The recursive coefficient is exactly the printed finite product over all
layers in the tail, including its current and output layers. -/
theorem MaskedTrace.bulkCoefficient_product {n m} (tr : MaskedTrace n m) (α : ℕ → ℝ) :
    tr.bulkCoefficient α = ∏ i ∈ Finset.range (tr.depth+1), (1-2*α i) := by
  induction tr generalizing α with
  | output n => simp [MaskedTrace.bulkCoefficient, MaskedTrace.depth]
  | layer wp wn gate tail ih =>
      simp only [MaskedTrace.bulkCoefficient, MaskedTrace.depth]
      rw [ih, Finset.prod_range_succ' _ (tail.depth+1)]
      exact mul_comm _ _

@[simp] theorem MaskedTrace.bulkCoefficient_half {n m} (tr : MaskedTrace n m) :
    tr.bulkCoefficient (fun _ => (1/2 : ℝ)) = 0 := by
  cases tr <;> simp [MaskedTrace.bulkCoefficient]

@[simp] theorem MaskedTrace.correction_half {n m} (tr : MaskedTrace n m) (r : Row m) :
    tr.correction (fun _ => (1/2 : ℝ)) r = 0 := by
  induction tr with
  | output n => rfl
  | layer wp wn gate tail ih =>
      simp only [MaskedTrace.correction, ih, MaskedTrace.bulkCoefficient_half,
        ContinuousLinearMap.zero_comp, zero_smul, add_zero]

/-- At α=1/2 both shifted gradients are exactly half the original gradient,
with opposite signs; this follows from the complete implemented recursion. -/
theorem Network.half_shift_gradients {n m} (net : Network n m) (x : PairVec n) (r : Row m) :
    unified ((net.trace x).stabilized (fun _ => (1/2 : ℝ)) r true) =
      (1/2 : ℝ) • r.comp (net.trace x).originalJac ∧
    unified ((net.trace x).stabilized (fun _ => (1/2 : ℝ)) r false) =
      (-1/2 : ℝ) • r.comp (net.trace x).originalJac := by
  rw [MaskedTrace.stabilized_backward_closed_form_g, MaskedTrace.stabilized_backward_closed_form_h]
  simp only [MaskedTrace.correction_half, sub_zero, add_zero]
  constructor <;> trivial

/-- The two separate cross-head partial invariants, stronger than only their
balanced difference: positive input gives +Df and negative input gives -Df. -/
theorem MaskedTrace.stabilized_partial_invariants {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (r : Row m) :
    (tr.stabilized α r true).1-(tr.stabilized α r false).1 = r.comp tr.originalJac ∧
    (tr.stabilized α r true).2-(tr.stabilized α r false).2 = -(r.comp tr.originalJac) := by
  have hsum : (tr.stabilized α r true).1+(tr.stabilized α r true).2 =
      (tr.stabilized α r false).1+(tr.stabilized α r false).2 := by
    rw [tr.stabilized_bulk, tr.stabilized_bulk]
  have hdiff := tr.stabilized_backward_invariant α r
  constructor <;> apply ContinuousLinearMap.ext <;> intro v
  · have hs := congrArg (fun R : Row n => R v) hsum
    have hd := congrArg (fun R : Row n => R v) hdiff
    simp only [unified, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at hs hd ⊢
    linarith
  · have hs := congrArg (fun R : Row n => R v) hsum
    have hd := congrArg (fun R : Row n => R v) hdiff
    simp only [unified, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul] at hs hd ⊢
    linarith

end HiddenMonotonicity
