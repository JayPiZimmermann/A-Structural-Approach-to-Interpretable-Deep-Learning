import HiddenMonotonicity.StabilizedBackward
import HiddenMonotonicity.Sensitivities

namespace HiddenMonotonicity
open Matrix

noncomputable def affineLayer {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) : Vec k := matrixCLM (wp-wn) x + (bp-bn)

noncomputable def reluLayer {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) : Vec k := fun i => relu (affineLayer wp wn bp bn x i)

noncomputable def minLayer {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) : Vec k := fun i => min (affineLayer wp wn bp bn x i) 0

noncomputable def originalGate {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) : Fin k → Bool :=
  fun i => decide (0 < affineLayer wp wn bp bn x i)

noncomputable def Network.originalTrace {n m} : Network n m → Vec n → MaskedTrace n m
  | .output n, _ => .output n
  | .layer wp wn bp bn tail, x => .layer wp wn (originalGate wp wn bp bn x)
      (tail.originalTrace (reluLayer wp wn bp bn x))

noncomputable def Network.Strict {n m} : Network n m → Vec n → Prop
  | .output _, _ => True
  | .layer wp wn bp bn tail, x => (∀ i, affineLayer wp wn bp bn x i ≠ 0) ∧
      tail.Strict (reluLayer wp wn bp bn x)

noncomputable def Network.absCLM {n m} : Network n m → (Vec n →L[ℝ] Vec m)
  | .output _ => ContinuousLinearMap.id ℝ _
  | .layer wp wn _ _ tail => tail.absCLM.comp (matrixCLM (wp+wn))

theorem preactivation_difference {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) :
    preP wp wn x+bp-(preN wp wn x+bn) = affineLayer wp wn bp bn (x.1-x.2) := by
  funext i
  change (wp.mulVec x.1+wn.mulVec x.2+bp-(wn.mulVec x.1+wp.mulVec x.2+bn)) i =
    ((wp-wn).mulVec (x.1-x.2)+(bp-bn)) i
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply]
  ring

theorem layerFun_difference {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) :
    (layerFun wp wn bp bn x).1-(layerFun wp wn bp bn x).2 =
      reluLayer wp wn bp bn (x.1-x.2) := by
  funext i
  change max ((preP wp wn x+bp) i) ((preN wp wn x+bn) i)-
    (preN wp wn x+bn) i = _
  rw [max_sub]
  change relu ((preP wp wn x+bp-(preN wp wn x+bn)) i) = _
  rw [preactivation_difference]
  rfl

/-- Gate extraction depends only on the represented original activation. -/
theorem Network.trace_originalTrace {n m} (net : Network n m) (x : PairVec n) :
    net.trace x = net.originalTrace (x.1-x.2) := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [Network.trace, Network.originalTrace]
      rw [ih, layerFun_difference]
      congr 1
      funext i
      have hi := congrFun (preactivation_difference wp wn bp bn x) i
      simp only [Pi.sub_apply] at hi
      unfold originalGate
      rw [← hi]
      simp only [sub_pos]

theorem Network.regular_iff_strict {n m} (net : Network n m) (x : PairVec n) :
    net.Regular x ↔ net.Strict (x.1-x.2) := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [Network.Regular, Network.Strict]
      rw [ih, layerFun_difference]
      apply and_congr
      · apply forall_congr'
        intro i
        have hi := congrFun (preactivation_difference wp wn bp bn x) i
        simp only [Pi.sub_apply] at hi
        constructor <;> intro h hh <;> apply h <;> linarith
      · rfl

theorem Network.trace_absCLM {n m} (net : Network n m) (x : PairVec n) :
    (net.trace x).absMap = net.absCLM := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [Network.trace, MaskedTrace.absMap, Network.absCLM]
      rw [ih]

theorem Network.originalTrace_absCLM {n m} (net : Network n m) (x : Vec n) :
    (net.originalTrace x).absMap = net.absCLM := by
  have h := net.trace_absCLM (x,0)
  rw [net.trace_originalTrace] at h
  simpa using h

/-- Actual original MLP derivative under directly readable nonzero-preactivation assumptions. -/
theorem Network.hasFDerivAt_originalTrace {n m} (net : Network n m) (x : Vec n)
    (hx : net.Strict x) : HasFDerivAt net.eval (net.originalTrace x).originalJac x := by
  have hr : net.Regular (x,0) := (net.regular_iff_strict (x,0)).mpr (by simpa using hx)
  have h := net.hasFDerivAt_eval_trace x hr
  simpa [net.trace_originalTrace] using h

theorem affineLayer_hasFDerivAt {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) :
    HasFDerivAt (affineLayer wp wn bp bn) (matrixCLM (wp-wn)) x :=
  (matrixCLM (wp-wn)).hasFDerivAt.add_const (bp-bn)

theorem reluLayer_hasFDerivAt {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) (hx : ∀ i, affineLayer wp wn bp bn x i ≠ 0) :
    HasFDerivAt (reluLayer wp wn bp bn)
      (MaskedTrace.signedMap wp wn (originalGate wp wn bp bn x)) x := by
  have hpi : HasFDerivAt (reluLayer wp wn bp bn)
      (ContinuousLinearMap.pi fun i => if 0 < affineLayer wp wn bp bn x i then
        (ContinuousLinearMap.proj i).comp (matrixCLM (wp-wn)) else 0) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    have hz := (ContinuousLinearMap.proj i).hasFDerivAt.comp x
      (affineLayer_hasFDerivAt wp wn bp bn x)
    have h0 : HasFDerivAt (fun _ : Vec n => (0 : ℝ)) (0 : Vec n →L[ℝ] ℝ) x := hasFDerivAt_const (0 : ℝ) x
    by_cases h : 0 < affineLayer wp wn bp bn x i
    · simpa [reluLayer, relu, h] using max_derivative_left _ _ _ _ _ hz h0 h
    · have hn : affineLayer wp wn bp bn x i < 0 := lt_of_le_of_ne (le_of_not_gt h) (hx i)
      simpa [reluLayer, relu, h] using max_derivative_right _ _ _ _ _ hz h0 hn
  convert hpi using 1
  apply ContinuousLinearMap.ext
  intro v
  funext i
  simp [MaskedTrace.signedMap, MaskedTrace.activeMap, originalGate]
  split_ifs <;> rfl

theorem minLayer_hasFDerivAt {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) (hx : ∀ i, affineLayer wp wn bp bn x i ≠ 0) :
    HasFDerivAt (minLayer wp wn bp bn)
      (MaskedTrace.deadMap wp wn (originalGate wp wn bp bn x)) x := by
  have hz := affineLayer_hasFDerivAt wp wn bp bn x
  have hr := reluLayer_hasFDerivAt wp wn bp bn x hx
  have h := hz.fun_sub hr
  have hf : (fun y => affineLayer wp wn bp bn y-reluLayer wp wn bp bn y) =
      minLayer wp wn bp bn := by
    funext y i
    unfold reluLayer relu minLayer
    change affineLayer wp wn bp bn y i-max (affineLayer wp wn bp bn y i) 0 = _
    rcases le_total (affineLayer wp wn bp bn y i) 0 with ha | ha
    · rw [max_eq_right ha, min_eq_left ha]; ring
    · rw [max_eq_left ha, min_eq_right ha]; ring
  have hd : matrixCLM (wp-wn)-MaskedTrace.signedMap wp wn (originalGate wp wn bp bn x) =
      MaskedTrace.deadMap wp wn (originalGate wp wn bp bn x) := by
    ext v i
    simp [MaskedTrace.deadMap, MaskedTrace.inactiveMap, MaskedTrace.signedMap]
  rw [hf, hd] at h
  exact h

/-- Canonical sign parts: W+=max(W,0), W-=max(-W,0) entrywise.
This is precisely the setting in which W++W- is the entrywise absolute weight. -/
def Network.Canonical {n m} : Network n m → Prop
  | .output _ => True
  | .layer wp wn _ _ tail =>
      (∀ i j, wp i j = max (wp i j-wn i j) 0 ∧
        wn i j = max (-(wp i j-wn i j)) 0) ∧ tail.Canonical

noncomputable def Network.absoluteMap {n m} : Network n m → (Vec n →L[ℝ] Vec m)
  | .output _ => ContinuousLinearMap.id ℝ _
  | .layer wp wn _ _ tail =>
      tail.absoluteMap.comp (matrixCLM (fun i j => |wp i j-wn i j|))

/-- The common-mode product is exactly the printed absolute-weight product
for the canonical sign split, including all varying layer widths. -/
theorem Network.absCLM_eq_absoluteMap {n m} (net : Network n m) (hc : net.Canonical) :
    net.absCLM = net.absoluteMap := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [Network.absCLM, Network.absoluteMap, ih hc.2]
      congr 2
      funext i j
      change wp i j+wn i j=|wp i j-wn i j|
      have hp := (hc.1 i j).1
      have hn := (hc.1 i j).2
      calc
        wp i j+wn i j = max (wp i j-wn i j) 0+max (-(wp i j-wn i j)) 0 := congrArg₂ (·+·) hp hn
        _ = |wp i j-wn i j| := (canonical_weight_split _).2

/-- Thesis thm:delta_connection with the literal absolute-weight tail. -/
theorem Network.sensitivity_complementarity_absolute {n m} (net : Network n m)
    (hc : net.Canonical) (x : PairVec n) (r : Row m) (head : Bool) :
    ((net.trace x).stabilized (fun _ => 0) r head).1+
      ((net.trace x).stabilized (fun _ => 0) r head).2 = r.comp net.absoluteMap := by
  rw [net.sensitivity_complementarity, net.trace_absCLM, net.absCLM_eq_absoluteMap hc]

end HiddenMonotonicity
