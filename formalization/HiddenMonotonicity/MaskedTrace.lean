import HiddenMonotonicity.NetworkDerivative

namespace HiddenMonotonicity
open Matrix

/-- A finite MLP with a fixed choice of ReLU gate at every neuron. Widths may
change at each layer. `Network.trace` obtains exactly these gates from a forward pass. -/
inductive MaskedTrace : ℕ → ℕ → Type
  | output (n : ℕ) : MaskedTrace n n
  | layer {n k m : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ)
      (gate : Fin k → Bool) (tail : MaskedTrace k m) : MaskedTrace n m

namespace MaskedTrace

noncomputable def activeMap {n : ℕ} (gate : Fin n → Bool) : Vec n →L[ℝ] Vec n :=
  ContinuousLinearMap.pi fun i => if gate i then ContinuousLinearMap.proj i else 0

noncomputable def inactiveMap {n : ℕ} (gate : Fin n → Bool) : Vec n →L[ℝ] Vec n :=
  ContinuousLinearMap.id ℝ (Vec n) - activeMap gate

@[simp] theorem activeMap_apply {n : ℕ} (gate : Fin n → Bool) (v : Vec n) (i : Fin n) :
    activeMap gate v i = if gate i then v i else 0 := by
  simp only [activeMap, ContinuousLinearMap.pi_apply]
  cases gate i <;> rfl

@[simp] theorem inactiveMap_apply {n : ℕ} (gate : Fin n → Bool) (v : Vec n) (i : Fin n) :
    inactiveMap gate v i = if gate i then 0 else v i := by
  simp [inactiveMap]
  split_ifs <;> simp_all

noncomputable def signedMap {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (gate : Fin k → Bool) : Vec n →L[ℝ] Vec k :=
  (activeMap gate).comp (matrixCLM (wp-wn))

noncomputable def deadMap {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (gate : Fin k → Bool) : Vec n →L[ℝ] Vec k :=
  (inactiveMap gate).comp (matrixCLM (wp-wn))

noncomputable def splitLayerJac {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (gate : Fin k → Bool) : PairVec n →L[ℝ] PairVec k :=
  ((activeMap gate).comp (preP wp wn) +
    (inactiveMap gate).comp (preN wp wn)).prod (preN wp wn)

noncomputable def originalJac {n m} : MaskedTrace n m → (Vec n →L[ℝ] Vec m)
  | .output _ => ContinuousLinearMap.id ℝ _
  | .layer wp wn gate tail => tail.originalJac.comp (signedMap wp wn gate)

noncomputable def splitJac {n m} : MaskedTrace n m → (PairVec n →L[ℝ] PairVec m)
  | .output _ => ContinuousLinearMap.id ℝ _
  | .layer wp wn gate tail => tail.splitJac.comp (splitLayerJac wp wn gate)

theorem difference_splitLayer {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (gate : Fin k → Bool) :
    (differenceCLM k).comp (splitLayerJac wp wn gate) =
      (signedMap wp wn gate).comp (differenceCLM n) := by
  apply ContinuousLinearMap.ext
  intro y
  funext i
  change ((activeMap gate (preP wp wn y) + inactiveMap gate (preN wp wn y)) -
      preN wp wn y) i = activeMap gate (matrixCLM (wp-wn) (y.1-y.2)) i
  simp only [Pi.sub_apply, Pi.add_apply, activeMap_apply, inactiveMap_apply]
  change (if gate i then (wp.mulVec y.1+wn.mulVec y.2) i else 0) +
      (if gate i then 0 else (wn.mulVec y.1+wp.mulVec y.2) i) -
      (wn.mulVec y.1+wp.mulVec y.2) i =
    if gate i then ((wp-wn).mulVec (y.1-y.2)) i else 0
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Pi.sub_apply, Pi.add_apply]
  cases gate i <;> simp <;> ring

/-- The split Jacobian represents exactly the original gated network Jacobian. -/
theorem difference_splitJac {n m} (tr : MaskedTrace n m) :
    (differenceCLM m).comp tr.splitJac = tr.originalJac.comp (differenceCLM n) := by
  induction tr with
  | output n => rfl
  | layer wp wn gate tail ih =>
      simp only [splitJac, originalJac, ← ContinuousLinearMap.comp_assoc]
      rw [ih]
      simp only [ContinuousLinearMap.comp_assoc, difference_splitLayer]

end MaskedTrace

noncomputable def Network.trace {n m} : Network n m → PairVec n → MaskedTrace n m
  | .output n, _ => .output n
  | .layer wp wn bp bn tail, x =>
      .layer wp wn (fun i => decide ((preN wp wn x+bn) i < (preP wp wn x+bp) i))
        (tail.trace (layerFun wp wn bp bn x))

theorem layerJac_trace {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) :
    layerJac wp wn bp bn x = MaskedTrace.splitLayerJac wp wn
      (fun i => decide ((preN wp wn x+bn) i < (preP wp wn x+bp) i)) := by
  apply ContinuousLinearMap.ext
  intro y
  apply Prod.ext
  · funext i
    simp only [layerJac, MaskedTrace.splitLayerJac, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, MaskedTrace.activeMap_apply,
      MaskedTrace.inactiveMap_apply, Pi.add_apply]
    split_ifs <;> simp_all <;> linarith
  · rfl

theorem Network.jacobian_trace {n m} (net : Network n m) (x : PairVec n) :
    net.jacobian x = (net.trace x).splitJac := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [Network.jacobian, Network.trace, MaskedTrace.splitJac]
      rw [ih, layerJac_trace]

/-- The actual gradient of the original MLP is the same masked, signed product
used by the stopping-game and split-backward formalizations. -/
theorem Network.hasFDerivAt_eval_trace {n m} (net : Network n m) (x : Vec n)
    (hx : net.Regular (x,0)) :
    HasFDerivAt net.eval (net.trace (x,0)).originalJac x := by
  have h := net.hasFDerivAt_eval x hx
  rw [net.jacobian_trace] at h
  have he : (differenceCLM m).comp ((net.trace (x,0)).splitJac.comp (liftCLM n)) =
      (net.trace (x,0)).originalJac := by
    rw [← ContinuousLinearMap.comp_assoc, MaskedTrace.difference_splitJac,
      ContinuousLinearMap.comp_assoc]
    have hi : (differenceCLM n).comp (liftCLM n) = ContinuousLinearMap.id ℝ (Vec n) := by
      ext v i
      simp [differenceCLM, liftCLM]
    rw [hi, ContinuousLinearMap.comp_id]
  rw [he] at h
  exact h

end HiddenMonotonicity
