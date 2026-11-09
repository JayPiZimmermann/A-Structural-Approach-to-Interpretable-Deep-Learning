import HiddenMonotonicity.Network
import HiddenMonotonicity.Chunks
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace HiddenMonotonicity
open Matrix
abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev PairVec (n : ℕ) := Vec n × Vec n

noncomputable def matrixCLM {n k} (W : Matrix (Fin k) (Fin n) ℝ) : Vec n →L[ℝ] Vec k :=
  (Matrix.toLin' W).toContinuousLinearMap

noncomputable def preP {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) : PairVec n →L[ℝ] Vec k :=
  (matrixCLM wp).comp (ContinuousLinearMap.fst ℝ (Vec n) (Vec n)) +
  (matrixCLM wn).comp (ContinuousLinearMap.snd ℝ (Vec n) (Vec n))

noncomputable def preN {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) : PairVec n →L[ℝ] Vec k :=
  preP wn wp

noncomputable def layerFun {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) : PairVec k :=
  ((fun i => max ((preP wp wn x + bp) i) ((preN wp wn x + bn) i)), preN wp wn x + bn)

noncomputable def layerJac {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) : PairVec n →L[ℝ] PairVec k :=
  (ContinuousLinearMap.pi fun i =>
    if (preN wp wn x + bn) i < (preP wp wn x + bp) i then
      (ContinuousLinearMap.proj i).comp (preP wp wn)
    else (ContinuousLinearMap.proj i).comp (preN wp wn)).prod (preN wp wn)

theorem preP_apply {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (x : PairVec n) :
    preP wp wn x = wp.mulVec x.1 + wn.mulVec x.2 := by
  rfl

theorem layer_derivative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n)
    (hx : ∀ i, (preP wp wn x+bp) i ≠ (preN wp wn x+bn) i) :
    HasFDerivAt (layerFun wp wn bp bn) (layerJac wp wn bp bn x) x := by
  have hp : HasFDerivAt (fun y => preP wp wn y+bp) (preP wp wn) x :=
    (preP wp wn).hasFDerivAt.add_const bp
  have hn : HasFDerivAt (fun y => preN wp wn y+bn) (preN wp wn) x :=
    (preN wp wn).hasFDerivAt.add_const bn
  have hm : HasFDerivAt
      (fun y i => max ((preP wp wn y+bp) i) ((preN wp wn y+bn) i))
      (ContinuousLinearMap.pi fun i =>
        if (preN wp wn x+bn) i < (preP wp wn x+bp) i then
          (ContinuousLinearMap.proj i).comp (preP wp wn)
        else (ContinuousLinearMap.proj i).comp (preN wp wn)) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    have hpi := (ContinuousLinearMap.proj i).hasFDerivAt.comp x hp
    have hni := (ContinuousLinearMap.proj i).hasFDerivAt.comp x hn
    split_ifs with h
    · exact max_derivative_left _ _ _ _ _ hpi hni h
    · exact max_derivative_right _ _ _ _ _ hpi hni (lt_of_le_of_ne (le_of_not_gt h) (hx i))
  exact hm.prodMk hn

noncomputable def Network.jacobian {n m} : (net : Network n m) → PairVec n →
    (PairVec n →L[ℝ] PairVec m)
  | .output _, _ => ContinuousLinearMap.id ℝ _
  | .layer wp wn bp bn tail, x =>
      (tail.jacobian (layerFun wp wn bp bn x)).comp (layerJac wp wn bp bn x)

noncomputable def Network.Regular {n m} : (net : Network n m) → PairVec n → Prop
  | .output _, _ => True
  | .layer wp wn bp bn tail, x =>
      (∀ i, (preP wp wn x+bp) i ≠ (preN wp wn x+bn) i) ∧
      tail.Regular (layerFun wp wn bp bn x)

/-- Actual Fréchet derivative of the entire varying-width split network,
computed recursively from the weight maps and strict winning max branches. -/
theorem Network.hasFDerivAt_split {n m} (net : Network n m) (x : PairVec n)
    (hx : net.Regular x) :
    HasFDerivAt (fun y : PairVec n => net.split y.1 y.2) (net.jacobian x) x := by
  induction net with
  | output n => exact (ContinuousLinearMap.id ℝ (PairVec n)).hasFDerivAt
  | layer wp wn bp bn tail ih =>
      have ht := ih (layerFun wp wn bp bn x) hx.2
      have hl := layer_derivative wp wn bp bn x hx.1
      exact ht.comp x hl

noncomputable def blockPP {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) : Vec n →L[ℝ] Vec k :=
  ContinuousLinearMap.pi fun i =>
    if (preN wp wn x+bn) i < (preP wp wn x+bp) i then
      (ContinuousLinearMap.proj i).comp (matrixCLM wp)
    else (ContinuousLinearMap.proj i).comp (matrixCLM wn)

noncomputable def blockPN {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) : Vec n →L[ℝ] Vec k :=
  ContinuousLinearMap.pi fun i =>
    if (preN wp wn x+bn) i < (preP wp wn x+bp) i then
      (ContinuousLinearMap.proj i).comp (matrixCLM wn)
    else (ContinuousLinearMap.proj i).comp (matrixCLM wp)

theorem layerJac_positive_input {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) (v : Vec n) :
    layerJac wp wn bp bn x (v,0) = (blockPP wp wn bp bn x v, matrixCLM wn v) := by
  apply Prod.ext
  · funext i
    simp only [layerJac, blockPP, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]
    split_ifs <;> simp [preP, preN]
  · simp [layerJac, preN, preP]

theorem layerJac_negative_input {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) (v : Vec n) :
    layerJac wp wn bp bn x (0,v) = (blockPN wp wn bp bn x v, matrixCLM wp v) := by
  apply Prod.ext
  · funext i
    simp only [layerJac, blockPN, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]
    split_ifs <;> simp [preP, preN]
  · simp [layerJac, preN, preP]

/-- The actual differential chain rule has exactly the two positive-input
sensitivity contributions used by the paper's block backward recursion. -/
theorem actual_positive_pullback {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) (v : Vec n) (D : PairVec k →L[ℝ] ℝ) :
    (D.comp (layerJac wp wn bp bn x)) (v,0) =
      D (blockPP wp wn bp bn x v,0) + D (0,matrixCLM wn v) := by
  simp only [ContinuousLinearMap.comp_apply, layerJac_positive_input]
  rw [← map_add]
  simp

/-- The matching negative-input sensitivity recurrence. -/
theorem actual_negative_pullback {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) (v : Vec n) (D : PairVec k →L[ℝ] ℝ) :
    (D.comp (layerJac wp wn bp bn x)) (0,v) =
      D (blockPN wp wn bp bn x v,0) + D (0,matrixCLM wp v) := by
  simp only [ContinuousLinearMap.comp_apply, layerJac_negative_input]
  rw [← map_add]
  simp

noncomputable def liftCLM (n : ℕ) : Vec n →L[ℝ] PairVec n :=
  (ContinuousLinearMap.id ℝ (Vec n)).prod 0

noncomputable def differenceCLM (n : ℕ) : PairVec n →L[ℝ] Vec n :=
  ContinuousLinearMap.fst ℝ (Vec n) (Vec n) - ContinuousLinearMap.snd ℝ (Vec n) (Vec n)

/-- The original network also has a genuine derivative, obtained by projecting
and composing the recursively computed split-network Jacobian. -/
theorem Network.hasFDerivAt_eval {n m} (net : Network n m) (x : Vec n)
    (hx : net.Regular (x,0)) :
    HasFDerivAt net.eval
      ((differenceCLM m).comp ((net.jacobian (x,0)).comp (liftCLM n))) x := by
  have hs := net.hasFDerivAt_split (x,0) hx
  have hl : HasFDerivAt (liftCLM n) (liftCLM n) x := (liftCLM n).hasFDerivAt
  have hd : HasFDerivAt (differenceCLM m) (differenceCLM m) (net.split x 0) :=
    (differenceCLM m).hasFDerivAt
  have hc := hd.comp x (hs.comp x hl)
  have he : net.eval = (differenceCLM m) ∘
      ((fun y : PairVec n => net.split y.1 y.2) ∘ liftCLM n) := by
    funext y
    simpa [differenceCLM, liftCLM] using (net.correct y 0).symm
  rw [he]
  exact hc

end HiddenMonotonicity
