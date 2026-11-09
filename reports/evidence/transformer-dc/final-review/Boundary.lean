import HiddenMonotonicity.TransformerCorrectness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open HiddenMonotonicity.TransformerDC
open Set
namespace TransformerFinalBoundary

private def signedNorm : TransformerNorm 2 where
  epsilon := 1
  epsilon_pos := by norm_num
  gamma := fun i => if i = 0 then -2 else 3
  beta := fun i => if i = 0 then -1 else 2

private def selfMask : TransformerMask 2 where
  keyCount := fun _ => 1
  keyCount_pos := fun _ => by norm_num
  keyAt := fun q _ => q
  keyAt_injective := fun _ _ _ _ => Subsingleton.elim _ _

private def projection : TransformerAffine 2 1 where
  weight := fun _ j => if j = 0 then -1 else 2
  bias := fun _ => -3

private def fullHead : TransformerHead 2 2 where
  keyWidth := 1
  keyWidth_pos := by norm_num
  valueWidth := 1
  valueWidth_pos := by norm_num
  query := projection
  key := projection
  value := projection
  outputWeight := fun i _ => if i = 0 then -2 else 3
  scale := 1
  mask := TransformerMask.full 2

private def selfHead : TransformerHead 2 2 := { fullHead with mask := selfMask }

private def feedAffine : TransformerAffine 2 2 where
  weight := fun i j => if i = j then -1 else 2
  bias := fun i => if i = 0 then -2 else 1

private def block : TransformerBlock 2 2 where
  attentionNorm := signedNorm
  heads := [fullHead, selfHead]
  attentionBias := fun _ => -1
  feedForwardNorm := signedNorm
  hiddenWidth := 2
  up := feedAffine
  activation := HiddenMonotonicity.SmoothDC.ClosedFormActivation.gaussianGelu
  down := feedAffine

private def net (blocks : List (TransformerBlock 2 2))
    (finalNorm : Option (TransformerNorm 2)) : Transformer 2 2 1 where
  tokens_pos := by norm_num
  width_pos := by norm_num
  positionalBias := fun _ _ => 1
  blocks := blocks
  finalNorm := finalNorm
  readoutWeight := fun _ _ _ => -1
  readoutBias := fun _ => -7

private def zeroDepth : Transformer 2 2 1 := net [] none
private def oneDepth : Transformer 2 2 1 := net [block] none
private def twoDepth : Transformer 2 2 1 := net [block, block] (some signedNorm)
private def negativeInput : Fin 2 × Fin 2 → ℝ := fun _ => -2

example : zeroDepth.blocks.length = 0 := rfl
example : oneDepth.blocks.length = 1 := rfl
example : twoDepth.blocks.length = 2 := rfl
example : block.heads.length = 2 := rfl
example : zeroDepth.finalNorm = none := rfl
example : twoDepth.finalNorm = some signedNorm := rfl
example : fullHead.mask.keyCount 0 = 2 := rfl
example : selfHead.mask.keyCount 1 = 1 := rfl
example : signedNorm.gamma 0 = -2 := by norm_num [signedNorm]
example : projection.weight 0 0 = -1 := by norm_num [projection]

/-- The signed affine head really can return a negative logit. -/
example : zeroDepth.eval negativeInput 0 = -3 := by
  norm_num [zeroDepth, net, Transformer.eval, evalOptionalTransformerNorm,
    evalTransformerBlocks, negativeInput, Fin.sum_univ_two]

example (x : DoubledInput (Fin 2 × Fin 2)) :
    (zeroDepth.decompose x 0).1 - (zeroDepth.decompose x 0).2 =
      zeroDepth.eval (x.1 - x.2) 0 := zeroDepth.decompose_exact x 0

example (x : DoubledInput (Fin 2 × Fin 2)) :
    (oneDepth.decompose x 0).1 - (oneDepth.decompose x 0).2 =
      oneDepth.eval (x.1 - x.2) 0 := oneDepth.decompose_exact x 0

example (x : DoubledInput (Fin 2 × Fin 2)) :
    (twoDepth.decompose x 0).1 - (twoDepth.decompose x 0).2 =
      twoDepth.eval (x.1 - x.2) 0 := twoDepth.decompose_exact x 0

example : MonotoneOn twoDepth.decompose
    (Ici (0 : DoubledInput (Fin 2 × Fin 2))) :=
  twoDepth.dc_decomposition.1

example : ConvexOn ℝ (Ici (0 : DoubledInput (Fin 2 × Fin 2)))
    (fun x => (twoDepth.decompose x 0).1) := twoDepth.dc_decomposition.2.1 0

example : ConvexOn ℝ (Ici (0 : DoubledInput (Fin 2 × Fin 2)))
    (fun x => (twoDepth.decompose x 0).2) := twoDepth.dc_decomposition.2.2.1 0

example (x : DoubledInput (Fin 2 × Fin 2)) (hx : 0 ≤ x) :
    0 ≤ twoDepth.decompose x := twoDepth.dc_decomposition.2.2.2.1 x hx

example : ConvexOn ℝ univ (fun x : Fin 2 × Fin 2 → ℝ =>
    (twoDepth.rawDecompose x 0).1) := twoDepth.raw_dc_decomposition.1 0

example : ConvexOn ℝ univ (fun x : Fin 2 × Fin 2 → ℝ =>
    (twoDepth.rawDecompose x 0).2) := twoDepth.raw_dc_decomposition.2.1 0

example : 0 ≤ twoDepth.rawDecompose negativeInput :=
  twoDepth.raw_dc_decomposition.2.2.1 negativeInput

example : (twoDepth.rawDecompose negativeInput 0).1 -
    (twoDepth.rawDecompose negativeInput 0).2 = twoDepth.eval negativeInput 0 :=
  twoDepth.raw_dc_decomposition.2.2.2 negativeInput 0

example : (zeroDepth.rawDecompose negativeInput 0).1 -
    (zeroDepth.rawDecompose negativeInput 0).2 = -3 := by
  rw [zeroDepth.raw_dc_decomposition.2.2.2]
  norm_num [zeroDepth, net, Transformer.eval, evalOptionalTransformerNorm,
    evalTransformerBlocks, negativeInput, Fin.sum_univ_two]

/-- Zero output width remains a total, vacuous output family, not an assumption contradiction. -/
private def noOutputs : Transformer 2 2 0 where
  tokens_pos := by norm_num
  width_pos := by norm_num
  positionalBias := fun _ _ => -1
  blocks := [block]
  finalNorm := some signedNorm
  readoutWeight := fun i => Fin.elim0 i
  readoutBias := fun i => Fin.elim0 i

example : MonotoneOn noOutputs.decompose
    (Ici (0 : DoubledInput (Fin 2 × Fin 2))) := noOutputs.dc_decomposition.1

/-- A symbolic depth exercises the theorem without choosing a finite numerical bound. -/
example (n : ℕ) : (net (List.replicate n block) none).blocks.length = n := by
  simp [net]

example (n : ℕ) (x : DoubledInput (Fin 2 × Fin 2)) :
    ((net (List.replicate n block) none).decompose x 0).1 -
      ((net (List.replicate n block) none).decompose x 0).2 =
      (net (List.replicate n block) none).eval (x.1 - x.2) 0 :=
  (net (List.replicate n block) none).decompose_exact x 0

example (n : ℕ) : MonotoneOn (net (List.replicate n block) none).decompose
    (Ici (0 : DoubledInput (Fin 2 × Fin 2))) :=
  (net (List.replicate n block) none).dc_decomposition.1

example (n : ℕ) : ConvexOn ℝ univ (fun x : Fin 2 × Fin 2 → ℝ =>
    ((net (List.replicate n block) (some signedNorm)).rawDecompose x 0).1) :=
  (net (List.replicate n block) (some signedNorm)).raw_dc_decomposition.1 0

end TransformerFinalBoundary
