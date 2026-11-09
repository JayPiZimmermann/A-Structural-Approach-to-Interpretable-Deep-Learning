import HiddenMonotonicity.TransformerDefinition

noncomputable section
set_option autoImplicit false
open HiddenMonotonicity.TransformerDC
open scoped BigOperators

namespace TransformerDefinitionAudit

def causalMask (tokens : ℕ) : TransformerMask tokens where
  keyCount := fun q => q.val + 1
  keyCount_pos := by intro q; omega
  keyAt := fun q k => ⟨k.val, by omega⟩
  keyAt_injective := by
    intro q a b h
    apply Fin.ext
    exact congrArg (fun z : Fin tokens => z.val) h

example : (causalMask 2).keyCount 0 = 1 := rfl
example : (causalMask 2).keyCount 1 = 2 := rfl
example : (causalMask 2).keyAt 0 ⟨0, by decide⟩ = (0 : Fin 2) := rfl

def norm : TransformerNorm 1 where
  epsilon := 1
  epsilon_pos := by norm_num
  gamma := fun _ => -2
  beta := fun _ => 7

def affine (c : ℝ) : TransformerAffine 1 1 where
  weight := fun _ _ => 0
  bias := fun _ => c

def head : TransformerHead 1 1 where
  keyWidth := 1
  keyWidth_pos := by norm_num
  valueWidth := 1
  valueWidth_pos := by norm_num
  query := affine 0
  key := affine 0
  value := affine 3
  outputWeight := fun _ _ => 1
  scale := 1
  mask := TransformerMask.full 1

def block : TransformerBlock 1 1 where
  attentionNorm := norm
  heads := [head]
  attentionBias := fun _ => -1
  feedForwardNorm := norm
  hiddenWidth := 1
  up := affine 0
  activation := .gaussianGelu
  down := affine (-4)

def network (depth : ℕ) : Transformer 1 1 1 where
  tokens_pos := by norm_num
  width_pos := by norm_num
  positionalBias := fun _ _ => -2
  blocks := List.replicate depth block
  finalNorm := none
  readoutWeight := fun _ _ _ => -3
  readoutBias := fun _ => -5

theorem head_eval (x : Fin 1 → Fin 1 → ℝ) : head.eval x 0 0 = 3 := by
  dsimp only [TransformerHead.eval, TransformerHead.logits, head, affine,
    TransformerAffine.eval, TransformerMask.full]
  norm_num [
    HiddenMonotonicity.SoftmaxDC.softmax, HiddenMonotonicity.SoftmaxDC.expSum]

theorem block_eval (x : Fin 1 → Fin 1 → ℝ) (q i : Fin 1) :
    block.eval x q i = x q i - 2 := by
  fin_cases q
  fin_cases i
  change block.eval x 0 0 = x 0 0 - 2
  have hres : block.attentionResidual x 0 0 = x 0 0 + 2 := by
    change x 0 0 + ((∑ h : Fin 1, head.eval (norm.eval x) 0 0) + (-1)) = _
    rw [Fin.sum_univ_one, head_eval]
    ring
  change block.attentionResidual x 0 0 +
    ((∑ j : Fin 1, (0 : ℝ) * _) + (-4)) = _
  rw [hres]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  ring

example (x : ℝ) : (network 0).eval (fun _ => x) 0 = 1 - 3 * x := by
  norm_num [network, Transformer.eval, evalOptionalTransformerNorm, evalTransformerBlocks]
  ring

example (x : ℝ) : (network 2).eval (fun _ => x) 0 = 13 - 3 * x := by
  norm_num [network, Transformer.eval, evalOptionalTransformerNorm, evalTransformerBlocks,
    block_eval]
  ring

example (x : Fin 1 × Fin 1 → ℝ) :
    ((network 2).syntax 0).eval x = (network 2).eval x 0 := by
  exact Transformer.eval_syntax (network 2) x 0

example (x : Fin 1 × Fin 1 → ℝ) :
    (Transformer.eval { network 2 with finalNorm := some norm } x 0) = -26 := by
  norm_num [Transformer.eval, network, evalOptionalTransformerNorm, TransformerNorm.eval,
    norm, layerNorm, layerMean, layerVariance]

example (x : Fin 1 × Fin 1 → ℝ) :
    (({ network 2 with finalNorm := some norm } : Transformer 1 1 1).syntax 0).eval x =
      ({ network 2 with finalNorm := some norm } : Transformer 1 1 1).eval x 0 := by
  exact Transformer.eval_syntax _ x 0

end TransformerDefinitionAudit
