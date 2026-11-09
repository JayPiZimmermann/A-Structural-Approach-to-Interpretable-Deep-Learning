import HiddenMonotonicity.TransformerCorrectness

noncomputable section
set_option autoImplicit false
open HiddenMonotonicity.TransformerDC
open scoped BigOperators

/-- A genuine signed logit at depth zero, with nonzero positional and output biases. -/
def signedLogit : Transformer 1 1 1 where
  tokens_pos := by decide
  width_pos := by decide
  positionalBias := fun _ _ => 1
  blocks := []
  finalNorm := none
  readoutWeight := fun _ _ _ => -2
  readoutBias := fun _ => 3

example (x : Fin 1 × Fin 1 → ℝ) :
    signedLogit.eval x 0 = -2 * x (0,0) + 1 := by
  simp [signedLogit, Transformer.eval, evalOptionalTransformerNorm, evalTransformerBlocks]
  ring

-- A negative output remains negative. An accidental final ReLU would fail this.
example : signedLogit.eval (fun _ => 2) 0 = -3 := by
  norm_num [signedLogit, Transformer.eval, evalOptionalTransformerNorm, evalTransformerBlocks]

-- Evaluate the actual recursive split, not only its abstract recovery theorem.
example : signedLogit.decompose ((fun _ => 2), (fun _ => 0)) 0 = (3,6) := by
  norm_num [signedLogit, Transformer.decompose, Transformer.syntax, Transformer.compile,
    compileOptionalTransformerNorm, compileTransformerBlocks, Expr.decompose,
    Expr.splitEval, constPair, scalePair, addPair]

example : signedLogit.rawDecompose (fun _ => -2) 0 = (7,2) := by
  norm_num [signedLogit, Transformer.rawDecompose, Transformer.decompose, Transformer.syntax,
    Transformer.compile, compileOptionalTransformerNorm, compileTransformerBlocks,
    Expr.decompose, signedInput, Expr.splitEval, constPair, scalePair, addPair]

-- Arbitrary blocks are actually composed; depth is not an unused parameter.
example {t d : ℕ} (a b : TransformerBlock t d) (x : Fin t → Fin d → ℝ) :
    evalTransformerBlocks [a,b] x = b.eval (a.eval x) := rfl

-- This head projects onto the first feature for Q, K, and V. For two tokens,
-- both keys remain in the coupled denominator and both value routes contribute.
def firstFeature : TransformerAffine 2 1 where
  weight := fun _ j => if j = 0 then 1 else 0
  bias := fun _ => 0

def twoTokenHead : TransformerHead 2 2 where
  keyWidth := 1
  keyWidth_pos := by decide
  valueWidth := 1
  valueWidth_pos := by decide
  query := firstFeature
  key := firstFeature
  value := firstFeature
  outputWeight := fun _ _ => 1
  scale := 1
  mask := TransformerMask.full 2

theorem twoTokenHead_logits (x : Fin 2 → Fin 2 → ℝ) (q k : Fin 2) :
    twoTokenHead.logits x q k = x q 0 * x k 0 := by
  change (1 : ℝ) * (∑ r : Fin 1, firstFeature.eval (x q) r * firstFeature.eval (x k) r) = _
  simp [firstFeature, TransformerAffine.eval]

example (x : Fin 2 → Fin 2 → ℝ) (q : Fin 2) (i : Fin 2) :
    twoTokenHead.eval x q i =
      HiddenMonotonicity.SoftmaxDC.softmax (fun k => x q 0 * x k 0) 0 * x 0 0 +
      HiddenMonotonicity.SoftmaxDC.softmax (fun k => x q 0 * x k 0) 1 * x 1 0 := by
  change (∑ r : Fin 1, (1 : ℝ) * ∑ k : Fin 2,
    HiddenMonotonicity.SoftmaxDC.softmax (twoTokenHead.logits x q) k *
      firstFeature.eval (x k) r) = _
  have hlogits : twoTokenHead.logits x q = fun k => x q 0 * x k 0 :=
    funext (twoTokenHead_logits x q)
  simp [hlogits, firstFeature, TransformerAffine.eval, Fin.sum_univ_two]
  rfl

-- The fixed-mask type rules out a completely masked existing query.
example {t : ℕ} (mask : TransformerMask t) (q : Fin t) : mask.keyCount q ≠ 0 :=
  Nat.ne_of_gt (mask.keyCount_pos q)

-- No sign restriction is required for the exactness identity.
example {t d o : ℕ} (net : Transformer t d o)
    (x : DoubledInput (Fin t × Fin d)) (i : Fin o) :
    (net.decompose x i).1 - (net.decompose x i).2 = net.eval (x.1-x.2) i :=
  net.decompose_exact x i

-- Raw-input convexity does not smuggle in a monotonicity hypothesis for x⁻.
example {t d o : ℕ} (net : Transformer t d o) (i : Fin o) :
    ConvexOn ℝ Set.univ (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).2) :=
  net.raw_dc_decomposition.2.1 i

#print axioms Transformer.dc_decomposition
#print axioms Transformer.raw_dc_decomposition
#print axioms Transformer.eval_syntax
#print axioms layerNormPair_exact
