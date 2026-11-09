import HiddenMonotonicity.TransformerExpr

/-! Explicit finite pre-normalization Transformers and their compilation to the
scalar expression language. The forward definition contains ordinary signed
projections, coupled softmax attention, input-dependent LayerNorm, residuals,
and feed-forward activations. Depth is an arbitrary finite list of blocks. -/
noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity.TransformerDC
open scoped BigOperators

universe u

/-- A signed affine map; neither weights nor biases have sign restrictions. -/
structure TransformerAffine (n m : ℕ) where
  weight : Fin m → Fin n → ℝ
  bias : Fin m → ℝ

def TransformerAffine.eval {n m : ℕ} (a : TransformerAffine n m)
    (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  (∑ j, a.weight i j * x j) + a.bias i

def TransformerAffine.compile {n m : ℕ} {ι : Type u}
    (a : TransformerAffine n m) (x : Fin n → Expr ι) (i : Fin m) : Expr ι :=
  .add (.sum n (fun j => .scale (a.weight i j) (x j))) (.const (a.bias i))

@[simp] theorem TransformerAffine.eval_compile {n m : ℕ} {ι : Type u}
    (a : TransformerAffine n m) (x : Fin n → Expr ι) (v : ι → ℝ) (i : Fin m) :
    (a.compile x i).eval v = a.eval (fun j => (x j).eval v) i := by
  simp [TransformerAffine.compile, TransformerAffine.eval]

/-- Fixed attention masks are finite nonempty sets, represented by injective
index maps. Causal masks and the full mask are instances. -/
structure TransformerMask (tokens : ℕ) where
  keyCount : Fin tokens → ℕ
  keyCount_pos : ∀ q, 0 < keyCount q
  keyAt : (q : Fin tokens) → Fin (keyCount q) → Fin tokens
  keyAt_injective : ∀ q, Function.Injective (keyAt q)

def TransformerMask.full (tokens : ℕ) : TransformerMask tokens where
  keyCount := fun _ => tokens
  keyCount_pos := fun q => Nat.zero_lt_of_lt q.isLt
  keyAt := fun _ k => k
  keyAt_injective := fun _ => Function.injective_id

/-- A head includes its block-output projection. Summing these projections is
identical to concatenating head outputs and applying one affine output map. -/
structure TransformerHead (tokens width : ℕ) where
  keyWidth : ℕ
  keyWidth_pos : 0 < keyWidth
  valueWidth : ℕ
  valueWidth_pos : 0 < valueWidth
  query : TransformerAffine width keyWidth
  key : TransformerAffine width keyWidth
  value : TransformerAffine width valueWidth
  outputWeight : Fin width → Fin valueWidth → ℝ
  scale : ℝ
  mask : TransformerMask tokens

def TransformerHead.logits {t d : ℕ} (h : TransformerHead t d)
    (x : Fin t → Fin d → ℝ) (q : Fin t) (k : Fin (h.mask.keyCount q)) : ℝ :=
  h.scale * ∑ r, h.query.eval (x q) r * h.key.eval (x (h.mask.keyAt q k)) r

def TransformerHead.eval {t d : ℕ} (h : TransformerHead t d)
    (x : Fin t → Fin d → ℝ) (q : Fin t) (i : Fin d) : ℝ :=
  ∑ r, h.outputWeight i r *
    ∑ k, SoftmaxDC.softmax (h.logits x q) k *
      h.value.eval (x (h.mask.keyAt q k)) r

def TransformerHead.compileLogits {t d : ℕ} {ι : Type u}
    (h : TransformerHead t d) (x : Fin t → Fin d → Expr ι)
    (q : Fin t) (k : Fin (h.mask.keyCount q)) : Expr ι :=
  .scale h.scale (.sum h.keyWidth (fun r =>
    .mul (h.query.compile (x q) r) (h.key.compile (x (h.mask.keyAt q k)) r)))

def TransformerHead.compile {t d : ℕ} {ι : Type u}
    (h : TransformerHead t d) (x : Fin t → Fin d → Expr ι)
    (q : Fin t) (i : Fin d) : Expr ι :=
  .sum h.valueWidth (fun r => .scale (h.outputWeight i r)
    (.sum (h.mask.keyCount q) (fun k =>
      .mul (.softmax (h.mask.keyCount q) (h.compileLogits x q) k)
        (h.value.compile (x (h.mask.keyAt q k)) r))))

@[simp] theorem TransformerHead.eval_compileLogits {t d : ℕ} {ι : Type u}
    (h : TransformerHead t d) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ) (q : Fin t) (k : Fin (h.mask.keyCount q)) :
    (h.compileLogits x q k).eval v =
      h.logits (fun a b => (x a b).eval v) q k := by
  simp [TransformerHead.compileLogits, TransformerHead.logits]

@[simp] theorem TransformerHead.eval_compile {t d : ℕ} {ι : Type u}
    (h : TransformerHead t d) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ) (q : Fin t) (i : Fin d) :
    (h.compile x q i).eval v = h.eval (fun a b => (x a b).eval v) q i := by
  simp [TransformerHead.compile, TransformerHead.eval]

structure TransformerNorm (width : ℕ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  gamma : Fin width → ℝ
  beta : Fin width → ℝ

def TransformerNorm.eval {t d : ℕ} (p : TransformerNorm d)
    (x : Fin t → Fin d → ℝ) (q : Fin t) (i : Fin d) : ℝ :=
  layerNorm p.epsilon p.gamma p.beta (x q) i

def TransformerNorm.compile {t d : ℕ} {ι : Type u} (p : TransformerNorm d)
    (x : Fin t → Fin d → Expr ι) (q : Fin t) (i : Fin d) : Expr ι :=
  .layerNorm d p.epsilon p.epsilon_pos p.gamma p.beta (x q) i

@[simp] theorem TransformerNorm.eval_compile {t d : ℕ} {ι : Type u}
    (p : TransformerNorm d) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ) (q : Fin t) (i : Fin d) :
    (p.compile x q i).eval v = p.eval (fun a b => (x a b).eval v) q i := by
  simp [TransformerNorm.compile, TransformerNorm.eval]

def evalOptionalTransformerNorm {t d : ℕ} (p : Option (TransformerNorm d))
    (x : Fin t → Fin d → ℝ) : Fin t → Fin d → ℝ :=
  match p with
  | none => x
  | some norm => norm.eval x

def compileOptionalTransformerNorm {t d : ℕ} {ι : Type u}
    (p : Option (TransformerNorm d)) (x : Fin t → Fin d → Expr ι) :
    Fin t → Fin d → Expr ι :=
  match p with
  | none => x
  | some norm => norm.compile x

@[simp] theorem eval_compileOptionalTransformerNorm {t d : ℕ} {ι : Type u}
    (p : Option (TransformerNorm d)) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ) (q : Fin t) (i : Fin d) :
    (compileOptionalTransformerNorm p x q i).eval v =
      evalOptionalTransformerNorm p (fun a b => (x a b).eval v) q i := by
  cases p <;> simp [compileOptionalTransformerNorm, evalOptionalTransformerNorm]

/-- A pre-LayerNorm Transformer block with a finite collection of attention
heads, two residual additions, and a tokenwise feed-forward subnetwork. -/
structure TransformerBlock (tokens width : ℕ) where
  attentionNorm : TransformerNorm width
  heads : List (TransformerHead tokens width)
  attentionBias : Fin width → ℝ
  feedForwardNorm : TransformerNorm width
  hiddenWidth : ℕ
  up : TransformerAffine width hiddenWidth
  activation : SmoothDC.ClosedFormActivation
  down : TransformerAffine hiddenWidth width

def TransformerBlock.attentionResidual {t d : ℕ} (b : TransformerBlock t d)
    (x : Fin t → Fin d → ℝ) (q : Fin t) (i : Fin d) : ℝ :=
  x q i + ((∑ h : Fin b.heads.length,
    (b.heads.get h).eval (b.attentionNorm.eval x) q i) + b.attentionBias i)

def TransformerBlock.eval {t d : ℕ} (b : TransformerBlock t d)
    (x : Fin t → Fin d → ℝ) (q : Fin t) (i : Fin d) : ℝ :=
  let y := b.attentionResidual x
  let z := b.feedForwardNorm.eval y
  y q i + b.down.eval (fun j => b.activation.eval (b.up.eval (z q) j)) i

def TransformerBlock.compileAttentionResidual {t d : ℕ} {ι : Type u}
    (b : TransformerBlock t d) (x : Fin t → Fin d → Expr ι)
    (q : Fin t) (i : Fin d) : Expr ι :=
  .add (x q i) (.add (.sum b.heads.length (fun h =>
    (b.heads.get h).compile (b.attentionNorm.compile x) q i)) (.const (b.attentionBias i)))

def TransformerBlock.compile {t d : ℕ} {ι : Type u}
    (b : TransformerBlock t d) (x : Fin t → Fin d → Expr ι)
    (q : Fin t) (i : Fin d) : Expr ι :=
  let y := b.compileAttentionResidual x
  let z := b.feedForwardNorm.compile y
  .add (y q i) (b.down.compile
    (fun j => .activation b.activation (b.up.compile (z q) j)) i)

@[simp] theorem TransformerBlock.eval_compileAttentionResidual {t d : ℕ} {ι : Type u}
    (b : TransformerBlock t d) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ) (q : Fin t) (i : Fin d) :
    (b.compileAttentionResidual x q i).eval v =
      b.attentionResidual (fun a c => (x a c).eval v) q i := by
  simp [TransformerBlock.compileAttentionResidual, TransformerBlock.attentionResidual]

@[simp] theorem TransformerBlock.eval_compile {t d : ℕ} {ι : Type u}
    (b : TransformerBlock t d) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ) (q : Fin t) (i : Fin d) :
    (b.compile x q i).eval v = b.eval (fun a c => (x a c).eval v) q i := by
  simp [TransformerBlock.compile, TransformerBlock.eval]

/-- Ordinary block evaluation at arbitrary finite depth. -/
def evalTransformerBlocks {t d : ℕ} :
    List (TransformerBlock t d) → (Fin t → Fin d → ℝ) → Fin t → Fin d → ℝ
  | [], x => x
  | b :: bs, x => evalTransformerBlocks bs (b.eval x)

/-- An explicit recursive compiler, without any depth bound. -/
def compileTransformerBlocks {t d : ℕ} {ι : Type u} :
    List (TransformerBlock t d) → (Fin t → Fin d → Expr ι) → Fin t → Fin d → Expr ι
  | [], x => x
  | b :: bs, x => compileTransformerBlocks bs (b.compile x)

@[simp] theorem eval_compileTransformerBlocks {t d : ℕ} {ι : Type u}
    (bs : List (TransformerBlock t d)) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ) (q : Fin t) (i : Fin d) :
    (compileTransformerBlocks bs x q i).eval v =
      evalTransformerBlocks bs (fun a c => (x a c).eval v) q i := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih => simpa [compileTransformerBlocks, evalTransformerBlocks] using ih (b.compile x)

/-- Transformer logits as a function of real input embeddings. The affine
readout includes token pooling or CLS selection as special choices of weights. -/
structure Transformer (tokens width outputs : ℕ) where
  tokens_pos : 0 < tokens
  width_pos : 0 < width
  positionalBias : Fin tokens → Fin width → ℝ
  blocks : List (TransformerBlock tokens width)
  finalNorm : Option (TransformerNorm width)
  readoutWeight : Fin outputs → Fin tokens → Fin width → ℝ
  readoutBias : Fin outputs → ℝ

def Transformer.eval {t d o : ℕ} (net : Transformer t d o)
    (x : Fin t × Fin d → ℝ) (i : Fin o) : ℝ :=
  let z := evalOptionalTransformerNorm net.finalNorm
    (evalTransformerBlocks net.blocks (fun q j => x (q,j) + net.positionalBias q j))
  (∑ q, ∑ j, net.readoutWeight i q j * z q j) + net.readoutBias i

def Transformer.compile {t d o : ℕ} {ι : Type u} (net : Transformer t d o)
    (x : Fin t → Fin d → Expr ι) (i : Fin o) : Expr ι :=
  let z := compileOptionalTransformerNorm net.finalNorm
    (compileTransformerBlocks net.blocks
      (fun q j => .add (x q j) (.const (net.positionalBias q j))))
  .add (.sum t (fun q => .sum d (fun j => .scale (net.readoutWeight i q j) (z q j))))
    (.const (net.readoutBias i))

@[simp] theorem Transformer.eval_compile {t d o : ℕ} {ι : Type u}
    (net : Transformer t d o) (x : Fin t → Fin d → Expr ι) (v : ι → ℝ) (i : Fin o) :
    (net.compile x i).eval v = net.eval (fun p => (x p.1 p.2).eval v) i := by
  simp [Transformer.compile, Transformer.eval]

/-- The explicit symbolic expression for the complete network, including its
positional input bias and its ungated signed affine logits. -/
def Transformer.syntax {t d o : ℕ} (net : Transformer t d o)
    (i : Fin o) : Expr (Fin t × Fin d) :=
  net.compile (fun q j => .input (q,j)) i

@[simp] theorem Transformer.eval_syntax {t d o : ℕ} (net : Transformer t d o)
    (x : Fin t × Fin d → ℝ) (i : Fin o) :
    (net.syntax i).eval x = net.eval x i := by
  simp [Transformer.syntax]

end HiddenMonotonicity.TransformerDC
