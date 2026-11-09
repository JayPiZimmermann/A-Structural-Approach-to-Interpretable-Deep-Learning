import Thesis.RoutingBackward

/-! Conditioned attention: the attention matrix is a fixed parameter. These
statements concern X ↦ A(X Wvᵀ+bv), and never the derivative through QK-softmax. -/
noncomputable section
namespace Thesis.AttentionBackward
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward

def pairIndex {a b : ℕ} : Fin (a*b) → Fin a × Fin b :=
  (finProdFinEquiv : Fin a × Fin b ≃ Fin (a*b)).symm

def flatIndex {a b : ℕ} : Fin a × Fin b → Fin (a*b) :=
  (finProdFinEquiv : Fin a × Fin b ≃ Fin (a*b))

/-- The conditioned attention product and Value projection as one effective map. -/
def effectiveWeight {T K C D : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) : Matrix (Fin (T*C)) (Fin (K*D)) ℝ :=
  fun u v => A (pairIndex u).1 (pairIndex v).1 * Wv (pairIndex u).2 (pairIndex v).2

def effectiveBias {T K C : ℕ} (A : Matrix (Fin T) (Fin K) ℝ) (bv : Vec C) : Vec (T*C) :=
  fun u => ∑ k, A (pairIndex u).1 k * bv (pairIndex u).2

/-- Direct token-by-token computation, with one Value bias per output channel. -/
def conditionedAttention {T K C D : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (x : Vec (K*D)) : Vec (T*C) :=
  fun u => ∑ k, A (pairIndex u).1 k *
    ((∑ d, Wv (pairIndex u).2 d * x (flatIndex (k,d))) + bv (pairIndex u).2)

/-- Exact algebraic identification of the effective affine attention block. -/
theorem conditionedAttention_affine {T K C D : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (x : Vec (K*D)) :
    conditionedAttention A Wv bv x = (effectiveWeight A Wv).mulVec x + effectiveBias A bv := by
  funext u
  simp only [conditionedAttention, mul_add, Finset.sum_add_distrib, effectiveBias, Pi.add_apply]
  congr 1
  change (∑ k, A (pairIndex u).1 k * ∑ d, Wv (pairIndex u).2 d * x (flatIndex (k,d))) =
    ∑ v, effectiveWeight A Wv u v * x v
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin K × Fin D ≃ Fin (K*D))
    (fun v => effectiveWeight A Wv u v * x v), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp only [effectiveWeight, pairIndex, Equiv.symm_apply_apply, flatIndex]
  ring

/-- Actual affine derivative of the conditioned block, including its Value bias. -/
theorem conditionedAttention_hasFDerivAt {T K C D : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (x : Vec (K*D)) :
    HasFDerivAt (conditionedAttention A Wv bv) (matrixCLM (effectiveWeight A Wv)) x := by
  have h : HasFDerivAt (fun y => matrixCLM (effectiveWeight A Wv) y + effectiveBias A bv)
      (matrixCLM (effectiveWeight A Wv)) x :=
    (matrixCLM (effectiveWeight A Wv)).hasFDerivAt.add_const (effectiveBias A bv)
  have he : conditionedAttention A Wv bv =
      (fun y => matrixCLM (effectiveWeight A Wv) y + effectiveBias A bv) := by
    funext y
    exact conditionedAttention_affine A Wv bv y
  rwa [he]

/-- Row normalization of the reference policy preserves the Value bias. -/
theorem normalized_attention_bias {T K C : ℕ} (A : Matrix (Fin T) (Fin K) ℝ) (bv : Vec C)
    (hA : ∀ t, ∑ k, A t k = 1) (u : Fin (T*C)) : effectiveBias A bv u = bv (pairIndex u).2 := by
  unfold effectiveBias
  rw [← Finset.sum_mul, hA, one_mul]

/-- Exact positive/negative contribution factoring through a nonnegative reference policy. -/
theorem effective_contribution_factor {T K C D : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (x : Vec (K*D))
    (hA : ∀ t k, 0 ≤ A t k) (u : Fin (T*C)) (v : Fin (K*D)) :
    posContribution (effectiveWeight A Wv) 0 x u v =
      A (pairIndex u).1 (pairIndex v).1 * max (x v * Wv (pairIndex u).2 (pairIndex v).2) 0 ∧
    negContribution (effectiveWeight A Wv) 0 x u v =
      A (pairIndex u).1 (pairIndex v).1 * max (-(x v * Wv (pairIndex u).2 (pairIndex v).2)) 0 := by
  have hm (a b : ℝ) (ha : 0 ≤ a) : max (a*b) 0 = a * max b 0 := by
    by_cases hb : 0 ≤ b
    · rw [max_eq_left hb, max_eq_left (mul_nonneg ha hb)]
    · rw [max_eq_right (le_of_not_ge hb), max_eq_right (mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hb)), mul_zero]
  constructor
  · simp only [posContribution, effectiveWeight, Matrix.zero_apply, sub_zero]
    rw [show x v * (A (pairIndex u).1 (pairIndex v).1 * Wv (pairIndex u).2 (pairIndex v).2) =
      A (pairIndex u).1 (pairIndex v).1 * (x v * Wv (pairIndex u).2 (pairIndex v).2) by ring]
    exact hm _ _ (hA _ _)
  · simp only [negContribution, effectiveWeight, Matrix.zero_apply, sub_zero]
    rw [show -(x v * (A (pairIndex u).1 (pairIndex v).1 * Wv (pairIndex u).2 (pairIndex v).2)) =
      A (pairIndex u).1 (pairIndex v).1 * (-(x v * Wv (pairIndex u).2 (pairIndex v).2)) by ring]
    exact hm _ _ (hA _ _)

/-- Ungated affine alpha-beta rule, appropriate to a conditioned attention block or final logit. -/
def affineRule {n m} (C : Matrix (Fin m) (Fin n) ℝ) (b : Vec m) (α β ε : ℝ)
    (x : Vec n) : Matrix (Fin m) (Fin n) ℝ := fun j i =>
  α * posContribution C 0 x j i / posDenominator C 0 b 0 ε x j -
    β * negContribution C 0 x j i / negDenominator C 0 b 0 ε x j

/-- Composite attention followed by an arbitrary shared ReLU backbone. -/
def attentionLRP {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (x : Vec (K*D)) (R : Vec m) : Vec (K*D) :=
  lrp α β ε tail (conditionedAttention A Wv bv x) R ᵥ*
    affineRule (effectiveWeight A Wv) (effectiveBias A bv) α β ε x

def attentionTrace {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (x : Vec (K*D)) : MaskedTrace (K*D) m :=
  .layer
    (fun j i => α * posContribution (effectiveWeight A Wv) 0 x j i /
      posDenominator (effectiveWeight A Wv) 0 (effectiveBias A bv) 0 ε x j)
    (fun j i => β * negContribution (effectiveWeight A Wv) 0 x j i /
      negDenominator (effectiveWeight A Wv) 0 (effectiveBias A bv) 0 ε x j)
    (fun _ => true) (routingTrace α β ε tail (conditionedAttention A Wv bv x))

theorem attentionLRP_matrix {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (x : Vec (K*D)) (R : Vec m) :
    attentionLRP A Wv bv tail α β ε x R = R ᵥ* signedProduct (attentionTrace A Wv bv tail α β ε x) := by
  rw [attentionLRP, full_lrp_matrix, Matrix.vecMul_vecMul]
  apply congrArg (fun M : Matrix _ _ ℝ => R ᵥ* M)
  apply congrArg (fun M : Matrix _ _ ℝ => signedProduct (routingTrace α β ε tail
    (conditionedAttention A Wv bv x)) * M)
  ext j i
  rfl

/-- The conditioned composite rule is exactly the signed occupation of its entire routing trace. -/
theorem attention_raw_recovery {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (x : Vec (K*D)) (R : Vec m) (i : Fin (K*D)) :
    attentionLRP A Wv bv tail α β ε x R i = ∑ j, R j *
      ((∑ path : Paths (attentionTrace A Wv bv tail α β ε x),
        rawWeight (attentionTrace A Wv bv tail α β ε x) j i false path) -
       (∑ path : Paths (attentionTrace A Wv bv tail α β ε x),
        rawWeight (attentionTrace A Wv bv tail α β ε x) j i true path)) := by
  rw [attentionLRP_matrix, ← occupation_difference]
  change (∑ j, R j * ((occupations (attentionTrace A Wv bv tail α β ε x)).1 -
      (occupations (attentionTrace A Wv bv tail α β ε x)).2) j i) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [(raw_path_integral _ j i).1, (raw_path_integral _ j i).2]
  rfl

/-- Actual one-block routing probabilities followed by the backbone routing law. -/
def attentionProbability {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (x : Vec (K*D)) (j : Fin m) (i : Fin (K*D)) (p : Bool)
    (path : Paths (attentionTrace A Wv bv tail α β ε x)) : ℝ :=
  ((if path.2.1 then negContribution (effectiveWeight A Wv) 0 x path.1 i /
      negDenominator (effectiveWeight A Wv) 0 (effectiveBias A bv) 0 ε x path.1
    else posContribution (effectiveWeight A Wv) 0 x path.1 i /
      posDenominator (effectiveWeight A Wv) 0 (effectiveBias A bv) 0 ε x path.1) / 2) *
  rgProbability α β ε tail (conditionedAttention A Wv bv x) j path.1 (Bool.xor p path.2.1) path.2.2

def attentionDiscount {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (x : Vec (K*D)) (path : Paths (attentionTrace A Wv bv tail α β ε x)) : ℝ :=
  (if path.2.1 then 2*β else 2*α) *
    rgDiscount α β ε tail (conditionedAttention A Wv bv x) path.2.2

theorem attention_path_discount_recovery {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (x : Vec (K*D)) (j : Fin m) (i : Fin (K*D)) (p : Bool)
    (path : Paths (attentionTrace A Wv bv tail α β ε x)) :
    attentionDiscount A Wv bv tail α β ε x path * attentionProbability A Wv bv tail α β ε x j i p path =
      rawWeight (attentionTrace A Wv bv tail α β ε x) j i p path := by
  simp only [attentionDiscount, attentionProbability, attentionTrace, rawWeight, ite_true]
  have ht := rg_path_discount_recovery tail α β ε (conditionedAttention A Wv bv x)
    j path.1 (Bool.xor p path.2.1) path.2.2
  split_ifs <;> simp only [← ht] <;> ring

def attentionOccupation {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (x : Vec (K*D)) (j : Fin m) (i : Fin (K*D)) (p : Bool) : ℝ :=
  ∑ path : Paths (attentionTrace A Wv bv tail α β ε x),
    attentionDiscount A Wv bv tail α β ε x path * attentionProbability A Wv bv tail α β ε x j i p path

/-- Source-facing composite-rule recovery, including every downstream MLP layer.
This is the anchor policy/occupation identity on the attention-conditioned map;
it asserts no derivative through QK or a global game-equilibrium theorem. -/
theorem thesis_attention_alpha_beta_recovery {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (_hε : 0 < ε)
    (_hA : ∀ t k, 0 ≤ A t k) (_hA1 : ∀ t, ∑ k, A t k = 1)
    (x : Vec (K*D)) (R : Vec m) (i : Fin (K*D)) :
    attentionLRP A Wv bv tail α β ε x R i = ∑ j, R j *
      (attentionOccupation A Wv bv tail α β ε x j i false -
       attentionOccupation A Wv bv tail α β ε x j i true) := by
  simp only [attentionOccupation, attention_path_discount_recovery]
  exact attention_raw_recovery A Wv bv tail α β ε x R i

theorem attentionProbability_nonneg {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (hε : 0 < ε) (x : Vec (K*D)) (j : Fin m) (i : Fin (K*D)) (p : Bool)
    (path : Paths (attentionTrace A Wv bv tail α β ε x)) :
    0 ≤ attentionProbability A Wv bv tail α β ε x j i p path := by
  apply mul_nonneg _ (rgProbability_nonneg tail α β ε hε _ _ _ _ _)
  apply div_nonneg _ (by norm_num)
  split_ifs
  · exact div_nonneg (le_max_right _ _)
      (negDenominator_pos _ _ _ _ ε hε _ _).le
  · exact div_nonneg (le_max_right _ _)
      (posDenominator_pos _ _ _ _ ε hε _ _).le

theorem attentionDiscount_nonneg {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (x : Vec (K*D))
    (path : Paths (attentionTrace A Wv bv tail α β ε x)) :
    0 ≤ attentionDiscount A Wv bv tail α β ε x path := by
  apply mul_nonneg _ (rgDiscount_nonneg tail α β ε hα hβ _ _)
  split_ifs
  · exact mul_nonneg (by norm_num) hβ
  · exact mul_nonneg (by norm_num) hα

theorem attentionOccupation_nonneg {T K C D m : ℕ} (A : Matrix (Fin T) (Fin K) ℝ)
    (Wv : Matrix (Fin C) (Fin D) ℝ) (bv : Vec C) (tail : Network (T*C) m)
    (α β ε : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 < ε) (x : Vec (K*D))
    (j : Fin m) (i : Fin (K*D)) (p : Bool) :
    0 ≤ attentionOccupation A Wv bv tail α β ε x j i p :=
  Finset.sum_nonneg fun path _ => mul_nonneg (attentionDiscount_nonneg A Wv bv tail α β ε hα hβ x path)
    (attentionProbability_nonneg A Wv bv tail α β ε hε x j i p path)

end Thesis.AttentionBackward
