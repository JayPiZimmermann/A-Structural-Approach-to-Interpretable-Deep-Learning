import Thesis.BackwardGames
import Thesis.Regularization

/-! Alpha-beta LRP derived from the shared network, with the game probability
and discount kept distinct. Forward activations and signed contributions are
computed from the original weights, rather than assumed routing coefficients. -/
noncomputable section
namespace Thesis.RoutingBackward
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames

/-- Original affine preactivation, including the original signed bias. -/
def preactivation {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : Vec n) : Vec k :=
  (wp-wn).mulVec x + (bp-bn)

def posContribution {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (x : Vec n) :
    Matrix (Fin k) (Fin n) ℝ := fun j i => max (x i * (wp j i - wn j i)) 0

def negContribution {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (x : Vec n) :
    Matrix (Fin k) (Fin n) ℝ := fun j i => max (-(x i * (wp j i - wn j i))) 0

def posDenominator {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (x : Vec n) (j : Fin k) : ℝ :=
  (∑ i, posContribution wp wn x j i) + max (bp j - bn j) 0 + ε

def negDenominator {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (ε : ℝ) (x : Vec n) (j : Fin k) : ℝ :=
  (∑ i, negContribution wp wn x j i) + max (-(bp j - bn j)) 0 + ε

/-- The actual signed alpha-beta local rule, including stabilizer leakage and closed gates. -/
def lrpLayer {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (α β ε : ℝ) (x : Vec n) : Matrix (Fin k) (Fin n) ℝ := fun j i =>
  if 0 < preactivation wp wn bp bn x j then
    α * posContribution wp wn x j i / posDenominator wp wn bp bn ε x j -
      β * negContribution wp wn x j i / negDenominator wp wn bp bn ε x j else 0

/-- Full layer-by-layer relevance propagation, from an arbitrary output relevance vector. -/
def lrp {n m} (α β ε : ℝ) : (net : Network n m) → Vec n → Vec m → Vec n
  | .output _, _, R => R
  | .layer wp wn bp bn tail, x, R =>
      (lrp α β ε tail (fun j => relu (preactivation wp wn bp bn x j)) R) ᵥ*
        lrpLayer wp wn bp bn α β ε x

/-- Derive the game's signed weighted trace from the original forward calculation. -/
def routingTrace {n m} (α β ε : ℝ) : (net : Network n m) → Vec n → MaskedTrace n m
  | .output n, _ => .output n
  | .layer wp wn bp bn tail, x =>
      .layer
        (fun j i => α * posContribution wp wn x j i / posDenominator wp wn bp bn ε x j)
        (fun j i => β * negContribution wp wn x j i / negDenominator wp wn bp bn ε x j)
        (fun j => decide (0 < preactivation wp wn bp bn x j))
        (routingTrace α β ε tail (fun j => relu (preactivation wp wn bp bn x j)))

theorem signed_routing_layer {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (α β ε : ℝ) (x : Vec n) :
    gated (fun j => decide (0 < preactivation wp wn bp bn x j))
      ((fun j i => α * posContribution wp wn x j i / posDenominator wp wn bp bn ε x j) -
       (fun j i => β * negContribution wp wn x j i / negDenominator wp wn bp bn ε x j)) =
      lrpLayer wp wn bp bn α β ε x := by
  ext j i
  simp [gated, lrpLayer]

/-- The complete alpha-beta recurrence is the signed product of the derived routing trace. -/
theorem full_lrp_matrix {n m} (net : Network n m) (α β ε : ℝ) (x : Vec n) (R : Vec m) :
    lrp α β ε net x R = R ᵥ* signedProduct (routingTrace α β ε net x) := by
  induction net with
  | output n => simp [lrp, routingTrace, signedProduct]
  | layer wp wn bp bn tail ih =>
      simp only [lrp, routingTrace, signedProduct, ih]
      rw [Matrix.vecMul_vecMul]
      exact congrArg (fun M : Matrix _ _ ℝ => R ᵥ*
        (signedProduct (routingTrace α β ε tail (fun j => relu (preactivation wp wn bp bn x j))) * M))
        (signed_routing_layer wp wn bp bn α β ε x).symm

/-- Routing probabilities: one half for each sign stream, then normalized contribution mass. -/
def rgProbability {n m} (α β ε : ℝ) : (net : Network n m) → (x : Vec n) →
    Fin m → Fin n → Bool → Paths (routingTrace α β ε net x) → ℝ
  | .output _, _, j, i, p, _ => if j = i ∧ p = false then 1 else 0
  | .layer wp wn bp bn tail, x, j, i, p, path =>
      (if 0 < preactivation wp wn bp bn x path.1 then
        (if path.2.1 then negContribution wp wn x path.1 i / negDenominator wp wn bp bn ε x path.1
         else posContribution wp wn x path.1 i / posDenominator wp wn bp bn ε x path.1) / 2 else 0) *
      rgProbability α β ε tail (fun h => relu (preactivation wp wn bp bn x h))
        j path.1 (Bool.xor p path.2.1) path.2.2

/-- Branch discounts compensate the fair stream split and impose alpha-beta path weights. -/
def rgDiscount {n m} (α β ε : ℝ) : (net : Network n m) → (x : Vec n) →
    Paths (routingTrace α β ε net x) → ℝ
  | .output _, _, _ => 1
  | .layer wp wn bp bn tail, x, path =>
      (if path.2.1 then 2 * β else 2 * α) *
      rgDiscount α β ε tail (fun h => relu (preactivation wp wn bp bn x h)) path.2.2

theorem rg_path_discount_recovery {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (j : Fin m) (i : Fin n) (p : Bool)
    (path : Paths (routingTrace α β ε net x)) :
    rgDiscount α β ε net x path * rgProbability α β ε net x j i p path =
      rawWeight (routingTrace α β ε net x) j i p path := by
  induction net generalizing p with
  | output n => simp [rgDiscount, rgProbability, rawWeight, routingTrace]
  | layer wp wn bp bn tail ih =>
      simp only [rgDiscount, rgProbability, routingTrace, rawWeight, decide_eq_true_eq]
      have ht := ih (fun h => relu (preactivation wp wn bp bn x h)) j path.1
        (Bool.xor p path.2.1) path.2.2
      split_ifs <;> simp only [← ht] <;> ring

/-- Discounted ordinary-input occupation of the actual alpha-beta routing game. -/
def rgOccupation {n m} (net : Network n m) (α β ε : ℝ) (x : Vec n)
    (j : Fin m) (i : Fin n) (p : Bool) : ℝ :=
  ∑ path : Paths (routingTrace α β ε net x),
    rgDiscount α β ε net x path * rgProbability α β ε net x j i p path

theorem rg_occupation_kernels {n m} (net : Network n m) (α β ε : ℝ) (x : Vec n)
    (j : Fin m) (i : Fin n) :
    rgOccupation net α β ε x j i false = (occupations (routingTrace α β ε net x)).1 j i ∧
    rgOccupation net α β ε x j i true = (occupations (routingTrace α β ε net x)).2 j i := by
  simp only [rgOccupation, rg_path_discount_recovery]
  exact raw_path_integral _ j i

/-- Thesis Theorem `ptnb:thm:ab-recovery` and `ptnb:thm:lrp-recovery`:
the explicit alpha-beta LRP recurrence on the entire shared MLP equals the
signed discounted routing occupation, for the anchor policies defined above. -/
theorem thesis_alpha_beta_recovery {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (R : Vec m) (i : Fin n) :
    lrp α β ε net x R i = ∑ j, R j *
      (rgOccupation net α β ε x j i false - rgOccupation net α β ε x j i true) := by
  rw [full_lrp_matrix, ← occupation_difference]
  change (∑ j, R j * ((occupations (routingTrace α β ε net x)).1 -
    (occupations (routingTrace α β ε net x)).2) j i) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [(rg_occupation_kernels net α β ε x j i).1, (rg_occupation_kernels net α β ε x j i).2]
  rfl

theorem posDenominator_pos {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 < ε) (x : Vec n) (j : Fin k) :
    0 < posDenominator wp wn bp bn ε x j := by
  have hs : 0 ≤ ∑ i, posContribution wp wn x j i :=
    Finset.sum_nonneg fun i _ => le_max_right _ _
  have hb : 0 ≤ max (bp j - bn j) 0 := le_max_right _ _
  unfold posDenominator
  linarith

theorem negDenominator_pos {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0 < ε) (x : Vec n) (j : Fin k) :
    0 < negDenominator wp wn bp bn ε x j := by
  have hs : 0 ≤ ∑ i, negContribution wp wn x j i :=
    Finset.sum_nonneg fun i _ => le_max_right _ _
  have hb : 0 ≤ max (-(bp j - bn j)) 0 := le_max_right _ _
  unfold negDenominator
  linarith

theorem rgProbability_nonneg {n m} (net : Network n m) (α β ε : ℝ) (hε : 0 < ε)
    (x : Vec n) (j : Fin m) (i : Fin n) (p : Bool)
    (path : Paths (routingTrace α β ε net x)) :
    0 ≤ rgProbability α β ε net x j i p path := by
  induction net generalizing p with
  | output n => simp only [rgProbability]; split_ifs <;> norm_num
  | layer wp wn bp bn tail ih =>
      simp only [rgProbability]
      apply mul_nonneg _ (ih (fun h => relu (preactivation wp wn bp bn x h)) j path.1
        (Bool.xor p path.2.1) path.2.2)
      split_ifs
      · exact div_nonneg (div_nonneg (le_max_right _ _)
          (negDenominator_pos wp wn bp bn ε hε x _).le) (by norm_num)
      · exact div_nonneg (div_nonneg (le_max_right _ _)
          (posDenominator_pos wp wn bp bn ε hε x _).le) (by norm_num)
      · exact le_rfl

theorem rgDiscount_nonneg {n m} (net : Network n m) (α β ε : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (x : Vec n) (path : Paths (routingTrace α β ε net x)) :
    0 ≤ rgDiscount α β ε net x path := by
  induction net with
  | output n => exact zero_le_one
  | layer wp wn bp bn tail ih =>
      simp only [rgDiscount]
      apply mul_nonneg _ (ih _ path.2.2)
      split_ifs
      · exact mul_nonneg (by norm_num) hβ
      · exact mul_nonneg (by norm_num) hα

theorem rgOccupation_nonneg {n m} (net : Network n m) (α β ε : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 < ε) (x : Vec n)
    (j : Fin m) (i : Fin n) (p : Bool) : 0 ≤ rgOccupation net α β ε x j i p :=
  Finset.sum_nonneg fun path _ => mul_nonneg (rgDiscount_nonneg net α β ε hα hβ x path)
    (rgProbability_nonneg net α β ε hε x j i p path)

end Thesis.RoutingBackward
