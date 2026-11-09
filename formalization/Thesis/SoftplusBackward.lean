import Thesis.RoutingBackward
import HiddenMonotonicity.Convexity

/-! The Softplus variant uses the same varying-width `Network` weights and biases.
Its actual derivative is identified with discounted stochastic stopping paths. -/
noncomputable section
namespace Thesis.SoftplusBackward
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.Regularization

def softLayer {n k} (θ : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) : Vec k := fun j => softplus θ (preactivation wp wn bp bn x j)

def softSigned {n k} (θ : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) : Matrix (Fin k) (Fin n) ℝ :=
  fun j i => gate θ (preactivation wp wn bp bn x j) * (wp j i - wn j i)

def softEval {n m} (θ : ℝ) : Network n m → Vec n → Vec m
  | .output _, x => x
  | .layer wp wn bp bn tail, x => softEval θ tail (softLayer θ wp wn bp bn x)

def softTrace {n m} (θ : ℝ) : (net : Network n m) → Vec n → MaskedTrace n m
  | .output n, _ => .output n
  | .layer wp wn bp bn tail, x => .layer
      (fun j i => gate θ (preactivation wp wn bp bn x j) * wp j i)
      (fun j i => gate θ (preactivation wp wn bp bn x j) * wn j i)
      (fun _ => true) (softTrace θ tail (softLayer θ wp wn bp bn x))

theorem softLayer_hasFDerivAt {n k} (θ : ℝ) (hθ : 0 < θ)
    (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : Vec n) :
    HasFDerivAt (softLayer θ wp wn bp bn) (matrixCLM (softSigned θ wp wn bp bn x)) x := by
  apply hasFDerivAt_pi'.mpr
  intro j
  have ha : HasFDerivAt (fun y : Vec n => matrixCLM (wp-wn) y + (bp-bn))
      (matrixCLM (wp-wn)) x := (matrixCLM (wp-wn)).hasFDerivAt.add_const (bp-bn)
  have hf : HasFDerivAt (fun y : Vec n => preactivation wp wn bp bn y j)
      ((ContinuousLinearMap.proj j).comp (matrixCLM (wp-wn))) x := by
    convert (ContinuousLinearMap.proj j).hasFDerivAt.comp x ha using 1
    rfl
  have hd := (hasDerivAt_softplus θ (preactivation wp wn bp bn x j) hθ).comp_hasFDerivAt x hf
  convert hd using 1
  · rfl
  · ext v
    change (∑ i, gate θ (preactivation wp wn bp bn x j) * (wp j i-wn j i) * v i) =
      gate θ (preactivation wp wn bp bn x j) * ∑ i, (wp j i-wn j i) * v i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem softTrace_layer_map {n k} (θ : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : Vec n) :
    MaskedTrace.signedMap
      (fun j i => gate θ (preactivation wp wn bp bn x j) * wp j i)
      (fun j i => gate θ (preactivation wp wn bp bn x j) * wn j i) (fun _ => true) =
      matrixCLM (softSigned θ wp wn bp bn x) := by
  rw [signedMap_matrix
    (fun j i => gate θ (preactivation wp wn bp bn x j) * wp j i)
    (fun j i => gate θ (preactivation wp wn bp bn x j) * wn j i) (fun _ => true)]
  congr 1
  ext j i
  change gate θ (preactivation wp wn bp bn x j) * wp j i -
    gate θ (preactivation wp wn bp bn x j) * wn j i =
    gate θ (preactivation wp wn bp bn x j) * (wp j i - wn j i)
  ring

/-- Actual full-network Fréchet derivative, without assuming a backward recurrence. -/
theorem softEval_hasFDerivAt {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ) (x : Vec n) :
    HasFDerivAt (softEval θ net) (softTrace θ net x).originalJac x := by
  induction net with
  | output n => exact (ContinuousLinearMap.id ℝ _).hasFDerivAt
  | layer wp wn bp bn tail ih =>
      change HasFDerivAt (softEval θ tail ∘ softLayer θ wp wn bp bn)
        ((softTrace θ tail (softLayer θ wp wn bp bn x)).originalJac.comp
          (MaskedTrace.signedMap
            (fun j i => gate θ (preactivation wp wn bp bn x j) * wp j i)
            (fun j i => gate θ (preactivation wp wn bp bn x j) * wn j i) (fun _ => true))) x
      rw [softTrace_layer_map]
      exact (ih (softLayer θ wp wn bp bn x)).comp x (softLayer_hasFDerivAt θ hθ wp wn bp bn x)

def PositiveFanIn {n m} : Network n m → Prop
  | .output _ => True
  | .layer wp wn _ _ tail => (∀ j, 0 < fanIn wp wn j) ∧ PositiveFanIn tail

/-- Stochastic sigmoid continuation followed by the original weight-normalized kernel. -/
def softProbability {n m} (θ : ℝ) : (net : Network n m) → (x : Vec n) →
    Fin m → Fin n → Bool → Paths (softTrace θ net x) → ℝ
  | .output _, _, j, i, p, _ => if j = i ∧ p = false then 1 else 0
  | .layer wp wn bp bn tail, x, j, i, p, path =>
      (gate θ (preactivation wp wn bp bn x path.1) *
        (if path.2.1 then wn path.1 i else wp path.1 i) / fanIn wp wn path.1) *
      softProbability θ tail (softLayer θ wp wn bp bn x) j path.1 (Bool.xor p path.2.1) path.2.2

/-- Original fan-in discounts: the soft gate belongs to the probability law. -/
def softDiscount {n m} (θ : ℝ) : (net : Network n m) → (x : Vec n) →
    Paths (softTrace θ net x) → ℝ
  | .output _, _, _ => 1
  | .layer wp wn bp bn tail, x, path => fanIn wp wn path.1 *
      softDiscount θ tail (softLayer θ wp wn bp bn x) path.2.2

theorem soft_path_discount_recovery {n m} (net : Network n m) (θ : ℝ)
    (hγ : PositiveFanIn net) (x : Vec n) (j : Fin m) (i : Fin n) (p : Bool)
    (path : Paths (softTrace θ net x)) :
    softDiscount θ net x path * softProbability θ net x j i p path =
      rawWeight (softTrace θ net x) j i p path := by
  induction net generalizing p with
  | output n => simp [softDiscount, softProbability, softTrace, rawWeight]
  | layer wp wn bp bn tail ih =>
      simp only [softDiscount, softProbability, softTrace, rawWeight, ite_true]
      have ht := ih hγ.2 (softLayer θ wp wn bp bn x) j path.1 (Bool.xor p path.2.1) path.2.2
      have hg : fanIn wp wn path.1 ≠ 0 := (hγ.1 _).ne'
      cases hs : path.2.1 <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at *
      all_goals rw [← ht]; field_simp

def softOccupation {n m} (net : Network n m) (θ : ℝ) (x : Vec n)
    (j : Fin m) (i : Fin n) (p : Bool) : ℝ :=
  ∑ path : Paths (softTrace θ net x), softDiscount θ net x path * softProbability θ net x j i p path

theorem soft_occupation_kernels {n m} (net : Network n m) (θ : ℝ)
    (hγ : PositiveFanIn net) (x : Vec n) (j : Fin m) (i : Fin n) :
    softOccupation net θ x j i false = (occupations (softTrace θ net x)).1 j i ∧
    softOccupation net θ x j i true = (occupations (softTrace θ net x)).2 j i := by
  simp only [softOccupation, soft_path_discount_recovery net θ hγ]
  exact raw_path_integral _ j i

theorem softProbability_nonneg {n m} (net : Network n m) (θ : ℝ)
    (hw : net.Nonnegative) (hγ : PositiveFanIn net) (x : Vec n)
    (j : Fin m) (i : Fin n) (p : Bool) (path : Paths (softTrace θ net x)) :
    0 ≤ softProbability θ net x j i p path := by
  induction net generalizing p with
  | output n => simp only [softProbability]; split_ifs <;> norm_num
  | layer wp wn bp bn tail ih =>
      simp only [softProbability]
      apply mul_nonneg _ (ih hw.2.2 hγ.2 (softLayer θ wp wn bp bn x) j path.1
        (Bool.xor p path.2.1) path.2.2)
      apply div_nonneg _ (hγ.1 _).le
      apply mul_nonneg (gate_pos θ _).le
      split_ifs
      · exact hw.2.1 _ _
      · exact hw.1 _ _

theorem softDiscount_pos {n m} (net : Network n m) (θ : ℝ) (hγ : PositiveFanIn net)
    (x : Vec n) (path : Paths (softTrace θ net x)) : 0 < softDiscount θ net x path := by
  induction net with
  | output n => exact zero_lt_one
  | layer wp wn bp bn tail ih => exact mul_pos (hγ.1 _) (ih hγ.2 _ path.2.2)

theorem softOccupation_nonneg {n m} (net : Network n m) (θ : ℝ)
    (hw : net.Nonnegative) (hγ : PositiveFanIn net) (x : Vec n)
    (j : Fin m) (i : Fin n) (p : Bool) : 0 ≤ softOccupation net θ x j i p :=
  Finset.sum_nonneg fun path _ => mul_nonneg (softDiscount_pos net θ hγ x path).le
    (softProbability_nonneg net θ hw hγ x j i p path)

/-- Thesis Theorem `ptnb:thm:softplus-gradient`: the derivative of the actual
full Softplus network equals the signed discounted sigmoid-policy occupation. -/
theorem thesis_softplus_gradient {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (_hw : net.Nonnegative) (hγ : PositiveFanIn net) (x : Vec n) (j : Fin m) (i : Fin n) :
    fderiv ℝ (softEval θ net) x (Pi.single i 1) j =
      softOccupation net θ x j i false - softOccupation net θ x j i true := by
  rw [(softEval_hasFDerivAt net θ hθ x).fderiv, originalJac_occupation]
  change ((fun j i => (occupations (softTrace θ net x)).1 j i -
    (occupations (softTrace θ net x)).2 j i) *ᵥ (Pi.single i 1)) j = _
  simp [Matrix.mulVec, dotProduct, Pi.single_apply,
    (soft_occupation_kernels net θ hγ x j i).1, (soft_occupation_kernels net θ hγ x j i).2]

end Thesis.SoftplusBackward
