import HiddenMonotonicity.Core
import Mathlib.Data.Matrix.Mul

namespace HiddenMonotonicity
open Matrix

/-- Finite feedforward networks of arbitrary, varying width, including split biases.
Wp and Wn need not be disjoint for correctness; positivity is needed for monotonicity. -/
inductive Network : ℕ → ℕ → Type
  | output (n : ℕ) : Network n n
  | layer {n k m : ℕ} (Wp Wn : Matrix (Fin k) (Fin n) ℝ)
      (bp bn : Fin k → ℝ) (tail : Network k m) : Network n m

def Network.eval {n m} : Network n m → (Fin n → ℝ) → (Fin m → ℝ)
  | .output _, x => x
  | .layer wp wn bp bn tail, x =>
      tail.eval (fun i => relu (((wp-wn).mulVec x + (bp-bn)) i))

def Network.split {n m} : Network n m → (Fin n → ℝ) → (Fin n → ℝ) →
    (Fin m → ℝ) × (Fin m → ℝ)
  | .output _, p, n => (p,n)
  | .layer wp wn bp bn tail, p, n =>
      let zp := wp.mulVec p + wn.mulVec n + bp
      let zn := wn.mulVec p + wp.mulVec n + bn
      tail.split (fun i => max (zp i) (zn i)) zn

theorem layer_difference {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn p n' : _) :
    (fun i => max ((wp.mulVec p + wn.mulVec n' + bp) i)
      ((wn.mulVec p + wp.mulVec n' + bn) i)) -
      (wn.mulVec p + wp.mulVec n' + bn) =
      (fun i => relu (((wp-wn).mulVec (p-n') + (bp-bn)) i)) := by
  funext i
  simp only [Pi.sub_apply, max_sub, sub_mulVec, mulVec_sub, Pi.add_apply]
  congr 1
  ring

/-- Complete forward correctness, not merely a single-layer scalar identity. -/
theorem Network.correct {n m} (net : Network n m) (p q : Fin n → ℝ) :
    (net.split p q).1 - (net.split p q).2 = net.eval (p-q) := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [Network.split, Network.eval]
      rw [ih, layer_difference]

/-- Common-mode shift propagated through absolute-weight sums. -/
def Network.common {n m} : Network n m → (Fin n → ℝ) → (Fin m → ℝ)
  | .output _, c => c
  | .layer wp wn _ _ tail, c => tail.common ((wp+wn).mulVec c)

theorem shifted_layer_preactivation {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (b : Fin k → ℝ) (p q c : Fin n → ℝ) :
    wp.mulVec (p+c) + wn.mulVec (q+c) + b =
      (wp.mulVec p + wn.mulVec q + b) + (wp+wn).mulVec c := by
  simp only [mulVec_add, add_mulVec]
  abel

/-- Entire varying-width network common-shift law, including split biases. -/
theorem Network.shift {n m} (net : Network n m) (p q c : Fin n → ℝ) :
    net.split (p+c) (q+c) =
      ((net.split p q).1 + net.common c, (net.split p q).2 + net.common c) := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [Network.split, Network.common]
      rw [shifted_layer_preactivation, shifted_layer_preactivation]
      have hc : (wn+wp).mulVec c = (wp+wn).mulVec c := by rw [add_comm wn wp]
      rw [hc]
      have hm :
          (fun i => max (((wp.mulVec p + wn.mulVec q + bp) + (wp+wn).mulVec c) i)
             (((wn.mulVec p + wp.mulVec q + bn) + (wp+wn).mulVec c) i)) =
          (fun i => max ((wp.mulVec p + wn.mulVec q + bp) i)
             ((wn.mulVec p + wp.mulVec q + bn) i)) + (wp+wn).mulVec c := by
        funext i
        exact max_common_shift _ _ _
      rw [hm, ih]

end HiddenMonotonicity
