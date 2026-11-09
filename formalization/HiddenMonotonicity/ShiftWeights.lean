import HiddenMonotonicity.Core
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
namespace HiddenMonotonicity
open scoped BigOperators

/-- Backward-time indexing: 0 is the output, t+1 the next earlier layer. -/
def shiftCoefficient (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1-2*α 0
  | t+1 => (1-2*α (t+1))*shiftCoefficient α t

theorem shiftCoefficient_product (α : ℕ → ℝ) (t : ℕ) :
    shiftCoefficient α t = ∏ i ∈ Finset.range (t+1), (1-2*α i) := by
  induction t with
  | zero => simp [shiftCoefficient]
  | succ t ih =>
      rw [shiftCoefficient, ih, Finset.prod_range_succ (n := t+1)]
      exact mul_comm _ _

/-- The source term for the transition t→t+1 uses the coefficient BEFORE
subtracting the new local shift α(t+1), as the latter cancels in the difference. -/
theorem shifted_source_coefficient (p n m wp wn α c A : ℝ)
    (h : p+n=c*A) :
    let bp := backPos p n m wp wn
    let bn := backNeg p n m wp wn
    ((bp-α*(bp+bn))-(bn-α*(bp+bn)))/2 =
      ((p-n)/2)*m*(wp-wn) - c*A*(1-m)*(wp-wn)/2 := by
  dsimp
  rw [shifted_backward_difference, h]
  ring

/-- A constant shift is innocuous, but an input-dependent shift changes
individual head derivatives even though the difference stays unchanged. -/
theorem input_dependent_shift_counterexample (x : ℝ) (hx : 0 < x) :
    max (x+x) (0+x) = 2*x ∧ (0+x=x) ∧
    (2*x-x=x) := by
  constructor
  · rw [max_eq_left (by linarith)]; ring
  constructor <;> ring

end HiddenMonotonicity
