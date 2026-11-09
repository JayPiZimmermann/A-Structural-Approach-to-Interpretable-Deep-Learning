import HiddenMonotonicity.Backward
import HiddenMonotonicity.ShiftWeights

namespace HiddenMonotonicity
open Matrix
open scoped BigOperators

/-- Ordered product D_i D_(i+1) ... D_(t-1). Products are empty when t≤i.
Explicitly ordered because matrix factors need not commute. -/
def intervalProduct {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (i : ℕ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | t+1 => if i ≤ t then intervalProduct D i t * D t else 1

theorem intervalProduct_self {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (t : ℕ) :
    intervalProduct D t t = 1 := by
  cases t with
  | zero => rfl
  | succ t => simp [intervalProduct]

theorem transported_product {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (v : Matrix Unit (Fin n) ℝ) (t : ℕ) :
    transported D v t = v * intervalProduct D 0 t := by
  induction t with
  | zero => simp [transported, intervalProduct]
  | succ t ih => simp [transported, intervalProduct, ih, Matrix.mul_assoc]

/-- Exact finite-sum formula for every propagated source term. -/
theorem sources_sum {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℕ → Matrix Unit (Fin n) ℝ) (t : ℕ) :
    sources D b t = ∑ i ∈ Finset.range t, b i * intervalProduct D (i+1) t := by
  induction t with
  | zero => simp [sources]
  | succ t ih =>
      rw [sources, ih, Finset.sum_range_succ, intervalProduct_self, Matrix.mul_one]
      congr 1
      rw [Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hil : i+1 ≤ t := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
      simp only [intervalProduct, if_pos hil, Matrix.mul_assoc]

/-- Full ordered finite-sum solution of the exact backward affine recurrence.
For split sensitivities v is the terminal half-gradient, and b_i is half the
masked absolute-tail source, with its corrected shift coefficient. -/
theorem affine_finite_sum {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℕ → Matrix Unit (Fin n) ℝ) (v : Matrix Unit (Fin n) ℝ) (t : ℕ) :
    affineBack D b v t = v * intervalProduct D 0 t -
      ∑ i ∈ Finset.range t, b i * intervalProduct D (i+1) t := by
  rw [affine_closed_form, transported_product, sources_sum]

/-- Scalar shift factor multiplying the Q-source at backward-time i.
Backward-time 0 denotes the terminal/output layer, so the local shift at i+1
is excluded from the source generated on transition i→i+1. -/
noncomputable def shiftedSource {n : ℕ} (Q : ℕ → Matrix Unit (Fin n) ℝ) (α : ℕ → ℝ)
    (i : ℕ) : Matrix Unit (Fin n) ℝ := (shiftCoefficient α i / 2) • Q i

noncomputable def qSum {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Q : ℕ → Matrix Unit (Fin n) ℝ) (α : ℕ → ℝ) (t : ℕ) :=
  ∑ i ∈ Finset.range t, shiftCoefficient α i • (Q i * intervalProduct D (i+1) t)

theorem shifted_source_sum {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (Q : ℕ → Matrix Unit (Fin n) ℝ) (α : ℕ → ℝ) (t : ℕ) :
    (∑ i ∈ Finset.range t, shiftedSource Q α i * intervalProduct D (i+1) t) =
      (1/2 : ℝ) • qSum D Q α t := by
  simp only [qSum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [shiftedSource, Matrix.smul_mul, smul_smul]
  congr 1
  ring

/-- Corrected printed form of the g-head shifted gradient finite sum. -/
theorem shifted_gradient_g_finite_sum {n : ℕ}
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (Q : ℕ → Matrix Unit (Fin n) ℝ)
    (α : ℕ → ℝ) (v : Matrix Unit (Fin n) ℝ) (t : ℕ) :
    affineBack D (shiftedSource Q α) ((1/2 : ℝ) • v) t =
      (1/2 : ℝ) • (v * intervalProduct D 0 t - qSum D Q α t) := by
  rw [affine_finite_sum, shifted_source_sum, Matrix.smul_mul, smul_sub]

/-- Corrected printed form of the h-head shifted gradient finite sum. -/
theorem shifted_gradient_h_finite_sum {n : ℕ}
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (Q : ℕ → Matrix Unit (Fin n) ℝ)
    (α : ℕ → ℝ) (v : Matrix Unit (Fin n) ℝ) (t : ℕ) :
    affineBack D (shiftedSource Q α) ((-1/2 : ℝ) • v) t =
      (-1/2 : ℝ) • (v * intervalProduct D 0 t + qSum D Q α t) := by
  rw [affine_finite_sum, shifted_source_sum, Matrix.smul_mul]
  module

/-- The shifted head difference reconstructs the original backward product. -/
theorem shifted_heads_reconstruct {n : ℕ}
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (Q : ℕ → Matrix Unit (Fin n) ℝ)
    (α : ℕ → ℝ) (v : Matrix Unit (Fin n) ℝ) (t : ℕ) :
    affineBack D (shiftedSource Q α) ((1/2 : ℝ) • v) t -
      affineBack D (shiftedSource Q α) ((-1/2 : ℝ) • v) t =
      v * intervalProduct D 0 t := by
  rw [shifted_gradient_g_finite_sum, shifted_gradient_h_finite_sum]
  module

end HiddenMonotonicity
