import HiddenMonotonicity.Core
import Mathlib.Data.Matrix.Mul

namespace HiddenMonotonicity
open Matrix

/-- Rectangular Jacobian pullback: p,n are head derivatives at the later layer,
M is its activation mask, Wp,Wn are the positive/negative weight parts. -/
def matrixBackPos {k n : ℕ} (p q : Matrix Unit (Fin k) ℝ)
    (M : Matrix (Fin k) (Fin k) ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ) :=
    p * (M*wp+(1-M)*wn)+q*wn

def matrixBackNeg {k n : ℕ} (p q : Matrix Unit (Fin k) ℝ)
    (M : Matrix (Fin k) (Fin k) ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ) :=
    p * (M*wn+(1-M)*wp)+q*wp

theorem matrix_backward_sum {k n : ℕ} (p q : Matrix Unit (Fin k) ℝ)
    (M : Matrix (Fin k) (Fin k) ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ) :
    matrixBackPos p q M wp wn + matrixBackNeg p q M wp wn = (p+q)*(wp+wn) := by
  simp only [matrixBackPos, matrixBackNeg, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_assoc]
  abel

theorem matrix_backward_difference {k n : ℕ} (p q : Matrix Unit (Fin k) ℝ)
    (M : Matrix (Fin k) (Fin k) ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ) :
    matrixBackPos p q M wp wn - matrixBackNeg p q M wp wn =
      (p-q)*(M*(wp-wn)) - (p+q)*((1-M)*(wp-wn)) := by
  simp only [matrixBackPos, matrixBackNeg, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_assoc]
  abel

/-- Equal row-vector subtraction preserves the difference, for any width. -/
theorem matrix_shift_difference {n : ℕ} (p q c : Matrix Unit (Fin n) ℝ) :
    (p-c)-(q-c) = p-q := by abel

/-- Four-head invariant, valid dimension by dimension. -/
theorem matrix_two_head_reconstruction {k n : ℕ}
    (pg ng ph nh : Matrix Unit (Fin k) ℝ)
    (M : Matrix (Fin k) (Fin k) ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hsum : pg+ng=ph+nh) :
    (matrixBackPos pg ng M wp wn - matrixBackNeg pg ng M wp wn) -
      (matrixBackPos ph nh M wp wn - matrixBackNeg ph nh M wp wn) =
      ((pg-ng)-(ph-nh))*(M*(wp-wn)) := by
  rw [matrix_backward_difference, matrix_backward_difference, hsum]
  simp only [Matrix.sub_mul]
  abel

/-- General-depth affine recurrence and its source-sum solution. The transition
matrices may be noncommuting; an accumulator stores already propagated sources. -/
def transported {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (v : Matrix Unit (Fin n) ℝ) : ℕ → Matrix Unit (Fin n) ℝ
  | 0 => v
  | t+1 => transported D v t * D t

def sources {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℕ → Matrix Unit (Fin n) ℝ) : ℕ → Matrix Unit (Fin n) ℝ
  | 0 => 0
  | t+1 => sources D b t * D t + b t

def affineBack {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℕ → Matrix Unit (Fin n) ℝ) (v : Matrix Unit (Fin n) ℝ) :
    ℕ → Matrix Unit (Fin n) ℝ
  | 0 => v
  | t+1 => affineBack D b v t * D t - b t

theorem affine_closed_form {n : ℕ} (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℕ → Matrix Unit (Fin n) ℝ) (v : Matrix Unit (Fin n) ℝ) (t : ℕ) :
    affineBack D b v t = transported D v t - sources D b t := by
  induction t with
  | zero => simp [affineBack, transported, sources]
  | succ t ih =>
      simp only [affineBack, transported, sources, ih, Matrix.sub_mul]
      abel

end HiddenMonotonicity
