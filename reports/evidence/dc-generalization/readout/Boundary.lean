import HiddenMonotonicity.ConvexMonotoneReadout

noncomputable section
set_option autoImplicit false
open HiddenMonotonicity
open scoped BigOperators

namespace AffineDecompositionBoundary

/-- A zero-width backbone with a negative output bias must keep its signed
negative value; an extra output activation would fail this boundary. -/
example (φ : (ℝ × ℝ) → ℝ × ℝ) (x : PairVec 0) :
    ((Network.output 0).affineDecomposeWith φ
      (0 : Matrix (Fin 1) (Fin 0) ℝ) 0 (fun _ => -1) 0 x).1 0 -
    ((Network.output 0).affineDecomposeWith φ
      (0 : Matrix (Fin 1) (Fin 0) ℝ) 0 (fun _ => -1) 0 x).2 0 = -1 := by
  simp [Network.affineDecomposeWith, preP_apply, preN]

/-- Empty output spaces are included; the same theorem requires no positive
width assumption anywhere in the network or readout. -/
example (φ : (ℝ × ℝ) → ℝ × ℝ) :
    Monotone ((Network.output 0).affineDecomposeWith φ
      (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 0 0) := by
  exact (Network.output 0).affineDecomposeWith_monotone_of_monotone
    φ monotone_id 0 0 (by simp) (by simp) 0 0

/-- A negative signed readout weight also preserves a negative output, even
when the original scalar input and all split weights are nonnegative. -/
example (φ : (ℝ × ℝ) → ℝ × ℝ) :
    ((Network.output 1).affineDecomposeWith φ
      (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 0 0 ((fun _ => 1),0)).1 0 -
    ((Network.output 1).affineDecomposeWith φ
      (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1) 0 0 ((fun _ => 1),0)).2 0 = -1 := by
  norm_num [Network.affineDecomposeWith, Network.decomposeWith, preP, preN,
    matrixCLM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  change (∑ _ : Fin 1, (1 : ℝ) * 1) = 1
  norm_num [Fin.sum_univ_succ]

/-- The signed input embedding is not monotone in raw input coordinates. The
signed-input DC theorem therefore correctly promises convexity and recovery. -/
example : ¬ Monotone (signedInput (n := 1)) := by
  intro h
  have hxy : (fun _ : Fin 1 => (-1 : ℝ)) ≤ (fun _ : Fin 1 => (0 : ℝ)) := by
    intro i
    norm_num
  have hq := (h hxy).2 0
  norm_num [signedInput] at hq

end AffineDecompositionBoundary
