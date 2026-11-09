import HiddenMonotonicity.LayerNormDCLift

set_option autoImplicit false
open HiddenMonotonicity.SmoothDC

-- The represented variance is zero on the whole diagonal, including signed streams.
example (ε a : ℝ) (hε : 0 < ε) :
    (inverseSqrtPair ε (a, a)).1 - (inverseSqrtPair ε (a, a)).2 =
      (Real.sqrt ε)⁻¹ := by
  simpa using inverseSqrtPair_difference ε hε (a, a) (by simp)

-- A positive epsilon is a nonempty hypothesis, and the corner output is finite.
example : inverseSqrtPair 1 (0, 0) = (1, 0) := by
  norm_num [inverseSqrtPair, inverseSqrtExtension, inverseSqrtSlope]

-- The extension below zero is deliberate; no square-root recovery is claimed there.
example : inverseSqrtPair 1 (0, 1) = (3 / 2, 0) := by
  norm_num [inverseSqrtPair, inverseSqrtExtension, inverseSqrtSlope]

-- Global isotonicity does not require nonnegative streams or represented variance.
example (ε : ℝ) (hε : 0 < ε) (a b : ℝ × ℝ) (hab : a ≤ b) :
    inverseSqrtPair ε a ≤ inverseSqrtPair ε b :=
  inverseSqrtPair_monotone ε hε hab

-- Nonnegativity covers the actual independent-stream composition domain.
example (ε x y : ℝ) (hε : 0 < ε) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (inverseSqrtPair ε (x, y)).1 ∧ 0 ≤ (inverseSqrtPair ε (x, y)).2 :=
  inverseSqrtPair_nonneg ε hε (x, y) ⟨hx, hy⟩

-- Recovery works at any positive represented variance, independently of stream signs.
example (ε x y : ℝ) (hε : 0 < ε) (hxy : y ≤ x) :
    (inverseSqrtPair ε (x, y)).1 - (inverseSqrtPair ε (x, y)).2 =
      (Real.sqrt (ε + (x - y)))⁻¹ :=
  inverseSqrtPair_difference ε hε (x, y) (sub_nonneg.mpr hxy)
