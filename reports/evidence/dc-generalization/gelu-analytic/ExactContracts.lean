import HiddenMonotonicity.GELUInflectionBounds

/-! Handwritten expected contracts for the analytic GELU inflection bounds.
These declarations state the intended mathematics without obtaining their
types from Lean's inferred type of the checked declaration. -/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology
open HiddenMonotonicity.SmoothDC

example : Tendsto standardGaussianCDF atBot (𝓝 (0 : ℝ)) :=
  @standardGaussianCDF_atBot

example : Tendsto standardGaussianCDF atTop (𝓝 (1 : ℝ)) :=
  @standardGaussianCDF_atTop

example : Tendsto (fun x : ℝ => x * standardGaussianDensity x) (cocompact ℝ) (𝓝 (0 : ℝ)) :=
  @standardGaussianDensity_mul_id_cocompact

example : Tendsto gaussianGeluFirst atBot (𝓝 (0 : ℝ)) :=
  @gaussianGeluFirst_atBot

example : Tendsto gaussianGeluFirst atTop (𝓝 (1 : ℝ)) :=
  @gaussianGeluFirst_atTop

example : AntitoneOn gaussianGeluFirst (Iic (-Real.sqrt 2)) :=
  @gaussianGeluFirst_antitone_left

example : MonotoneOn gaussianGeluFirst (Icc (-Real.sqrt 2) (Real.sqrt 2)) :=
  @gaussianGeluFirst_monotone_middle

example : AntitoneOn gaussianGeluFirst (Ici (Real.sqrt 2)) :=
  @gaussianGeluFirst_antitone_right

example : ∀ {x : ℝ}, x ≤ -Real.sqrt 2 →
    gaussianGeluFirst (-Real.sqrt 2) ≤ gaussianGeluFirst x ∧ gaussianGeluFirst x ≤ 0 :=
  @gaussianGeluFirst_left_bounds

example : ∀ {x : ℝ}, -Real.sqrt 2 ≤ x ∧ x ≤ Real.sqrt 2 →
    gaussianGeluFirst (-Real.sqrt 2) ≤ gaussianGeluFirst x ∧
      gaussianGeluFirst x ≤ gaussianGeluFirst (Real.sqrt 2) :=
  @gaussianGeluFirst_middle_bounds

example : ∀ {x : ℝ}, Real.sqrt 2 ≤ x →
    0 ≤ gaussianGeluFirst x ∧ gaussianGeluFirst x ≤ gaussianGeluFirst (Real.sqrt 2) :=
  @gaussianGeluFirst_right_bounds

example : gaussianGeluFirst (-Real.sqrt 2) ≤ 0 ∧
    0 ≤ gaussianGeluFirst (Real.sqrt 2) :=
  @gaussianGeluFirst_inflection_signs

-- The interval endpoints and the central zero are valid consumers.
example : gaussianGeluFirst (-Real.sqrt 2) ≤ 0 :=
  (gaussianGeluFirst_left_bounds (x := -Real.sqrt 2) le_rfl).2

example : 0 ≤ gaussianGeluFirst (Real.sqrt 2) :=
  (gaussianGeluFirst_right_bounds (x := Real.sqrt 2) le_rfl).1

example : gaussianGeluFirst (-Real.sqrt 2) ≤ gaussianGeluFirst 0 ∧
    gaussianGeluFirst 0 ≤ gaussianGeluFirst (Real.sqrt 2) :=
  gaussianGeluFirst_middle_bounds
    ⟨neg_nonpos.mpr (Real.sqrt_nonneg 2), Real.sqrt_nonneg 2⟩

example : gaussianGeluFirst (-Real.sqrt 2) ≤ gaussianGeluFirst (Real.sqrt 2) :=
  (gaussianGeluFirst_middle_bounds
    ⟨neg_le_self (Real.sqrt_nonneg 2), le_rfl⟩).1

#print axioms standardGaussianCDF_atBot
#print axioms standardGaussianCDF_atTop
#print axioms standardGaussianDensity_mul_id_cocompact
#print axioms gaussianGeluFirst_atBot
#print axioms gaussianGeluFirst_atTop
#print axioms gaussianGeluFirst_antitone_left
#print axioms gaussianGeluFirst_monotone_middle
#print axioms gaussianGeluFirst_antitone_right
#print axioms gaussianGeluFirst_left_bounds
#print axioms gaussianGeluFirst_middle_bounds
#print axioms gaussianGeluFirst_right_bounds
#print axioms gaussianGeluFirst_inflection_signs
