import Mathlib.Tactic

namespace HiddenMonotonicity.SoftmaxDC

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem probability_coord_le_one (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (i : ι) : p i ≤ 1 := by
  simpa [hsum] using Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)

theorem probability_two_coord_le_one [DecidableEq ι] (p : ι → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1) {i j : ι}
    (hij : i ≠ j) : p i + p j ≤ 1 := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({i, j} : Finset ι) ⊆ Finset.univ by simp)
    (fun k _ _ => hp k)
  simpa [Finset.sum_pair hij, hsum] using h

theorem weighted_variance_nonneg (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) : 0 ≤ ∑ j, p j * w j :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hp j) (hw j))

theorem probability_second_bounds (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (i : ι) :
    -(∑ j, p j * w j) ≤ p i * (w i - ∑ j, p j * w j) ∧
      p i * (w i - ∑ j, p j * w j) ≤ ∑ j, p j * w j := by
  have hv := weighted_variance_nonneg p hp w hw
  have hi := probability_coord_le_one p hp hsum i
  have hiw := mul_nonneg (hp i) (hw i)
  have hiv := mul_nonneg (hp i) hv
  have hcom := mul_nonneg (sub_nonneg.mpr hi) hv
  have hsingle : p i * w i ≤ ∑ j, p j * w j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hp j) (hw j)) (Finset.mem_univ i)
  constructor <;> nlinarith only [hiw, hiv, hcom, hsingle]

noncomputable def plusCoeff [DecidableEq ι] (p : ι → ℝ) (i j : ι) : ℝ :=
  (p j + p i * ((if i = j then 1 else 0) - p j)) / 2

noncomputable def minusCoeff [DecidableEq ι] (p : ι → ℝ) (i j : ι) : ℝ :=
  (p j - p i * ((if i = j then 1 else 0) - p j)) / 2

theorem plusCoeff_bounds [DecidableEq ι] (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (i j : ι) :
    0 ≤ plusCoeff p i j ∧ plusCoeff p i j ≤ 1 / 2 := by
  have hi := probability_coord_le_one p hp hsum i
  have hj := probability_coord_le_one p hp hsum j
  by_cases hij : i = j
  · subst j
    simp only [plusCoeff, ↓reduceIte]
    have hprod := mul_nonneg (hp i) (sub_nonneg.mpr hi)
    have hsq := sq_nonneg (1 - p i)
    constructor <;> nlinarith only [hp i, hprod, hsq]
  · simp only [plusCoeff, ite_eq_right hij, zero_sub]
    have hprod := mul_nonneg (hp j) (sub_nonneg.mpr hi)
    have hpp := mul_nonneg (hp i) (hp j)
    constructor <;> nlinarith only [hprod, hpp, hj]

theorem minusCoeff_bounds [DecidableEq ι] (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j = 1) (i j : ι) :
    0 ≤ minusCoeff p i j ∧ minusCoeff p i j ≤ 1 / 2 := by
  have hi := probability_coord_le_one p hp hsum i
  have hj := probability_coord_le_one p hp hsum j
  by_cases hij : i = j
  · subst j
    simp only [minusCoeff, ↓reduceIte]
    have hprod := mul_nonneg (sub_nonneg.mpr hi) (show 0 ≤ 1 + p i by linarith [hp i])
    have hsq := sq_nonneg (p i)
    constructor <;> nlinarith only [hprod, hsq]
  · simp only [minusCoeff, ite_eq_right hij, zero_sub]
    have hpp := mul_nonneg (hp i) (hp j)
    have hijle := probability_two_coord_le_one p hp hsum hij
    have hprod := mul_nonneg (hp i) (sub_nonneg.mpr hj)
    constructor <;> nlinarith only [hp j, hpp, hijle, hprod]

theorem plusCoeff_sum [DecidableEq ι] (p v : ι → ℝ) (i : ι) :
    ∑ j, plusCoeff p i j * v j =
      ((∑ j, p j * v j) + p i * (v i - ∑ j, p j * v j)) / 2 := by
  simp only [plusCoeff]
  have hdelta : ∑ j, (if i = j then (1 : ℝ) else 0) * v j = v i := by
    simp
  calc
    _ = ((∑ j, p j * v j) + p i *
        ((∑ j, (if i = j then (1 : ℝ) else 0) * v j) - ∑ j, p j * v j)) / 2 := by
      simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hdelta]

theorem minusCoeff_sum [DecidableEq ι] (p v : ι → ℝ) (i : ι) :
    ∑ j, minusCoeff p i j * v j =
      ((∑ j, p j * v j) - p i * (v i - ∑ j, p j * v j)) / 2 := by
  simp only [minusCoeff]
  have hdelta : ∑ j, (if i = j then (1 : ℝ) else 0) * v j = v i := by
    simp
  calc
    _ = ((∑ j, p j * v j) - p i *
        ((∑ j, (if i = j then (1 : ℝ) else 0) * v j) - ∑ j, p j * v j)) / 2 := by
      simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib,
        Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hdelta]

theorem coeff_direction_bounds (c v : ι → ℝ)
    (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1 / 2) (hv : ∀ j, 0 ≤ v j) :
    0 ≤ ∑ j, c j * v j ∧ (∑ j, c j * v j) ≤ (∑ j, v j) / 2 := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hc j).1 (hv j))
  · calc
      _ ≤ ∑ j, (1 / 2 : ℝ) * v j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hc j).2 (hv j))
      _ = _ := by rw [← Finset.mul_sum]; ring

end HiddenMonotonicity.SoftmaxDC
