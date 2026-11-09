import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace HiddenMonotonicity.SoftmaxDC

open Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A common affine tilt of a profile evaluated on the difference of two streams. -/
noncomputable def multivariateLift (P : (ι → ℝ) → ℝ) (L c : ℝ)
    (z : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  P (z.1 - z.2) + L * ∑ j, z.2 j - c

omit [Fintype ι] in
theorem convex_from_affine_lines (f : (ι → ℝ) → ℝ)
    (hline : ∀ a v : ι → ℝ,
      ConvexOn ℝ univ (fun t : ℝ => f (fun j => a j + t * v j))) :
    ConvexOn ℝ univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := (hline x (y - x)).2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb hab
  have hy' : (fun j => x j + (y - x) j) = y := by
    funext j
    simp
  have hc : (fun j => x j + b * (y - x) j) = a • x + b • y := by
    funext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith only [congrArg (fun t : ℝ => t * x j) hab]
  simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, one_mul, zero_mul, add_zero, hy', hc]
    using h

omit [Fintype ι] in
theorem monotone_from_affine_line_deriv (f : (ι → ℝ) → ℝ)
    (D : (ι → ℝ) → (ι → ℝ) → ℝ)
    (hderiv : ∀ (a v : ι → ℝ) (t : ℝ),
      HasDerivAt (fun s : ℝ => f (fun j => a j + s * v j))
        (D (fun j => a j + t * v j) v) t)
    (hnonneg : ∀ z v : ι → ℝ, (∀ j, 0 ≤ v j) → 0 ≤ D z v) :
    Monotone f := by
  intro a b hab
  have hm : Monotone (fun t : ℝ => f (fun j => a j + t * (b - a) j)) := by
    apply monotone_of_deriv_nonneg
    · exact fun t => (hderiv a (b - a) t).differentiableAt
    · intro t
      rw [(hderiv a (b - a) t).deriv]
      exact hnonneg _ _ (fun j => sub_nonneg.mpr (hab j))
  have h := hm (show (0 : ℝ) ≤ 1 by norm_num)
  have he : (fun j => a j + (b - a) j) = b := by
    funext j
    simp
  simpa only [zero_mul, add_zero, one_mul, he] using h

theorem multivariateLift_convex (P : (ι → ℝ) → ℝ) (L c : ℝ)
    (hP : ConvexOn ℝ univ P) :
    ConvexOn ℝ univ (multivariateLift P L c) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hP.2 (mem_univ (x.1 - x.2)) (mem_univ (y.1 - y.2)) ha hb hab
  have he : (a • x + b • y).1 - (a • x + b • y).2 =
      a • (x.1 - x.2) + b • (y.1 - y.2) := by
    funext j
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hs : (∑ j, (a • x + b • y).2 j) =
      a * (∑ j, x.2 j) + b * (∑ j, y.2 j) := by
    simp [Finset.mul_sum, Finset.sum_add_distrib]
  simp only [multivariateLift, he, hs, smul_eq_mul] at *
  nlinarith only [h, congrArg (fun t : ℝ => t * c) hab]

theorem multivariateLift_monotone (P : (ι → ℝ) → ℝ) (L c : ℝ)
    (hP : Monotone P)
    (hcomplement : Monotone (fun x : ι → ℝ => L * (∑ j, x j) - P x)) :
    Monotone (multivariateLift P L c) := by
  intro a b hab
  have hp := hP (show a.1 - a.2 ≤ b.1 - a.2 from
    fun j => sub_le_sub_right (hab.1 j) (a.2 j))
  have hc := hcomplement (show b.1 - b.2 ≤ b.1 - a.2 from
    fun j => sub_le_sub_left (hab.2 j) (b.1 j))
  simp only [Pi.sub_apply, Finset.sum_sub_distrib] at hc
  dsimp [multivariateLift]
  nlinarith only [hp, hc]

theorem multivariateLift_difference (P Q f : (ι → ℝ) → ℝ) (L c : ℝ)
    (hdiff : ∀ x, P x - Q x = f x) (z : (ι → ℝ) × (ι → ℝ)) :
    multivariateLift P L c z - multivariateLift Q L c z = f (z.1 - z.2) := by
  dsimp [multivariateLift]
  linarith only [hdiff (z.1 - z.2)]

theorem multivariateLift_nonnegative (P : (ι → ℝ) → ℝ) (L c : ℝ)
    (hmono : Monotone (multivariateLift P L c)) (hzero : c ≤ P 0)
    (z : (ι → ℝ) × (ι → ℝ)) (hz : 0 ≤ z) :
    0 ≤ multivariateLift P L c z := by
  have h := hmono hz
  have hz0 : 0 ≤ multivariateLift P L c 0 := by
    simpa [multivariateLift] using sub_nonneg.mpr hzero
  exact le_trans hz0 h

end HiddenMonotonicity.SoftmaxDC
