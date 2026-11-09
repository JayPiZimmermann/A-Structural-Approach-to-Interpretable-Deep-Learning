import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import HiddenMonotonicity.Core

namespace HiddenMonotonicity.SmoothDC
open Set

/-- The asymmetric lift makes a convex profile coordinatewise monotone when
its increasing secant slopes lie between zero and the common width `L`. -/
noncomputable def asymmetricLift (C : ℝ → ℝ) (L : ℝ) (z : ℝ × ℝ) : ℝ :=
  C (z.1 - z.2) + L * z.2

theorem asymmetricLift_convex (C : ℝ → ℝ) (L : ℝ)
    (hC : ConvexOn ℝ univ C) : ConvexOn ℝ univ (asymmetricLift C L) := by
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    have hc := hC.2 (mem_univ (x.1 - x.2)) (mem_univ (y.1 - y.2)) ha hb hab
    change C (a * (x.1 - x.2) + b * (y.1 - y.2)) ≤
      a * C (x.1 - x.2) + b * C (y.1 - y.2) at hc
    change C ((a • x + b • y).1 - (a • x + b • y).2) +
      L * (a • x + b • y).2 ≤ _
    simp only [Prod.fst_add, Prod.snd_add, smul_eq_mul]
    change C (a * x.1 + b * y.1 - (a * x.2 + b * y.2)) +
      L * (a * x.2 + b * y.2) ≤ _
    have he : a * x.1 + b * y.1 - (a * x.2 + b * y.2) =
        a * (x.1 - x.2) + b * (y.1 - y.2) := by ring
    rw [he]
    simp only [asymmetricLift]
    linarith

theorem asymmetricLift_convex_iff (C : ℝ → ℝ) (L : ℝ) :
    ConvexOn ℝ univ (asymmetricLift C L) ↔ ConvexOn ℝ univ C := by
  constructor
  · intro h
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hc := h.2 (mem_univ ((x, 0) : ℝ × ℝ)) (mem_univ ((y, 0) : ℝ × ℝ))
      ha hb hab
    simpa [asymmetricLift, smul_eq_mul] using hc
  · exact asymmetricLift_convex C L

/-- A derivative-free criterion, including nonsmooth convex profiles. -/
theorem asymmetricLift_monotone_iff_increments (C : ℝ → ℝ) (L : ℝ) :
    Monotone (asymmetricLift C L) ↔
      ∀ a b : ℝ, a ≤ b → 0 ≤ C b - C a ∧ C b - C a ≤ L * (b - a) := by
  constructor
  · intro h a b hab
    have hp := h (show ((a, 0) : ℝ × ℝ) ≤ (b, 0) from ⟨hab, le_rfl⟩)
    have hn := h (show ((b, 0) : ℝ × ℝ) ≤ (b, b - a) from
      ⟨le_rfl, sub_nonneg.mpr hab⟩)
    have he : b - (b - a) = a := by ring
    simp only [asymmetricLift, sub_zero, mul_zero, add_zero] at hp
    simp only [asymmetricLift, sub_zero, mul_zero, add_zero, he] at hn
    exact ⟨sub_nonneg.mpr hp, by linarith⟩
  · intro h x y hxy
    have hp := (h (x.1 - x.2) (y.1 - x.2) (sub_le_sub_right hxy.1 x.2)).1
    have hn := (h (y.1 - y.2) (y.1 - x.2) (sub_le_sub_left hxy.2 y.1)).2
    dsimp [asymmetricLift]
    nlinarith only [hp, hn]

theorem asymmetricLift_derivative_first (C D : ℝ → ℝ)
    (hC : ∀ x, HasDerivAt C (D x) x) (L a b : ℝ) :
    HasDerivAt (fun t => asymmetricLift C L (t, b)) (D (a - b)) a := by
  simpa [asymmetricLift, Function.comp_def, id_eq] using
    (((hC (a - b)).comp a ((hasDerivAt_id a).sub_const b)).add_const (L * b))

theorem asymmetricLift_derivative_second (C D : ℝ → ℝ)
    (hC : ∀ x, HasDerivAt C (D x) x) (L a b : ℝ) :
    HasDerivAt (fun t => asymmetricLift C L (a, t)) (L - D (a - b)) b := by
  have h := ((hC (a - b)).comp b ((hasDerivAt_id b).const_sub a)).fun_add
    ((hasDerivAt_id b).const_mul L)
  convert h using 1
  · funext t
    simp [asymmetricLift, id_eq]
  · ring

theorem asymmetricLift_monotone (C D : ℝ → ℝ)
    (hC : ∀ x, HasDerivAt C (D x) x) (L : ℝ)
    (hD : ∀ x, 0 ≤ D x ∧ D x ≤ L) : Monotone (asymmetricLift C L) := by
  have hx (b : ℝ) : Monotone (fun a => asymmetricLift C L (a, b)) := by
    apply monotone_of_deriv_nonneg
    · exact fun a => (asymmetricLift_derivative_first C D hC L a b).differentiableAt
    · intro a
      rw [(asymmetricLift_derivative_first C D hC L a b).deriv]
      exact (hD (a - b)).1
  have hy (a : ℝ) : Monotone (fun b => asymmetricLift C L (a, b)) := by
    apply monotone_of_deriv_nonneg
    · exact fun b => (asymmetricLift_derivative_second C D hC L a b).differentiableAt
    · intro b
      rw [(asymmetricLift_derivative_second C D hC L a b).deriv]
      exact sub_nonneg.mpr (hD (a - b)).2
  intro x y hxy
  exact le_trans (hx x.2 hxy.1) (hy y.1 hxy.2)

theorem asymmetricLift_monotone_iff (C D : ℝ → ℝ)
    (hC : ∀ x, HasDerivAt C (D x) x) (L : ℝ) :
    Monotone (asymmetricLift C L) ↔ ∀ x, 0 ≤ D x ∧ D x ≤ L := by
  constructor
  · intro h x
    have hp : Monotone (fun a => asymmetricLift C L (a, 0)) :=
      fun a b hab => h ⟨hab, le_rfl⟩
    have hn : Monotone (fun b => asymmetricLift C L (x, b)) :=
      fun a b hab => h ⟨le_rfl, hab⟩
    have hdp := hp.deriv_nonneg (x := x)
    have hdn := hn.deriv_nonneg (x := (0 : ℝ))
    rw [(asymmetricLift_derivative_first C D hC L x 0).deriv] at hdp
    rw [(asymmetricLift_derivative_second C D hC L x 0).deriv] at hdn
    simp only [sub_zero] at hdp hdn
    exact ⟨hdp, by linarith⟩
  · exact asymmetricLift_monotone C D hC L

theorem asymmetricLift_difference (P Q f : ℝ → ℝ) (L : ℝ)
    (h : ∀ t, P t - Q t = f t) (z : ℝ × ℝ) :
    asymmetricLift P L z - asymmetricLift Q L z = f (z.1 - z.2) := by
  dsimp [asymmetricLift]
  linarith [h (z.1 - z.2)]

/-- The complete profile criterion applies to smooth and nonsmooth activations. -/
theorem asymmetric_split (P Q f : ℝ → ℝ) (L : ℝ)
    (hP : ConvexOn ℝ univ P) (hQ : ConvexOn ℝ univ Q)
    (hPd : ∀ a b : ℝ, a ≤ b → 0 ≤ P b - P a ∧ P b - P a ≤ L * (b - a))
    (hQd : ∀ a b : ℝ, a ≤ b → 0 ≤ Q b - Q a ∧ Q b - Q a ≤ L * (b - a))
    (hdiff : ∀ t, P t - Q t = f t) :
    ConvexOn ℝ univ (asymmetricLift P L) ∧
    ConvexOn ℝ univ (asymmetricLift Q L) ∧
    Monotone (asymmetricLift P L) ∧
    Monotone (asymmetricLift Q L) ∧
    ∀ z : ℝ × ℝ, asymmetricLift P L z - asymmetricLift Q L z = f (z.1 - z.2) :=
  ⟨asymmetricLift_convex P L hP, asymmetricLift_convex Q L hQ,
    (asymmetricLift_monotone_iff_increments P L).2 hPd,
    (asymmetricLift_monotone_iff_increments Q L).2 hQd,
    asymmetricLift_difference P Q f L hdiff⟩

theorem asymmetricLift_common_shift (C : ℝ → ℝ) (L x y c : ℝ) :
    asymmetricLift C L (x + c, y + c) = asymmetricLift C L (x, y) + L * c := by
  have he : x + c - (y + c) = x - y := by ring
  simp only [asymmetricLift, he]
  ring

/-- The exact max/identity ReLU pair is a special case of the same lift. -/
theorem asymmetricLift_relu (z : ℝ × ℝ) :
    asymmetricLift relu 1 z = max z.1 z.2 ∧
      asymmetricLift (fun _ => 0) 1 z = z.2 := by
  constructor
  · have h := max_sub z.1 z.2
    dsimp [asymmetricLift]
    linarith
  · simp [asymmetricLift]

theorem relu_profile_convex : ConvexOn ℝ univ relu := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  change max (a * x + b * y) 0 ≤ a * max x 0 + b * max y 0
  apply max_le
  · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left x 0) ha)
      (mul_le_mul_of_nonneg_left (le_max_left y 0) hb)
  · exact add_nonneg (mul_nonneg ha (le_max_right x 0))
      (mul_nonneg hb (le_max_right y 0))

theorem relu_profile_increments (a b : ℝ) (hab : a ≤ b) :
    0 ≤ relu b - relu a ∧ relu b - relu a ≤ b - a := by
  have hm : max a 0 ≤ max b 0 := max_le_max hab le_rfl
  have hu : max b 0 ≤ max a 0 + (b - a) := by
    apply max_le
    · linarith [le_max_left a 0]
    · linarith [le_max_right a 0]
  exact ⟨sub_nonneg.mpr hm, by change max b 0 - max a 0 ≤ b - a; linarith⟩

/-- This proves the nonsmooth ReLU split by the generic lift conditions. -/
theorem relu_asymmetric_split :
    ConvexOn ℝ univ (asymmetricLift relu 1) ∧
    ConvexOn ℝ univ (asymmetricLift (fun _ => 0) 1) ∧
    Monotone (asymmetricLift relu 1) ∧
    Monotone (asymmetricLift (fun _ => 0) 1) ∧
    ∀ z : ℝ × ℝ, asymmetricLift relu 1 z -
      asymmetricLift (fun _ => 0) 1 z = relu (z.1 - z.2) := by
  refine ⟨asymmetricLift_convex _ _ relu_profile_convex,
    asymmetricLift_convex _ _ (convexOn_const 0 convex_univ), ?_, ?_, ?_⟩
  · apply (asymmetricLift_monotone_iff_increments relu 1).2
    intro a b hab
    simpa using relu_profile_increments a b hab
  · apply (asymmetricLift_monotone_iff_increments (fun _ => 0) 1).2
    intro a b hab
    simp only [sub_self, one_mul, le_refl, true_and]
    exact sub_nonneg.mpr hab
  · exact asymmetricLift_difference relu (fun _ => 0) relu 1 (fun _ => sub_zero _)

end HiddenMonotonicity.SmoothDC
