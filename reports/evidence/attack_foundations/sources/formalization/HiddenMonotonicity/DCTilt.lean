import HiddenMonotonicity.CurvaturePrimitives

namespace HiddenMonotonicity.SmoothDC
open Set

noncomputable def tilt (C : ℝ → ℝ) (M : ℝ) (z : ℝ × ℝ) : ℝ :=
  C (z.1-z.2)+M*(z.1+z.2)

theorem tilt_derivative_first (C D : ℝ → ℝ) (hC : ∀ x, HasDerivAt C (D x) x)
    (M a b : ℝ) : HasDerivAt (fun t => tilt C M (t,b)) (D (a-b)+M) a := by
  have h := ((hC (a-b)).comp a ((hasDerivAt_id a).sub_const b)).fun_add
    (((hasDerivAt_id a).add_const b).const_mul M)
  convert h using 1
  · funext t
    simp only [tilt,Function.comp_def,id_eq] <;> ring
  · ring

theorem tilt_derivative_second (C D : ℝ → ℝ) (hC : ∀ x, HasDerivAt C (D x) x)
    (M a b : ℝ) : HasDerivAt (fun t => tilt C M (a,t)) (-D (a-b)+M) b := by
  have h := ((hC (a-b)).comp b ((hasDerivAt_id b).const_sub a)).fun_add
    (((hasDerivAt_id b).const_add a).const_mul M)
  convert h using 1
  · funext t
    simp only [tilt,Function.comp_def,id_eq] <;> ring
  · ring

/-- Affine precomposition and an affine tilt preserve convexity. -/
theorem tilt_convex (C : ℝ → ℝ) (hC : ConvexOn ℝ univ C) (M : ℝ) :
    ConvexOn ℝ univ (tilt C M) := by
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    have hc := hC.2 (mem_univ (x.1-x.2)) (mem_univ (y.1-y.2)) ha hb hab
    change C (a*(x.1-x.2)+b*(y.1-y.2))≤a*C (x.1-x.2)+b*C (y.1-y.2) at hc
    change C ((a • x+b • y).1-(a • x+b • y).2)+M*((a • x+b • y).1+(a • x+b • y).2)≤_
    simp only [Prod.fst_add,Prod.snd_add,Prod.fst_smul,Prod.snd_smul,smul_eq_mul]
    change C (a*x.1+b*y.1-(a*x.2+b*y.2))+M*(a*x.1+b*y.1+(a*x.2+b*y.2))≤_
    have he : a*x.1+b*y.1-(a*x.2+b*y.2)=a*(x.1-x.2)+b*(y.1-y.2) := by ring
    rw [he]
    simp only [tilt,smul_eq_mul]
    linarith

/-- A derivative bound makes both coordinate derivatives nonnegative. -/
theorem tilt_monotone (C D : ℝ → ℝ) (hC : ∀ x, HasDerivAt C (D x) x)
    (M : ℝ) (hM : ∀ x, |D x|≤M) : Monotone (tilt C M) := by
  have hma (b : ℝ) : Monotone (fun a => tilt C M (a,b)) := by
    apply monotone_of_deriv_nonneg
    · exact fun a => (tilt_derivative_first C D hC M a b).differentiableAt
    · intro a
      rw [(tilt_derivative_first C D hC M a b).deriv]
      have h := (abs_le.mp (hM (a-b))).1
      linarith
  have hmb (a : ℝ) : Monotone (fun b => tilt C M (a,b)) := by
    apply monotone_of_deriv_nonneg
    · exact fun b => (tilt_derivative_second C D hC M a b).differentiableAt
    · intro b
      rw [(tilt_derivative_second C D hC M a b).deriv]
      have h := (abs_le.mp (hM (a-b))).2
      linarith
  intro x y hxy
  exact le_trans (hma x.2 hxy.1) (hmb y.1 hxy.2)

/-- Conversely, a monotone tilted pair must dominate the full absolute slope. -/
theorem tilt_monotone_iff (C D : ℝ → ℝ) (hC : ∀ x, HasDerivAt C (D x) x) (M : ℝ) :
    Monotone (tilt C M) ↔ ∀ x,|D x|≤M := by
  constructor
  · intro hm x
    have hma : Monotone (fun a => tilt C M (a,0)) := by
      intro a b hab
      exact hm ⟨hab,le_rfl⟩
    have hmb : Monotone (fun b => tilt C M (x,b)) := by
      intro a b hab
      exact hm ⟨le_rfl,hab⟩
    have ha := hma.deriv_nonneg (x:=x)
    have hb := hmb.deriv_nonneg (x:=(0 : ℝ))
    rw [(tilt_derivative_first C D hC M x 0).deriv] at ha
    rw [(tilt_derivative_second C D hC M x 0).deriv] at hb
    simp only [sub_zero] at ha hb
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · exact tilt_monotone C D hC M

/-- The canonical positive/negative curvature pair has the smallest common tilt.
This is precisely the tilt-minimality part of prop:curvature_minimality. -/
theorem minimum_common_tilt (C1 C2 D1 D2 : ℝ → ℝ)
    (h1 : ∀ x,HasDerivAt C1 (D1 x) x) (h2 : ∀ x,HasDerivAt C2 (D2 x) x)
    (b1 : BddAbove (Set.range (fun x => |D1 x|)))
    (b2 : BddAbove (Set.range (fun x => |D2 x|))) :
    let M := max (sSup (Set.range (fun x => |D1 x|))) (sSup (Set.range (fun x => |D2 x|)))
    Monotone (tilt C1 M) ∧ Monotone (tilt C2 M) ∧
      ∀ L, Monotone (tilt C1 L) → Monotone (tilt C2 L) → M≤L := by
  dsimp
  refine ⟨tilt_monotone C1 D1 h1 _ (fun x => ?_),tilt_monotone C2 D2 h2 _ (fun x => ?_),?_⟩
  · exact le_trans (le_csSup b1 (mem_range_self x)) (le_max_left _ _)
  · exact le_trans (le_csSup b2 (mem_range_self x)) (le_max_right _ _)
  · intro L hm1 hm2
    have hd1 := (tilt_monotone_iff C1 D1 h1 L).mp hm1
    have hd2 := (tilt_monotone_iff C2 D2 h2 L).mp hm2
    apply max_le
    · exact csSup_le (range_nonempty _) (fun y ⟨x,hx⟩ => hx ▸ hd1 x)
    · exact csSup_le (range_nonempty _) (fun y ⟨x,hx⟩ => hx ▸ hd2 x)

end HiddenMonotonicity.SmoothDC
