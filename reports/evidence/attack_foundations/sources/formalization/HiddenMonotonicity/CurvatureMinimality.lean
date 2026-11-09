import HiddenMonotonicity.SmoothCurvatureSplit
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory

/-- Convex differentiable functions have a monotone derivative, including in
the absence of an everywhere classical second derivative. -/
theorem convex_derivative_monotone (c : ℝ → ℝ) (hc : ConvexOn ℝ univ c)
    (hd : Differentiable ℝ c) : Monotone (deriv c) := by
  intro x y hxy
  exact hc.monotoneOn_deriv (fun z _ => hd z) (mem_univ x) (mem_univ y) hxy

/-- Jordan minimality of the actual a.e. curvature. This conclusion holds for
all differentiable convex components, even before imposing local AC on their derivatives. -/
theorem curvature_minimality_ae (f c1 c2 : ℝ → ℝ)
    (hc1 : ConvexOn ℝ univ c1) (hc2 : ConvexOn ℝ univ c2)
    (hd1 : Differentiable ℝ c1) (hd2 : Differentiable ℝ c2)
    (heq : ∀ x,f x=c1 x-c2 x) :
    ∀ᵐ x, positiveCurvature f x≤curvature c1 x ∧ negativeCurvature f x≤curvature c2 x := by
  have hm1 := convex_derivative_monotone c1 hc1 hd1
  have hm2 := convex_derivative_monotone c2 hc2 hd2
  have hdEq : deriv f=fun x => deriv c1 x-deriv c2 x := by
    funext x
    have h := (hd1 x).hasDerivAt.fun_sub (hd2 x).hasDerivAt
    have he : (fun y => c1 y-c2 y)=f := funext (fun y => (heq y).symm)
    rw [he] at h
    exact h.deriv
  filter_upwards [hm1.ae_differentiableAt,hm2.ae_differentiableAt] with x hx1 hx2
  have h := hx1.hasDerivAt.fun_sub hx2.hasDerivAt
  rw [← hdEq] at h
  have hq : curvature f x=curvature c1 x-curvature c2 x := h.deriv
  have hp1 : 0≤curvature c1 x := hm1.deriv_nonneg
  have hp2 : 0≤curvature c2 x := hm2.deriv_nonneg
  constructor
  · exact max_le (by change curvature f x≤curvature c1 x;linarith) hp1
  · exact max_le (by change -curvature f x≤curvature c2 x;linarith) hp2

/-- Cumulative integrals of L1 functions have locally absolutely continuous slopes. -/
theorem slope_locally_AC (q : ℝ → ℝ) (hq : Integrable q) (s a b : ℝ) :
    AbsolutelyContinuousOnInterval (slope q s) a b := by
  have hi : IntervalIntegrable q volume a b := hq.intervalIntegrable
  have hI := hi.absolutelyContinuousOnInterval_intervalIntegral (c:=a) (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => s+cumulative q a) a b :=
    (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => s+cumulative q a) (uIcc a b)).absolutelyContinuousOnInterval
  apply (hconst.fun_add hI).congr
  intro x hx
  have hc := intervalIntegral.integral_Iic_sub_Iic
    (hq.integrableOn (s:=Iic a)) (hq.integrableOn (s:=Iic x))
  change cumulative q x-cumulative q a=_ at hc
  unfold slope
  linarith

/-- Actual second derivatives of the canonical primitives are P and N a.e. -/
theorem primitive_second_derivatives_ae (f : ℝ → ℝ) (hq : Integrable (curvature f)) :
    (∀ᵐ x,HasDerivAt (D1 f) (positiveCurvature f x) x) ∧
    (∀ᵐ x,HasDerivAt (D2 f) (negativeCurvature f x) x) := by
  have h (q : ℝ → ℝ) (hi : Integrable q) (s : ℝ) :
      ∀ᵐ x,HasDerivAt (slope q s) (q x) x := by
    have ha := LocallyIntegrable.ae_hasDerivAt_integral hi.locallyIntegrable
    filter_upwards [ha] with x hx
    have hd := (hx (0 : ℝ)).const_add (s+cumulative q 0)
    have he : (fun y => (s+cumulative q 0)+∫ t in (0 : ℝ)..y,q t)=slope q s := by
      funext y
      have hh := intervalIntegral.integral_Iic_sub_Iic
        (hi.integrableOn (s:=Iic 0)) (hi.integrableOn (s:=Iic y))
      change cumulative q y-cumulative q 0=_ at hh
      unfold slope
      linarith
    rw [he] at hd
    exact hd
  exact ⟨h _ (positiveCurvature_integrable f hq) _,h _ (negativeCurvature_integrable f hq) _⟩

/-- In the locally-AC derivative setting, zero a.e. second derivative forces
an affine function; singular Cantor curvature is excluded by the actual AC hypothesis. -/
theorem affine_of_ae_second_derivative_zero (c : ℝ → ℝ) (hc : Differentiable ℝ c)
    (hAC : ∀ a b,AbsolutelyContinuousOnInterval (deriv c) a b)
    (hzero : ∀ᵐ x, HasDerivAt (deriv c) 0 x) :
    ∀ x,c x=c 0+deriv c 0*x := by
  have hconst (x : ℝ) : deriv c x=deriv c 0 := by
    obtain ⟨v,hv⟩ := (hAC 0 x).const_of_ae_hasDerivAt_zero
      (hzero.mono (fun z hz _ => hz))
    exact (hv x (by simp)).trans (hv 0 (by simp)).symm
  have hd (x : ℝ) : HasDerivAt (fun y => c y-deriv c 0*y) 0 x := by
    have h := (hc x).hasDerivAt.fun_sub ((hasDerivAt_id x).const_mul (deriv c 0))
    convert h using 1
    · funext y
      simp only [id_eq]
    · rw [hconst]
      ring
  intro x
  have he := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).deriv) x 0
  simp only [mul_zero,sub_zero] at he
  linarith

end HiddenMonotonicity.SmoothDC
