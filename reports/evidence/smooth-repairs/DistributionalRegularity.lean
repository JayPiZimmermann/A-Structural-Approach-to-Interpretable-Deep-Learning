import HiddenMonotonicity.CurvatureMinimality
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Convex.Continuous

/-! One-dimensional weak second derivatives, defined by the actual compactly
supported smooth test-function identity. -/
namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ContDiff

/-- The distributional second derivative of `f` is the locally integrable
function `q`. No classical regularity of `f` or its derivative is assumed here. -/
def HasSecondDistributionalDerivative (f q : ℝ → ℝ) : Prop :=
  LocallyIntegrable f ∧ LocallyIntegrable q ∧
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, f x * deriv (deriv φ) x) = ∫ x, q x * φ x

private theorem reflected_second_derivative (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (a : ℝ) :
    deriv (deriv (fun x => φ (a-x))) = fun x => deriv (deriv φ) (a-x) := by
  have hd : deriv (fun x => φ (a-x)) = fun x => -deriv φ (a-x) := by
    funext x
    have h := ((hφ.differentiable (by simp)) (a-x)).hasDerivAt.comp x
      ((hasDerivAt_id x).const_sub a)
    simpa only [id_eq,mul_neg_one,Function.comp_def] using h.deriv
  rw [hd]
  funext x
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have h := (((hφ'.differentiable (by simp)) (a-x)).hasDerivAt.comp x
    ((hasDerivAt_id x).const_sub a)).fun_neg
  simpa only [id_eq,mul_neg_one,neg_neg,Function.comp_def,Pi.neg_apply] using h.deriv

/-- Convolution transfers the actual weak equation to a classical equation. -/
theorem weak_second_zero_convolution (f : ℝ → ℝ) (hf : LocallyIntegrable f)
    (hz : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x * deriv (deriv φ) x)=0)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∀ x, HasDerivAt (deriv (φ ⋆[lsmul ℝ ℝ] f)) 0 x := by
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hd : deriv (φ ⋆[lsmul ℝ ℝ] f)=deriv φ ⋆[lsmul ℝ ℝ] f := by
    funext x
    exact (hc.hasDerivAt_convolution_left (lsmul ℝ ℝ) (hφ.of_le (by simp)) hf x).deriv
  intro x
  rw [hd]
  have h := hc.deriv.hasDerivAt_convolution_left (lsmul ℝ ℝ) (hφ'.of_le (by simp)) hf x
  have hz' := hz (fun t => φ (x-t)) (hφ.comp (contDiff_const.sub contDiff_id))
    (hc.comp_homeomorph (Homeomorph.subLeft x))
  rw [reflected_second_derivative φ hφ x] at hz'
  have he : ((deriv (deriv φ)) ⋆[lsmul ℝ ℝ] f) x=0 := by
    rw [convolution_eq_swap]
    simpa only [lsmul_apply,smul_eq_mul,mul_comm] using hz'
  rwa [he] at h

/-- A continuous function with zero distributional second derivative is affine.
The proof smooths with actual shrinking normalized bumps and passes the exact
classical affine identities to the pointwise limit. -/
theorem affine_of_distributional_second_zero (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x * deriv (deriv φ) x)=0) :
    ∀ x, f x=f 0+(f 1-f 0)*x := by
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨(1/((n:ℝ)+1))/2,1/((n:ℝ)+1),by positivity,half_lt_self (by positivity)⟩
  let F : ℕ → ℝ → ℝ := fun n => (φ n).normed volume ⋆[lsmul ℝ ℝ] f
  have hF (n : ℕ) : ContDiff ℝ ∞ (F n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ n).contDiff_normed hf.locallyIntegrable
  have ha (n : ℕ) (x : ℝ) : F n x=F n 0+(F n 1-F n 0)*x := by
    have hzero := weak_second_zero_convolution f hf.locallyIntegrable hz
      ((φ n).normed volume) (φ n).contDiff_normed (φ n).hasCompactSupport_normed
    have hd : ∀ x, deriv (F n) x=deriv (F n) 0 :=
      fun x => is_const_of_deriv_eq_zero (fun y => (hzero y).differentiableAt)
        (fun y => (hzero y).deriv) x 0
    have hg (y : ℝ) : HasDerivAt (fun z => F n z-deriv (F n) 0*z) 0 y := by
      convert ((hF n).differentiable (by simp) y).hasDerivAt.sub
        ((hasDerivAt_id y).const_mul (deriv (F n) 0)) using 1
      · rfl
      · simp [hd]
    have hh (y : ℝ) := is_const_of_deriv_eq_zero (fun z => (hg z).differentiableAt)
      (fun z => (hg z).deriv) y 0
    have h1 := hh 1
    have hx := hh x
    simp only [mul_zero,sub_zero,mul_one] at h1 hx
    have hs : deriv (F n) 0=F n 1-F n 0 := by linarith
    rw [← hs]
    linarith
  have ht (x : ℝ) : Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      (φ:=φ) tendsto_one_div_add_atTop_nhds_zero_nat hf x
  intro x
  exact tendsto_nhds_unique (ht x)
    (((ht 0).add (((ht 1).sub (ht 0)).mul_const x)).congr (fun n => (ha n x).symm))



/-- Global integration by parts for a locally absolutely continuous function and
an actual smooth compactly supported test function. -/
theorem locally_AC_integral_mul_deriv (f g : ℝ → ℝ)
    (hf : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    (∫ x, f x * deriv g x) = -(∫ x, deriv f x * g x) := by
  obtain ⟨A,hA⟩ := hc.bddBelow
  obtain ⟨B,hB⟩ := hc.bddAbove
  let a := A-1
  let b := B+1
  have hs : tsupport g ⊆ Ioc a b := by
    intro x hx
    exact ⟨by have := hA hx; dsimp [a]; linarith,
      by have := hB hx; dsimp [b]; linarith⟩
  have hga : g a=0 := by
    by_contra hn
    have ht := hA (subset_tsupport g (Function.mem_support.mpr hn))
    dsimp [a] at ht
    linarith
  have hgb : g b=0 := by
    by_contra hn
    have ht := hB (subset_tsupport g (Function.mem_support.mpr hn))
    dsimp [b] at ht
    linarith
  have h1 : Function.support (fun x => f x*deriv g x) ⊆ Ioc a b := by
    intro x hx
    apply hs
    apply support_deriv_subset
    exact fun hn => hx (by simp [hn])
  have h2 : Function.support (fun x => deriv f x*g x) ⊆ Ioc a b := by
    intro x hx
    apply hs
    apply subset_tsupport g
    exact fun hn => hx (by simp [hn])
  rw [← intervalIntegral.integral_eq_integral_of_support_subset h1,
    ← intervalIntegral.integral_eq_integral_of_support_subset h2]
  simpa [hga,hgb] using (hf a b).integral_mul_deriv_eq_deriv_mul
    ((hg.of_le (by simp) : ContDiff ℝ 1 g).contDiffOn.absolutelyContinuousOnInterval)

noncomputable def localPrimitive (q : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, q t

private theorem locally_integrable_intervalIntegrable (q : ℝ → ℝ)
    (hq : LocallyIntegrable q) (a b : ℝ) : IntervalIntegrable q volume a b :=
  (hq.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

theorem localPrimitive_continuous (q : ℝ → ℝ) (hq : LocallyIntegrable q) :
    Continuous (localPrimitive q) :=
  intervalIntegral.continuous_primitive (locally_integrable_intervalIntegrable q hq) 0

theorem localPrimitive_locally_AC (q : ℝ → ℝ) (hq : LocallyIntegrable q) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (localPrimitive q) a b := by
  have hI := (locally_integrable_intervalIntegrable q hq a b).absolutelyContinuousOnInterval_intervalIntegral
    (c:=a) (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => localPrimitive q a) a b :=
    (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => localPrimitive q a) (uIcc a b)).absolutelyContinuousOnInterval
  apply (hconst.fun_add hI).congr
  intro x hx
  exact intervalIntegral.integral_add_adjacent_intervals
    (locally_integrable_intervalIntegrable q hq 0 a) (locally_integrable_intervalIntegrable q hq a x)

theorem localPrimitive_derivative_ae (q : ℝ → ℝ) (hq : LocallyIntegrable q) :
    ∀ᵐ x, HasDerivAt (localPrimitive q) (q x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hq] with x hx
  exact hx 0

theorem localPrimitive_hasDerivAt (q : ℝ → ℝ) (hq : Continuous q) (x : ℝ) :
    HasDerivAt (localPrimitive q) (q x) x :=
  intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable 0 x) (hq.stronglyMeasurableAtFilter volume (𝓝 x))
    hq.continuousAt

/-- Twice integrating a locally integrable density realizes its distributional
second derivative, by two genuine integrations by parts. -/
theorem localPrimitive_twice_distributional (q : ℝ → ℝ) (hq : LocallyIntegrable q) :
    HasSecondDistributionalDerivative (localPrimitive (localPrimitive q)) q := by
  have hG := localPrimitive_continuous q hq
  have hF := localPrimitive_continuous (localPrimitive q) hG.locallyIntegrable
  refine ⟨hF.locallyIntegrable,hq,?_⟩
  intro φ hφ hc
  have hdF : deriv (localPrimitive (localPrimitive q))=localPrimitive q :=
    funext (fun x => (localPrimitive_hasDerivAt _ hG x).deriv)
  have h1 := locally_AC_integral_mul_deriv (localPrimitive (localPrimitive q)) (deriv φ)
    (localPrimitive_locally_AC _ hG.locallyIntegrable)
    (contDiff_infty_iff_deriv.mp hφ).2 hc.deriv
  have h2 := locally_AC_integral_mul_deriv (localPrimitive q) φ
    (localPrimitive_locally_AC q hq) hφ hc
  rw [hdF,h2,neg_neg] at h1
  rw [h1]
  apply integral_congr_ae
  filter_upwards [localPrimitive_derivative_ae q hq] with x hx
  rw [hx.deriv]



/-- The one-dimensional distributional regularity bridge. A continuous function
whose actual weak second derivative is locally integrable has a locally absolutely
continuous classical derivative, and that second derivative equals the given
density almost everywhere. -/
theorem distributional_second_derivative_regular (f q : ℝ → ℝ)
    (hf : Continuous f) (hw : HasSecondDistributionalDerivative f q) :
    Differentiable ℝ f ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b) ∧
    (∀ᵐ x, curvature f x=q x) ∧
    ∃ a b : ℝ, ∀ x, f x=localPrimitive (localPrimitive q) x+a*x+b := by
  let F := localPrimitive (localPrimitive q)
  have hG := localPrimitive_continuous q hw.2.1
  have hF : Continuous F := localPrimitive_continuous _ hG.locallyIntegrable
  have hFw := localPrimitive_twice_distributional q hw.2.1
  have hz : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (f x-F x)*deriv (deriv φ) x)=0 := by
    intro φ hφ hc
    have hc' := hc.deriv.deriv
    have hφ' : Continuous (deriv (deriv φ)) :=
      (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hφ).2).2.continuous
    have hIf : Integrable (fun x => f x*deriv (deriv φ) x) :=
      hw.1.integrable_smul_right_of_hasCompactSupport hφ' hc'
    have hIF : Integrable (fun x => F x*deriv (deriv φ) x) :=
      hF.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ' hc'
    simp_rw [sub_mul]
    rw [integral_sub hIf hIF,hw.2.2 φ hφ hc,hFw.2.2 φ hφ hc,sub_self]
  have ha := affine_of_distributional_second_zero (fun x => f x-F x) (hf.sub hF) hz
  let a := (f 1-F 1)-(f 0-F 0)
  let b := f 0-F 0
  have he (x : ℝ) : f x=F x+a*x+b := by
    have := ha x
    dsimp [a,b]
    linarith
  have hd (x : ℝ) : HasDerivAt f (localPrimitive q x+a) x := by
    have ht := ((localPrimitive_hasDerivAt _ hG x).fun_add ((hasDerivAt_id x).const_mul a)).add_const b
    have heq : (fun y => F y+a*y+b)=f := funext (fun y => (he y).symm)
    change HasDerivAt (fun y => F y+a*y+b) (localPrimitive q x+a*1) x at ht
    simpa only [heq,mul_one] using ht
  have hd' : deriv f=fun x => localPrimitive q x+a := funext (fun x => (hd x).deriv)
  refine ⟨fun x => (hd x).differentiableAt,?_,?_,a,b,he⟩
  · intro l r
    rw [hd']
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => a) l r :=
      (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => a) (uIcc l r)).absolutelyContinuousOnInterval
    exact (localPrimitive_locally_AC q hw.2.1 l r).fun_add hc
  · filter_upwards [localPrimitive_derivative_ae q hw.2.1] with x hx
    change deriv (deriv f) x=q x
    rw [hd']
    exact (hx.add_const a).deriv



/-- The source proposition with its actual distributional regularity scope.
Differentiability and local AC of the convex components are conclusions derived
from their locally integrable weak curvature densities. -/
theorem curvature_minimality_distributional (f c1 c2 q1 q2 : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hfAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f))
    (hc1 : ConvexOn ℝ univ c1) (hc2 : ConvexOn ℝ univ c2)
    (hw1 : HasSecondDistributionalDerivative c1 q1)
    (hw2 : HasSecondDistributionalDerivative c2 q2)
    (heq : ∀ x, f x=c1 x-c2 x) :
    Differentiable ℝ c1 ∧ Differentiable ℝ c2 ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv c1) a b) ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv c2) a b) ∧
    (∀ᵐ x, curvature c1 x=q1 x ∧ curvature c2 x=q2 x) ∧
    (∀ᵐ x, positiveCurvature f x≤q1 x ∧ negativeCurvature f x≤q2 x) ∧
    ((∀ᵐ x, q1 x=positiveCurvature f x ∧ q2 x=negativeCurvature f x) →
      ∃ a b : ℝ, (∀ x, c1 x=C1 f x+a*x+b) ∧ (∀ x, c2 x=C2 f x+a*x+b)) ∧
    (∀ L, Monotone (tilt (C1 f) L) → Monotone (tilt (C2 f) L) → commonTilt f≤L) := by
  have hcont1 : Continuous c1 := continuousOn_univ.mp (hc1.continuousOn isOpen_univ)
  have hcont2 : Continuous c2 := continuousOn_univ.mp (hc2.continuousOn isOpen_univ)
  obtain ⟨hd1,hAC1,hq1,_⟩ := distributional_second_derivative_regular c1 q1 hcont1 hw1
  obtain ⟨hd2,hAC2,hq2,_⟩ := distributional_second_derivative_regular c2 q2 hcont2 hw2
  obtain ⟨hbound,hunique,htilt⟩ := curvature_minimality_locally_AC f c1 c2
    hf hfAC hq hc1 hc2 hd1 hd2 hAC1 heq
  refine ⟨hd1,hd2,hAC1,hAC2,hq1.and hq2,?_,?_,htilt⟩
  · filter_upwards [hbound,hq1,hq2] with x hx hx1 hx2
    simpa only [hx1,hx2] using hx
  · intro he
    apply hunique
    filter_upwards [he,hq1,hq2] with x hx hx1 hx2
    simpa only [hx1,hx2] using hx

end HiddenMonotonicity.SmoothDC
