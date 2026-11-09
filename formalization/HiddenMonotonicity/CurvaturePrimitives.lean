import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

noncomputable def cumulative (q : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Iic x, q t
noncomputable def slope (q : ℝ → ℝ) (s x : ℝ) : ℝ := s+cumulative q x
noncomputable def primitive (q : ℝ → ℝ) (s c x : ℝ) : ℝ := c+∫ t in (0 : ℝ)..x, slope q s t

/-- An L1 curvature produces a continuous cumulative slope. -/
theorem cumulative_continuous (q : ℝ → ℝ) (hq : Integrable q) : Continuous (cumulative q) := by
  have he : cumulative q=fun x => cumulative q 0+∫ t in (0 : ℝ)..x,q t := by
    funext x
    have h := intervalIntegral.integral_Iic_sub_Iic (hq.integrableOn (s:=Iic 0))
      (hq.integrableOn (s:=Iic x))
    change cumulative q x-cumulative q 0=_ at h
    linarith
  rw [he]
  exact continuous_const.add (hq.continuous_primitive 0)

theorem slope_continuous (q : ℝ → ℝ) (hq : Integrable q) (s : ℝ) : Continuous (slope q s) :=
  continuous_const.add (cumulative_continuous q hq)

theorem primitive_hasDerivAt (q : ℝ → ℝ) (hq : Integrable q) (s c x : ℝ) :
    HasDerivAt (primitive q s c) (slope q s x) x := by
  exact ((slope_continuous q hq s).integral_hasStrictDerivAt 0 x).hasDerivAt.const_add c

theorem cumulative_monotone (q : ℝ → ℝ) (hq : Integrable q) (hp : ∀ x,0≤q x) :
    Monotone (cumulative q) := by
  intro x y hxy
  exact setIntegral_mono_set (hq.integrableOn (s:=Iic y))
    (Eventually.of_forall hp) (Eventually.of_forall (fun t ht => le_trans ht hxy))

theorem primitive_convex (q : ℝ → ℝ) (hq : Integrable q) (hp : ∀ x,0≤q x) (s c : ℝ) :
    ConvexOn ℝ univ (primitive q s c) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (primitive_hasDerivAt q hq s c x).differentiableAt)
  have hm := cumulative_monotone q hq hp
  intro x y hxy
  rw [(primitive_hasDerivAt q hq s c x).deriv,(primitive_hasDerivAt q hq s c y).deriv]
  exact add_le_add (le_refl s) (hm hxy)

/-- The antiderivative tends to zero at negative infinity. -/
theorem cumulative_atBot (q : ℝ → ℝ) : Tendsto (cumulative q) atBot (𝓝 0) :=
  tendsto_integral_Iic_zero tendsto_id

/-- Global integrable curvature and local absolute continuity recover the
entire derivative from its negative-infinity slope; no limit is assumed. -/
theorem derivative_cumulative_representation (f : ℝ → ℝ)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (deriv (deriv f))) (x : ℝ) :
    deriv f x = slope (deriv (deriv f))
      (deriv f 0-cumulative (deriv (deriv f)) 0) x := by
  have hf := (hAC 0 x).integral_deriv_eq_sub
  have hi := intervalIntegral.integral_Iic_sub_Iic
    (hq.integrableOn (s:=Iic 0)) (hq.integrableOn (s:=Iic x))
  change cumulative (deriv (deriv f)) x-cumulative (deriv (deriv f)) 0=_ at hi
  unfold slope
  linarith

theorem derivative_limit_atBot (f : ℝ → ℝ)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (deriv (deriv f))) :
    Tendsto (deriv f) atBot (𝓝 (deriv f 0-cumulative (deriv (deriv f)) 0)) := by
  have hlim : Tendsto (slope (deriv (deriv f)) (deriv f 0-cumulative (deriv (deriv f)) 0))
      atBot (𝓝 (deriv f 0-cumulative (deriv (deriv f)) 0)) := by
    change Tendsto (fun x => (deriv f 0-cumulative (deriv (deriv f)) 0)+cumulative (deriv (deriv f)) x)
      atBot (𝓝 (deriv f 0-cumulative (deriv (deriv f)) 0))
    simpa only [add_zero] using
      (tendsto_const_nhds (x:=(deriv f 0-cumulative (deriv (deriv f)) 0))).add
        (cumulative_atBot (deriv (deriv f)))
  exact hlim.congr' (Eventually.of_forall (fun x =>
    (derivative_cumulative_representation f hAC hq x).symm))

/-- A uniform finite L1 bound controls every cumulative slope. -/
theorem cumulative_abs_bound (q : ℝ → ℝ) (hq : Integrable q) (x : ℝ) :
    |cumulative q x|≤∫ t,|q t| := by
  have hnorm := norm_integral_le_integral_norm (μ:=volume.restrict (Iic x)) q
  have hsub := setIntegral_le_integral hq.norm (Eventually.of_forall (fun t => norm_nonneg (q t)))
    (s:=Iic x)
  simpa [cumulative,Real.norm_eq_abs] using le_trans hnorm hsub

theorem slope_abs_bound (q : ℝ → ℝ) (hq : Integrable q) (s x : ℝ) :
    |slope q s x|≤|s|+∫ t,|q t| := by
  exact le_trans (abs_add_le s (cumulative q x))
    (add_le_add (le_refl _) (cumulative_abs_bound q hq x))

end HiddenMonotonicity.SmoothDC
