import HiddenMonotonicity.ModernActivationBounds

/-! Global Swish/SiLU with arbitrary positive scale, including proved L1
curvature. The signed activation is not restricted to a routing-game domain. -/
namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

noncomputable def swish (β x : ℝ) := x*Real.sigmoid (β*x)
noncomputable def swishFirst (β x : ℝ) := Real.sigmoid (β*x)+β*x*sigmoidFirst (β*x)
noncomputable def swishSecond (β x : ℝ) :=
  β*sigmoidFirst (β*x)*(2+β*x*(1-2*Real.sigmoid (β*x)))

theorem swish_hasDerivAt (β x : ℝ) : HasDerivAt (swish β) (swishFirst β x) x := by
  have h := (hasDerivAt_id x).fun_mul
    ((Real.hasDerivAt_sigmoid (β*x)).comp x ((hasDerivAt_id x).const_mul β))
  convert h using 1
  · rfl
  · unfold swishFirst sigmoidFirst
    simp only [id_eq,Function.comp_def]
    ring

theorem swishFirst_hasDerivAt (β x : ℝ) :
    HasDerivAt (swishFirst β) (swishSecond β x) x := by
  have hs := (Real.hasDerivAt_sigmoid (β*x)).comp x ((hasDerivAt_id x).const_mul β)
  have hq := (sigmoidFirst_derivative (β*x)).comp x ((hasDerivAt_id x).const_mul β)
  have h := hs.fun_add (((hasDerivAt_id x).const_mul β).fun_mul hq)
  convert h using 1
  · rfl
  · unfold swishSecond sigmoidSecond sigmoidFirst
    simp only [id_eq,Function.comp_def]
    ring

theorem swish_curvature (β : ℝ) : curvature (swish β)=swishSecond β := by
  funext x
  unfold curvature
  rw [show deriv (swish β)=swishFirst β from funext fun y => (swish_hasDerivAt β y).deriv]
  exact (swishFirst_hasDerivAt β x).deriv

theorem swish_curvature_integrable (β : ℝ) (hβ : 0<β) : Integrable (curvature (swish β)) := by
  rw [swish_curvature]
  have h1 := (sigmoidFirst_integrable.comp_mul_left' (ne_of_gt hβ)).const_mul 2
  have h2 := weighted_sigmoidSecond_integrable.comp_mul_left' (ne_of_gt hβ)
  convert (h1.add h2).const_mul β using 1
  funext x
  simp only [swishSecond,sigmoidSecond,Pi.add_apply]
  ring

theorem swishSecond_continuous (β : ℝ) : Continuous (swishSecond β) := by
  unfold swishSecond sigmoidFirst
  fun_prop

theorem swish_derivative_locally_AC (β a b : ℝ) :
    AbsolutelyContinuousOnInterval (deriv (swish β)) a b := by
  rw [show deriv (swish β)=swishFirst β from funext fun y => (swish_hasDerivAt β y).deriv]
  exact locally_AC_of_continuous_derivative _ _ (swishFirst_hasDerivAt β) (swishSecond_continuous β) a b

theorem swishSecond_even (β x : ℝ) : swishSecond β (-x)=swishSecond β x := by
  unfold swishSecond
  rw [mul_neg,sigmoidFirst_even,Real.sigmoid_neg]
  ring

theorem swish_curvature_zero (β : ℝ) : curvature (swish β) 0=β/2 := by
  rw [swish_curvature]
  norm_num [swishSecond,sigmoidFirst,Real.sigmoid_zero]
  ring

/-- The curvature is strictly positive throughout a neighborhood of zero and
strictly negative in both sufficiently distant tails. -/
theorem swish_curvature_sign_regions (β : ℝ) (hβ : 0<β) :
    ∃ ε R : ℝ, 0<ε ∧ 0<R ∧
      (∀ x, |x|<ε → 0<curvature (swish β) x) ∧
      (∀ x, R< |x| → curvature (swish β) x<0) := by
  have hp : 0<swishSecond β 0 := by
    rw [← swish_curvature,swish_curvature_zero]
    exact div_pos hβ (by norm_num)
  have hevent : ∀ᶠ x in 𝓝 (0 : ℝ), 0<swishSecond β x :=
    continuous_const.continuousAt.eventually_lt (swishSecond_continuous β).continuousAt hp
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  have hsig : ∀ᶠ y in atTop, (3/4 : ℝ)<Real.sigmoid y :=
    (tendsto_order.mp Real.tendsto_sigmoid_atTop).1 _ (by norm_num)
  obtain ⟨r,hr⟩ := Filter.eventually_atTop.mp hsig
  let R := max r 4/β
  have hR : 0<R := div_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ)<4) (le_max_right _ _)) hβ
  have htail (x : ℝ) (hx : R<x) : swishSecond β x<0 := by
    have hy : max r 4<β*x := by
      have h := (div_lt_iff₀ hβ).mp hx
      simpa only [mul_comm] using h
    have hy4 : 4<β*x := (le_max_right _ _).trans_lt hy
    have hys : (3/4 : ℝ)<Real.sigmoid (β*x) := hr _ ((le_max_left _ _).trans hy.le)
    have hfac : 2+β*x*(1-2*Real.sigmoid (β*x))<0 := by
      nlinarith [mul_pos (show 0<β*x by linarith) (sub_pos.mpr hys)]
    have hfirst : 0<sigmoidFirst (β*x) :=
      mul_pos (Real.sigmoid_pos _) (sub_pos.mpr (Real.sigmoid_lt_one _))
    exact mul_neg_of_pos_of_neg (mul_pos hβ hfirst) hfac
  refine ⟨ε,R,hε,hR,?_,?_⟩
  · intro x hx
    rw [swish_curvature]
    exact hball (by simpa only [Real.dist_eq,sub_zero] using hx)
  · intro x hx
    rw [swish_curvature]
    rcases le_total 0 x with hx0 | hx0
    · exact htail x (by simpa only [abs_of_nonneg hx0] using hx)
    · rw [← swishSecond_even β x]
      exact htail (-x) (by simpa only [abs_of_nonpos hx0] using hx)

/-- Complete global Swish specialization for every positive scale. -/
theorem swish_smooth_dc_split (β : ℝ) (hβ : 0<β) :
    Integrable (curvature (swish β)) ∧
    (∀ a b, AbsolutelyContinuousOnInterval (deriv (swish β)) a b) ∧
    ConvexOn ℝ univ (tilt (C1 (swish β)) (commonTilt (swish β))) ∧
    ConvexOn ℝ univ (tilt (C2 (swish β)) (commonTilt (swish β))) ∧
    Monotone (tilt (C1 (swish β)) (commonTilt (swish β))) ∧
    Monotone (tilt (C2 (swish β)) (commonTilt (swish β))) ∧
    ValidPairActivation (swish β) (splitPair (swish β)) ∧
    NonnegativePairActivation (splitPair (swish β)) := by
  have hd : Differentiable ℝ (swish β) := fun x => (swish_hasDerivAt β x).differentiableAt
  have hs := smooth_dc_split (swish β) hd (swish_derivative_locally_AC β) (swish_curvature_integrable β hβ)
  exact ⟨swish_curvature_integrable β hβ,swish_derivative_locally_AC β,hs.2.2.1,hs.2.2.2.1,
    hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    smooth_pair_valid _ hd (swish_derivative_locally_AC β) (swish_curvature_integrable β hβ),
    smooth_pair_nonnegative _ hd (swish_derivative_locally_AC β) (swish_curvature_integrable β hβ)
      (by simp [swish])⟩

end HiddenMonotonicity.SmoothDC
