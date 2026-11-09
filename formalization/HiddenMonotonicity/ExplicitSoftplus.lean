import HiddenMonotonicity.ModernSoftplus

/-! Explicit convex and coordinatewise-monotone two-stream Softplus lift.
The negative stream is the identity, exactly as for the ReLU max/identity lift.
Temperature is strictly positive in the analytic statements. -/

namespace HiddenMonotonicity.SmoothDC
open Set

noncomputable def explicitSoftplusFirst (θ : ℝ) (z : ℝ × ℝ) : ℝ :=
  Thesis.Regularization.softplus θ (z.1-z.2)+z.2

noncomputable def explicitSoftplusPair (θ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (explicitSoftplusFirst θ z,z.2)

theorem explicitSoftplusFirst_derivative_first (θ a b : ℝ) (hθ : 0<θ) :
    HasDerivAt (fun t => explicitSoftplusFirst θ (t,b))
      (Thesis.Regularization.gate θ (a-b)) a := by
  convert ((Thesis.Regularization.hasDerivAt_softplus θ (a-b) hθ).comp a
    ((hasDerivAt_id a).sub_const b)).add_const b using 1 <;>
    simp [explicitSoftplusFirst]

theorem explicitSoftplusFirst_derivative_second (θ a b : ℝ) (hθ : 0<θ) :
    HasDerivAt (fun t => explicitSoftplusFirst θ (a,t))
      (1-Thesis.Regularization.gate θ (a-b)) b := by
  convert ((Thesis.Regularization.hasDerivAt_softplus θ (a-b) hθ).comp b
    ((hasDerivAt_id b).const_sub a)).fun_add (hasDerivAt_id b) using 1
  · simp [explicitSoftplusFirst]
  · ring

theorem explicitSoftplusFirst_convex (θ : ℝ) (hθ : 0<θ) :
    ConvexOn ℝ univ (explicitSoftplusFirst θ) := by
  have hC := (softplus_degenerate_split θ hθ).2.2.2.1
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    have hc := hC.2 (mem_univ (x.1-x.2)) (mem_univ (y.1-y.2)) ha hb hab
    change Thesis.Regularization.softplus θ (a*(x.1-x.2)+b*(y.1-y.2)) ≤
      a*Thesis.Regularization.softplus θ (x.1-x.2)+
      b*Thesis.Regularization.softplus θ (y.1-y.2) at hc
    simp only [explicitSoftplusFirst,Prod.fst_add,Prod.snd_add,smul_eq_mul]
    change Thesis.Regularization.softplus θ (a*x.1+b*y.1-(a*x.2+b*y.2))+
      (a*x.2+b*y.2) ≤ _
    rw [show a*x.1+b*y.1-(a*x.2+b*y.2)=a*(x.1-x.2)+b*(y.1-y.2) by ring]
    linarith

theorem explicitSoftplusFirst_monotone (θ : ℝ) (hθ : 0<θ) :
    Monotone (explicitSoftplusFirst θ) := by
  have hma (b : ℝ) : Monotone (fun a => explicitSoftplusFirst θ (a,b)) := by
    apply monotone_of_deriv_nonneg
    · exact fun a => (explicitSoftplusFirst_derivative_first θ a b hθ).differentiableAt
    · intro a
      rw [(explicitSoftplusFirst_derivative_first θ a b hθ).deriv]
      exact (Thesis.Regularization.gate_pos θ (a-b)).le
  have hmb (a : ℝ) : Monotone (fun b => explicitSoftplusFirst θ (a,b)) := by
    apply monotone_of_deriv_nonneg
    · exact fun b => (explicitSoftplusFirst_derivative_second θ a b hθ).differentiableAt
    · intro b
      rw [(explicitSoftplusFirst_derivative_second θ a b hθ).deriv]
      exact sub_nonneg.mpr (Thesis.Regularization.gate_lt_one θ (a-b)).le
  intro x y hxy
  exact le_trans (hma x.2 hxy.1) (hmb y.1 hxy.2)

theorem explicitSoftplusPair_valid (θ : ℝ) :
    ValidPairActivation (Thesis.Regularization.softplus θ) (explicitSoftplusPair θ) := by
  intro a b
  simp [explicitSoftplusPair,explicitSoftplusFirst]

/-- The first stream is the familiar two-input log-sum-exp soft maximum. -/
theorem explicitSoftplusFirst_logsumexp (θ : ℝ) (hθ : 0<θ) (x y : ℝ) :
    explicitSoftplusFirst θ (x,y)=
      θ*Real.log (Real.exp (x/θ)+Real.exp (y/θ)) := by
  have hproduct : (1+Real.exp ((x-y)/θ))*Real.exp (y/θ)=
      Real.exp (x/θ)+Real.exp (y/θ) := by
    rw [add_mul,one_mul,← Real.exp_add]
    rw [show (x-y)/θ+y/θ=x/θ by ring]
    ring
  rw [← hproduct,Real.log_mul (by positivity : (1+Real.exp ((x-y)/θ))≠0)
    (Real.exp_ne_zero _),Real.log_exp]
  unfold explicitSoftplusFirst Thesis.Regularization.softplus
  dsimp only
  field_simp

theorem explicitSoftplusPair_nonnegative (θ : ℝ) (hθ : 0<θ) :
    NonnegativePairActivation (explicitSoftplusPair θ) := by
  intro a b ha hb
  have hm := explicitSoftplusFirst_monotone θ hθ
    (show ((0,0) : ℝ × ℝ)≤(a,b) from ⟨ha,hb⟩)
  have h0 : 0≤explicitSoftplusFirst θ (0,0) := by
    simpa [explicitSoftplusFirst] using softplus_zero_nonnegative θ hθ
  exact ⟨h0.trans hm,hb⟩

/-- Both actual branches of the explicit pair are convex and monotone, and
their difference is Softplus of the difference on the whole real plane. -/
theorem explicitSoftplusPair_properties (θ : ℝ) (hθ : 0<θ) :
    ConvexOn ℝ univ (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).1) ∧
    ConvexOn ℝ univ (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).2) ∧
    Monotone (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).1) ∧
    Monotone (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).2) ∧
    ValidPairActivation (Thesis.Regularization.softplus θ) (explicitSoftplusPair θ) ∧
    NonnegativePairActivation (explicitSoftplusPair θ) := by
  refine ⟨explicitSoftplusFirst_convex θ hθ,?_,explicitSoftplusFirst_monotone θ hθ,
    fun _ _ h => h.2,explicitSoftplusPair_valid θ,explicitSoftplusPair_nonnegative θ hθ⟩
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    simp [explicitSoftplusPair,smul_eq_mul]

/-- The explicit Softplus split supplies every local hypothesis needed by the
two-stream network construction. -/
theorem softplus_explicit_split (θ : ℝ) (hθ : 0<θ) :
    ConvexOn ℝ univ (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).1) ∧
    ConvexOn ℝ univ (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).2) ∧
    Monotone (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).1) ∧
    Monotone (fun z : ℝ × ℝ => (explicitSoftplusPair θ z).2) ∧
    ValidPairActivation (Thesis.Regularization.softplus θ) (explicitSoftplusPair θ) ∧
    NonnegativePairActivation (explicitSoftplusPair θ) :=
  explicitSoftplusPair_properties θ hθ

end HiddenMonotonicity.SmoothDC
