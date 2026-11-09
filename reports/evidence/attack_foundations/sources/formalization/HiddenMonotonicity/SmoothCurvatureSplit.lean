import HiddenMonotonicity.DCTilt

namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

noncomputable def curvature (f : ℝ → ℝ) := deriv (deriv f)
noncomputable def positiveCurvature (f : ℝ → ℝ) (x : ℝ) := max (curvature f x) 0
noncomputable def negativeCurvature (f : ℝ → ℝ) (x : ℝ) := max (-curvature f x) 0
noncomputable def minusInfinitySlope (f : ℝ → ℝ) := deriv f 0-cumulative (curvature f) 0
noncomputable def C1 (f : ℝ → ℝ) := primitive (positiveCurvature f) (minusInfinitySlope f) (f 0)
noncomputable def C2 (f : ℝ → ℝ) := primitive (negativeCurvature f) 0 0
noncomputable def D1 (f : ℝ → ℝ) := slope (positiveCurvature f) (minusInfinitySlope f)
noncomputable def D2 (f : ℝ → ℝ) := slope (negativeCurvature f) 0
noncomputable def commonTilt (f : ℝ → ℝ) :=
  max (sSup (range (fun x => |D1 f x|))) (sSup (range (fun x => |D2 f x|)))

theorem positiveCurvature_integrable (f : ℝ → ℝ) (hq : Integrable (curvature f)) :
    Integrable (positiveCurvature f) := hq.pos_part

theorem negativeCurvature_integrable (f : ℝ → ℝ) (hq : Integrable (curvature f)) :
    Integrable (negativeCurvature f) := hq.neg_part

theorem cumulative_curvature_split (f : ℝ → ℝ) (hq : Integrable (curvature f)) (x : ℝ) :
    cumulative (positiveCurvature f) x-cumulative (negativeCurvature f) x=cumulative (curvature f) x := by
  unfold cumulative
  rw [← integral_sub ((positiveCurvature_integrable f hq).integrableOn (s:=Iic x))
    ((negativeCurvature_integrable f hq).integrableOn (s:=Iic x))]
  congr 1
  funext t
  change max (curvature f t) 0-max (-curvature f t) 0=curvature f t
  rcases le_total (curvature f t) 0 with h | h
  · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)];ring
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)];ring

theorem D1_sub_D2 (f : ℝ → ℝ)
    (hAC : ∀ a b,AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) (x : ℝ) : D1 f x-D2 f x=deriv f x := by
  have hc := cumulative_curvature_split f hq x
  have hd := derivative_cumulative_representation f hAC hq x
  change deriv f x=minusInfinitySlope f+cumulative (curvature f) x at hd
  unfold D1 D2 slope
  linarith

theorem C1_hasDerivAt (f : ℝ → ℝ) (hq : Integrable (curvature f)) (x : ℝ) :
    HasDerivAt (C1 f) (D1 f x) x := primitive_hasDerivAt _ (positiveCurvature_integrable f hq) _ _ x

theorem C2_hasDerivAt (f : ℝ → ℝ) (hq : Integrable (curvature f)) (x : ℝ) :
    HasDerivAt (C2 f) (D2 f x) x := primitive_hasDerivAt _ (negativeCurvature_integrable f hq) _ _ x

/-- The actual integrated curvature primitives differ by the original activation. -/
theorem primitive_difference (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b,AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) (x : ℝ) : C1 f x-C2 f x=f x := by
  have hd (y : ℝ) : HasDerivAt (fun z => C1 f z-C2 f z-f z) 0 y := by
    have h := ((C1_hasDerivAt f hq y).fun_sub (C2_hasDerivAt f hq y)).fun_sub (hf y).hasDerivAt
    have hzero : D1 f y-D2 f y-deriv f y=0 := by rw [D1_sub_D2 f hAC hq y];ring
    rw [hzero] at h
    exact h
  have heq := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).deriv) x 0
  simp only [C1,C2,primitive,intervalIntegral.integral_same,add_zero,sub_zero,sub_self] at heq
  dsimp [C1,C2,primitive]
  linarith

theorem D1_abs_bounded (f : ℝ → ℝ) (hq : Integrable (curvature f)) :
    BddAbove (range (fun x => |D1 f x|)) := by
  refine ⟨|minusInfinitySlope f|+∫ t,|positiveCurvature f t|,?_⟩
  rintro y ⟨x,rfl⟩
  exact slope_abs_bound _ (positiveCurvature_integrable f hq) _ x

theorem D2_abs_bounded (f : ℝ → ℝ) (hq : Integrable (curvature f)) :
    BddAbove (range (fun x => |D2 f x|)) := by
  refine ⟨|(0 : ℝ)|+∫ t,|negativeCurvature f t|,?_⟩
  rintro y ⟨x,rfl⟩
  exact slope_abs_bound _ (negativeCurvature_integrable f hq) _ x

theorem commonTilt_bounds (f : ℝ → ℝ) (hq : Integrable (curvature f)) (x : ℝ) :
    |D1 f x|≤commonTilt f ∧ |D2 f x|≤commonTilt f := by
  exact ⟨le_trans (le_csSup (D1_abs_bounded f hq) (mem_range_self x)) (le_max_left _ _),
    le_trans (le_csSup (D2_abs_bounded f hq) (mem_range_self x)) (le_max_right _ _)⟩

/-- Source thm:smooth_dc_split, with the actual curvature integrals, actual
negative-infinity limit and both convex coordinatewise-monotone split functions. -/
theorem smooth_dc_split (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b,AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) :
    Tendsto (deriv f) atBot (𝓝 (minusInfinitySlope f)) ∧
    (∃ B : ℝ,∀ x,|deriv f x|≤B) ∧
    ConvexOn ℝ univ (tilt (C1 f) (commonTilt f)) ∧
    ConvexOn ℝ univ (tilt (C2 f) (commonTilt f)) ∧
    Monotone (tilt (C1 f) (commonTilt f)) ∧
    Monotone (tilt (C2 f) (commonTilt f)) ∧
    ∀ z : ℝ × ℝ, tilt (C1 f) (commonTilt f) z-tilt (C2 f) (commonTilt f) z=f (z.1-z.2) := by
  refine ⟨derivative_limit_atBot f hAC hq,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨|minusInfinitySlope f|+∫ t,|curvature f t|,?_⟩
    intro x
    calc
      |deriv f x|=|slope (curvature f) (minusInfinitySlope f) x| :=
        congrArg abs (derivative_cumulative_representation f hAC hq x)
      _ ≤ _ := slope_abs_bound _ hq _ x
  · apply tilt_convex
    exact primitive_convex _ (positiveCurvature_integrable f hq) (fun x => le_max_right _ _) _ _
  · apply tilt_convex
    exact primitive_convex _ (negativeCurvature_integrable f hq) (fun x => le_max_right _ _) _ _
  · exact tilt_monotone _ _ (C1_hasDerivAt f hq) _ (fun x => (commonTilt_bounds f hq x).1)
  · exact tilt_monotone _ _ (C2_hasDerivAt f hq) _ (fun x => (commonTilt_bounds f hq x).2)
  · intro z
    unfold tilt
    have h := primitive_difference f hf hAC hq (z.1-z.2)
    linarith

/-- The exact M in the construction is the least admissible common monotone tilt. -/
theorem canonical_tilt_minimality (f : ℝ → ℝ) (hq : Integrable (curvature f)) :
    ∀ L, Monotone (tilt (C1 f) L) → Monotone (tilt (C2 f) L) → commonTilt f≤L :=
  (minimum_common_tilt _ _ _ _ (C1_hasDerivAt f hq) (C2_hasDerivAt f hq)
    (D1_abs_bounded f hq) (D2_abs_bounded f hq)).2.2

end HiddenMonotonicity.SmoothDC
