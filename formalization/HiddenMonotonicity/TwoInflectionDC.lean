import HiddenMonotonicity.CurvaturePrimitives
import HiddenMonotonicity.MonotoneDCLift

namespace HiddenMonotonicity.SmoothDC
open Set Filter
open scoped Topology

/-- Join two scalar functions at an ordered threshold. -/
noncomputable def thresholdJoin (f g : ℝ → ℝ) (c x : ℝ) : ℝ :=
  if x ≤ c then f x else g x

/-- Matching values and derivatives make a threshold join differentiable,
including at the threshold itself. -/
theorem thresholdJoin_hasDerivAt (f g df dg : ℝ → ℝ) (c : ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x)
    (hg : ∀ x, HasDerivAt g (dg x) x)
    (hv : f c = g c) (hd : df c = dg c) (x : ℝ) :
    HasDerivAt (thresholdJoin f g c) (thresholdJoin df dg c x) x := by
  rcases lt_trichotomy x c with hxc | hxc | hcx
  · simp only [thresholdJoin, ite_eq_left hxc.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hxc] with z hz
    simp [thresholdJoin, hz.le]
  · subst x
    have hl : HasDerivWithinAt (thresholdJoin f g c) (df c) (Iic c) c :=
      (hf c).hasDerivWithinAt.congr
        (fun z hz => by simp [thresholdJoin, show z ≤ c from hz]) (by simp [thresholdJoin])
    have hr : HasDerivWithinAt (thresholdJoin f g c) (df c) (Ici c) c := by
      rw [hd]
      apply (hg c).hasDerivWithinAt.congr
      · intro z hz
        by_cases hzc : z ≤ c
        · have he : z = c := le_antisymm hzc hz
          subst z
          simpa [thresholdJoin] using hv
        · simp [thresholdJoin, hzc]
      · simpa [thresholdJoin] using hv
    have hu : Iic c ∪ Ici c = (univ : Set ℝ) := by
      ext z
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total z c
    simpa only [hu, hasDerivWithinAt_univ, thresholdJoin, ite_eq_left le_rfl] using hl.union hr
  · simp only [thresholdJoin, ite_eq_right (not_le.mpr hcx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hcx] with z hz
    simp [thresholdJoin, not_le.mpr hz]

/-- Closed positive-curvature primitive for a function whose curvature is
nonpositive on both tails and nonnegative between `a` and `b`. -/
noncomputable def centralConvexP (f d : ℝ → ℝ) (a b z : ℝ) : ℝ :=
  if z ≤ a then f a - d a * a
  else if z ≤ b then f z - d a * z
  else f b - d a * b + (d b - d a) * (z - b)

/-- The complementary closed primitive; the original activation is recovered
by subtracting this function from `centralConvexP`. -/
noncomputable def centralConvexQ (f d : ℝ → ℝ) (a b z : ℝ) : ℝ :=
  centralConvexP f d a b z - f z

noncomputable def centralConvexPFirst (d : ℝ → ℝ) (a b z : ℝ) : ℝ :=
  if z ≤ a then 0 else if z ≤ b then d z - d a else d b - d a

noncomputable def centralConvexQFirst (d : ℝ → ℝ) (a b z : ℝ) : ℝ :=
  centralConvexPFirst d a b z - d z

theorem centralConvexP_hasDerivAt (f d : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : ∀ x, HasDerivAt f (d x) x) (z : ℝ) :
    HasDerivAt (centralConvexP f d a b) (centralConvexPFirst d a b z) z := by
  let u : ℝ → ℝ := fun x => f x - d a * x
  let du : ℝ → ℝ := fun x => d x - d a
  have hu : ∀ x, HasDerivAt u (du x) x := by
    intro x
    convert (hf x).sub ((hasDerivAt_id x).const_mul (d a)) using 1
    · funext y
      rfl
    · simp [du]
  have hi := thresholdJoin_hasDerivAt (fun _ => f a - d a * a) u
    (fun _ => 0) du a (fun _ => hasDerivAt_const _ _) hu rfl (by simp [du])
  have hb : thresholdJoin (fun _ => f a - d a * a) u a b =
      f b - d a * b + (d b - d a) * (b - b) := by
    simp [thresholdJoin, not_le.mpr hab, u]
  have hdb : thresholdJoin (fun _ => (0 : ℝ)) du a b = d b - d a := by
    simp [thresholdJoin, not_le.mpr hab, du]
  have ho := thresholdJoin_hasDerivAt
    (thresholdJoin (fun _ => f a - d a * a) u a)
    (fun x => f b - d a * b + (d b - d a) * (x - b))
    (thresholdJoin (fun _ => 0) du a) (fun _ => d b - d a) b hi
    (fun x => by convert (((hasDerivAt_id x).sub_const b).const_mul
      (d b - d a)).const_add (f b - d a * b) using 1 <;> simp) hb hdb z
  convert ho using 1
  · funext x
    by_cases hxa : x ≤ a
    · simp [centralConvexP, thresholdJoin, hxa, le_trans hxa hab.le]
    · simp [centralConvexP, thresholdJoin, hxa, u]
  · by_cases hza : z ≤ a
    · simp [centralConvexPFirst, thresholdJoin, hza, le_trans hza hab.le]
    · simp [centralConvexPFirst, thresholdJoin, hza, du]

theorem centralConvexQ_hasDerivAt (f d : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : ∀ x, HasDerivAt f (d x) x) (z : ℝ) :
    HasDerivAt (centralConvexQ f d a b) (centralConvexQFirst d a b z) z :=
  (centralConvexP_hasDerivAt f d a b hab hf z).sub (hf z)

theorem centralConvexP_sub_Q (f d : ℝ → ℝ) (a b z : ℝ) :
    centralConvexP f d a b z - centralConvexQ f d a b z = f z := by
  unfold centralConvexQ
  ring

theorem centralConvexPFirst_monotone (d : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hmiddle : MonotoneOn d (Icc a b)) : Monotone (centralConvexPFirst d a b) := by
  have habd := hmiddle ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
  intro x y hxy
  by_cases hxa : x ≤ a
  · by_cases hya : y ≤ a
    · simp [centralConvexPFirst, hxa, hya]
    · by_cases hyb : y ≤ b
      · have had := hmiddle ⟨le_rfl, hab.le⟩ ⟨(not_le.mp hya).le, hyb⟩
          (not_le.mp hya).le
        simp only [centralConvexPFirst, ite_eq_left hxa, ite_eq_right hya, ite_eq_left hyb]
        linarith
      · simp only [centralConvexPFirst, ite_eq_left hxa, ite_eq_right hya, ite_eq_right hyb]
        linarith
  · have hya : ¬y ≤ a := by linarith
    by_cases hxb : x ≤ b
    · by_cases hyb : y ≤ b
      · have hdd := hmiddle ⟨(not_le.mp hxa).le, hxb⟩
          ⟨(not_le.mp hya).le, hyb⟩ hxy
        simp only [centralConvexPFirst, ite_eq_right hxa, ite_eq_right hya, ite_eq_left hxb, ite_eq_left hyb]
        linarith
      · have hbd := hmiddle ⟨(not_le.mp hxa).le, hxb⟩ ⟨hab.le, le_rfl⟩ hxb
        simp only [centralConvexPFirst, ite_eq_right hxa, ite_eq_right hya, ite_eq_left hxb, ite_eq_right hyb]
        linarith
    · have hyb : ¬y ≤ b := by linarith
      simp [centralConvexPFirst, hxa, hya, hxb, hyb]

theorem centralConvexQFirst_monotone (d : ℝ → ℝ) (a b : ℝ)
    (hleft : AntitoneOn d (Iic a)) (hright : AntitoneOn d (Ici b)) :
    Monotone (centralConvexQFirst d a b) := by
  intro x y hxy
  by_cases hxa : x ≤ a
  · have had : d a ≤ d x := hleft hxa (show a ≤ a from le_rfl) hxa
    by_cases hya : y ≤ a
    · have hdd := hleft hxa hya hxy
      simp only [centralConvexQFirst, centralConvexPFirst, ite_eq_left hxa, ite_eq_left hya]
      linarith
    · by_cases hyb : y ≤ b
      · simp only [centralConvexQFirst, centralConvexPFirst,
          ite_eq_left hxa, ite_eq_right hya, ite_eq_left hyb]
        linarith
      · have hbd : d y ≤ d b := hright (show b ≤ b from le_rfl)
          (not_le.mp hyb).le (not_le.mp hyb).le
        simp only [centralConvexQFirst, centralConvexPFirst,
          ite_eq_left hxa, ite_eq_right hya, ite_eq_right hyb]
        linarith
  · have hya : ¬y ≤ a := by linarith
    by_cases hxb : x ≤ b
    · by_cases hyb : y ≤ b
      · simp only [centralConvexQFirst, centralConvexPFirst,
          ite_eq_right hxa, ite_eq_right hya, ite_eq_left hxb, ite_eq_left hyb]
        linarith
      · have hbd : d y ≤ d b := hright (show b ≤ b from le_rfl)
          (not_le.mp hyb).le (not_le.mp hyb).le
        simp only [centralConvexQFirst, centralConvexPFirst,
          ite_eq_right hxa, ite_eq_right hya, ite_eq_left hxb, ite_eq_right hyb]
        linarith
    · have hyb : ¬y ≤ b := by linarith
      have hdd := hright (not_le.mp hxb).le (not_le.mp hyb).le hxy
      simp only [centralConvexQFirst, centralConvexPFirst,
        ite_eq_right hxa, ite_eq_right hya, ite_eq_right hxb, ite_eq_right hyb]
      linarith

theorem centralConvexPFirst_bounds (d : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hmiddle : MonotoneOn d (Icc a b)) (z : ℝ) :
    0 ≤ centralConvexPFirst d a b z ∧ centralConvexPFirst d a b z ≤ d b - d a := by
  have habd := hmiddle ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
  by_cases hza : z ≤ a
  · simp only [centralConvexPFirst, ite_eq_left hza]
    constructor <;> linarith
  · by_cases hzb : z ≤ b
    · have had := hmiddle ⟨le_rfl, hab.le⟩ ⟨(not_le.mp hza).le, hzb⟩ (not_le.mp hza).le
      have hbd := hmiddle ⟨(not_le.mp hza).le, hzb⟩ ⟨hab.le, le_rfl⟩ hzb
      simp only [centralConvexPFirst, ite_eq_right hza, ite_eq_left hzb]
      constructor <;> linarith
    · simp only [centralConvexPFirst, ite_eq_right hza, ite_eq_right hzb]
      constructor <;> linarith

theorem centralConvexQFirst_bounds (d : ℝ → ℝ) (a b : ℝ)
    (hleft : AntitoneOn d (Iic a)) (hright : AntitoneOn d (Ici b))
    (hleft_sign : ∀ x, x ≤ a → d x ≤ 0)
    (hright_sign : ∀ x, b ≤ x → 0 ≤ d x) (z : ℝ) :
    0 ≤ centralConvexQFirst d a b z ∧ centralConvexQFirst d a b z ≤ d b - d a := by
  have ha := hleft_sign a le_rfl
  have hb := hright_sign b le_rfl
  by_cases hza : z ≤ a
  · have had := hleft hza (show a ≤ a from le_rfl) hza
    have hz := hleft_sign z hza
    simp only [centralConvexQFirst, centralConvexPFirst, ite_eq_left hza]
    constructor <;> linarith
  · by_cases hzb : z ≤ b
    · simp only [centralConvexQFirst, centralConvexPFirst, ite_eq_right hza, ite_eq_left hzb]
      constructor <;> linarith
    · have hbd := hright (show b ≤ b from le_rfl) (not_le.mp hzb).le (not_le.mp hzb).le
      have hz := hright_sign z (not_le.mp hzb).le
      simp only [centralConvexQFirst, centralConvexPFirst, ite_eq_right hza, ite_eq_right hzb]
      constructor <;> linarith

/-- The closed positive primitive is convex as soon as the original slope
increases on the central interval. -/
theorem centralConvexP_convex (f d : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ x, HasDerivAt f (d x) x) (hmiddle : MonotoneOn d (Icc a b)) :
    ConvexOn ℝ univ (centralConvexP f d a b) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (centralConvexP_hasDerivAt f d a b hab hf x).differentiableAt)
  intro x y hxy
  rw [(centralConvexP_hasDerivAt f d a b hab hf x).deriv,
    (centralConvexP_hasDerivAt f d a b hab hf y).deriv]
  exact centralConvexPFirst_monotone d a b hab hmiddle hxy

/-- The closed complementary primitive is convex as soon as the original
slope decreases on both tails. -/
theorem centralConvexQ_convex (f d : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ x, HasDerivAt f (d x) x)
    (hleft : AntitoneOn d (Iic a)) (hright : AntitoneOn d (Ici b)) :
    ConvexOn ℝ univ (centralConvexQ f d a b) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (centralConvexQ_hasDerivAt f d a b hab hf x).differentiableAt)
  intro x y hxy
  rw [(centralConvexQ_hasDerivAt f d a b hab hf x).deriv,
    (centralConvexQ_hasDerivAt f d a b hab hf y).deriv]
  exact centralConvexQFirst_monotone d a b hleft hright hxy

theorem centralConvexP_zero (f d : ℝ → ℝ) (a b : ℝ) (ha : a ≤ 0) (hb : 0 ≤ b) :
    centralConvexP f d a b 0 = f 0 := by
  by_cases he : 0 ≤ a
  · have hzero : a = 0 := le_antisymm ha he
    simp [centralConvexP, hzero]
  · simp [centralConvexP, he, hb]

theorem centralConvexQ_zero (f d : ℝ → ℝ) (a b : ℝ) (ha : a ≤ 0) (hb : 0 ≤ b) :
    centralConvexQ f d a b 0 = 0 := by
  simp [centralConvexQ, centralConvexP_zero f d a b ha hb]

/-- Explicit closed two-stream decomposition from elementary slope properties.
The hypotheses describe the original activation; neither convexity nor
monotonicity of the constructed streams is assumed. -/
theorem centralConvex_asymmetric_split (f d : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ∀ x, HasDerivAt f (d x) x)
    (hleft : AntitoneOn d (Iic a)) (hmiddle : MonotoneOn d (Icc a b))
    (hright : AntitoneOn d (Ici b))
    (hleft_sign : ∀ x, x ≤ a → d x ≤ 0)
    (hright_sign : ∀ x, b ≤ x → 0 ≤ d x) :
    ConvexOn ℝ univ (asymmetricLift (centralConvexP f d a b) (d b - d a)) ∧
    ConvexOn ℝ univ (asymmetricLift (centralConvexQ f d a b) (d b - d a)) ∧
    Monotone (asymmetricLift (centralConvexP f d a b) (d b - d a)) ∧
    Monotone (asymmetricLift (centralConvexQ f d a b) (d b - d a)) ∧
    ∀ z : ℝ × ℝ,
      asymmetricLift (centralConvexP f d a b) (d b - d a) z -
        asymmetricLift (centralConvexQ f d a b) (d b - d a) z = f (z.1 - z.2) := by
  refine ⟨asymmetricLift_convex _ _ (centralConvexP_convex f d a b hab hf hmiddle),
    asymmetricLift_convex _ _ (centralConvexQ_convex f d a b hab hf hleft hright),
    ?_, ?_, asymmetricLift_difference _ _ _ _ (centralConvexP_sub_Q f d a b)⟩
  · exact asymmetricLift_monotone _ _ (centralConvexP_hasDerivAt f d a b hab hf) _
      (centralConvexPFirst_bounds d a b hab hmiddle)
  · exact asymmetricLift_monotone _ _ (centralConvexQ_hasDerivAt f d a b hab hf) _
      (centralConvexQFirst_bounds d a b hleft hright hleft_sign hright_sign)

/-- For thresholds surrounding zero, the closed profiles preserve the
activation's baseline exactly. -/
theorem centralConvex_asymmetric_zero (f d : ℝ → ℝ) (a b : ℝ)
    (ha : a ≤ 0) (hb : 0 ≤ b) :
    asymmetricLift (centralConvexP f d a b) (d b - d a) (0, 0) = f 0 ∧
    asymmetricLift (centralConvexQ f d a b) (d b - d a) (0, 0) = 0 := by
  simp [asymmetricLift, centralConvexP_zero f d a b ha hb,
    centralConvexQ_zero f d a b ha hb]

end HiddenMonotonicity.SmoothDC
