import HiddenMonotonicity.TwoInflectionDC

/- Handwritten specification contracts: no inferred declaration type is used
to construct an expected type. -/
open Set
open HiddenMonotonicity.SmoothDC

example : ∀ (f g df dg : ℝ → ℝ) (c : ℝ),
    (∀ x, HasDerivAt f (df x) x) →
    (∀ x, HasDerivAt g (dg x) x) →
    f c = g c → df c = dg c →
    ∀ x, HasDerivAt (thresholdJoin f g c) (thresholdJoin df dg c x) x :=
  thresholdJoin_hasDerivAt

example : ∀ (f d : ℝ → ℝ) (a b : ℝ), a < b →
    (∀ x, HasDerivAt f (d x) x) →
    ∀ z, HasDerivAt (centralConvexP f d a b) (centralConvexPFirst d a b z) z :=
  centralConvexP_hasDerivAt

example : ∀ (f d : ℝ → ℝ) (a b : ℝ), a < b →
    (∀ x, HasDerivAt f (d x) x) →
    ∀ z, HasDerivAt (centralConvexQ f d a b) (centralConvexQFirst d a b z) z :=
  centralConvexQ_hasDerivAt

example : ∀ (f d : ℝ → ℝ) (a b z : ℝ),
    centralConvexP f d a b z - centralConvexQ f d a b z = f z :=
  centralConvexP_sub_Q

example : ∀ (d : ℝ → ℝ) (a b : ℝ), a < b →
    MonotoneOn d (Icc a b) → Monotone (centralConvexPFirst d a b) :=
  centralConvexPFirst_monotone

example : ∀ (d : ℝ → ℝ) (a b : ℝ),
    AntitoneOn d (Iic a) → AntitoneOn d (Ici b) →
    Monotone (centralConvexQFirst d a b) :=
  centralConvexQFirst_monotone

example : ∀ (d : ℝ → ℝ) (a b : ℝ), a < b →
    MonotoneOn d (Icc a b) → ∀ z,
    0 ≤ centralConvexPFirst d a b z ∧ centralConvexPFirst d a b z ≤ d b - d a :=
  centralConvexPFirst_bounds

example : ∀ (d : ℝ → ℝ) (a b : ℝ),
    AntitoneOn d (Iic a) → AntitoneOn d (Ici b) →
    (∀ x, x ≤ a → d x ≤ 0) → (∀ x, b ≤ x → 0 ≤ d x) → ∀ z,
    0 ≤ centralConvexQFirst d a b z ∧ centralConvexQFirst d a b z ≤ d b - d a :=
  centralConvexQFirst_bounds

example : ∀ (f d : ℝ → ℝ) (a b : ℝ), a < b →
    (∀ x, HasDerivAt f (d x) x) → MonotoneOn d (Icc a b) →
    ConvexOn ℝ univ (centralConvexP f d a b) :=
  centralConvexP_convex

example : ∀ (f d : ℝ → ℝ) (a b : ℝ), a < b →
    (∀ x, HasDerivAt f (d x) x) → AntitoneOn d (Iic a) → AntitoneOn d (Ici b) →
    ConvexOn ℝ univ (centralConvexQ f d a b) :=
  centralConvexQ_convex

example : ∀ (f d : ℝ → ℝ) (a b : ℝ), a ≤ 0 → 0 ≤ b →
    centralConvexP f d a b 0 = f 0 := centralConvexP_zero

example : ∀ (f d : ℝ → ℝ) (a b : ℝ), a ≤ 0 → 0 ≤ b →
    centralConvexQ f d a b 0 = 0 := centralConvexQ_zero

example : ∀ (f d : ℝ → ℝ) (a b : ℝ), a < b →
    (∀ x, HasDerivAt f (d x) x) →
    AntitoneOn d (Iic a) → MonotoneOn d (Icc a b) → AntitoneOn d (Ici b) →
    (∀ x, x ≤ a → d x ≤ 0) → (∀ x, b ≤ x → 0 ≤ d x) →
    ConvexOn ℝ univ (asymmetricLift (centralConvexP f d a b) (d b - d a)) ∧
    ConvexOn ℝ univ (asymmetricLift (centralConvexQ f d a b) (d b - d a)) ∧
    Monotone (asymmetricLift (centralConvexP f d a b) (d b - d a)) ∧
    Monotone (asymmetricLift (centralConvexQ f d a b) (d b - d a)) ∧
    ∀ z : ℝ × ℝ,
      asymmetricLift (centralConvexP f d a b) (d b - d a) z -
        asymmetricLift (centralConvexQ f d a b) (d b - d a) z = f (z.1 - z.2) :=
  centralConvex_asymmetric_split

example : ∀ (f d : ℝ → ℝ) (a b : ℝ), a ≤ 0 → 0 ≤ b →
    asymmetricLift (centralConvexP f d a b) (d b - d a) (0, 0) = f 0 ∧
    asymmetricLift (centralConvexQ f d a b) (d b - d a) (0, 0) = 0 :=
  centralConvex_asymmetric_zero

#print axioms thresholdJoin
#print axioms thresholdJoin_hasDerivAt
#print axioms centralConvexP
#print axioms centralConvexQ
#print axioms centralConvexPFirst
#print axioms centralConvexQFirst
#print axioms centralConvexP_hasDerivAt
#print axioms centralConvexQ_hasDerivAt
#print axioms centralConvexP_sub_Q
#print axioms centralConvexPFirst_monotone
#print axioms centralConvexQFirst_monotone
#print axioms centralConvexPFirst_bounds
#print axioms centralConvexQFirst_bounds
#print axioms centralConvexP_convex
#print axioms centralConvexQ_convex
#print axioms centralConvexP_zero
#print axioms centralConvexQ_zero
#print axioms centralConvex_asymmetric_split
#print axioms centralConvex_asymmetric_zero
