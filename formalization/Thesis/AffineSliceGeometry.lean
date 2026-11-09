import Thesis.SupportDerivatives

/-! Geometry on the affine slice used by biased max-affine networks.  Visibility
requires exposure by an actual direction `(x,1)`; it is not ambient extremality. -/
noncomputable section
namespace Thesis.Tropical
open Finset Matrix Filter
open scoped Topology
variable {I A : Type} [Fintype I] [Fintype A] [Nonempty A]

/-- The admissible directions of a homogenized affine function. -/
def affineSlice (x : I → ℝ) : I ⊕ Unit → ℝ := Sum.elim x (fun _ => 1)

/-- The actual input coordinates of a lifted coefficient vector. -/
def inputProjection (p : I ⊕ Unit → ℝ) : I → ℝ := fun i => p (Sum.inl i)

theorem affineSlice_pairing (p : I ⊕ Unit → ℝ) (x : I → ℝ) :
    p ⬝ᵥ affineSlice x = inputProjection p ⬝ᵥ x+p (Sum.inr ()) := by
  simp [affineSlice,inputProjection,dotProduct,Fintype.sum_sum_type]

/-- A lifted point is visible if a permitted slice direction exposes precisely it. -/
def SliceVisible (v : A → I ⊕ Unit → ℝ) (p : I ⊕ Unit → ℝ) : Prop :=
  p ∈ convexHull ℝ (Set.range v) ∧ ∃ x : I → ℝ,
    p ⬝ᵥ affineSlice x = support (convexHull ℝ (Set.range v)) (affineSlice x) ∧
    ∀ q ∈ convexHull ℝ (Set.range v),
      q ⬝ᵥ affineSlice x = support (convexHull ℝ (Set.range v)) (affineSlice x) → q=p

theorem sliceVisible_extreme (v : A → I ⊕ Unit → ℝ) (p : I ⊕ Unit → ℝ)
    (hp : SliceVisible v p) : p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ := by
  obtain ⟨hmem,x,he,huniq⟩ := hp
  exact unique_face_extreme v (affineSlice x) p hmem he huniq

/-- The restricted derivative identifies the input projection of every maximizing
lifted point; the intercept is not itself an input derivative. -/
theorem slice_maximizing_point_derivative (v : A → I ⊕ Unit → ℝ)
    (x : I → ℝ) (p : I ⊕ Unit → ℝ) (hp : p ∈ convexHull ℝ (Set.range v))
    (he : p ⬝ᵥ affineSlice x = support (convexHull ℝ (Set.range v)) (affineSlice x))
    (D : (I → ℝ) →L[ℝ] ℝ)
    (hd : HasFDerivAt (fun y => support (convexHull ℝ (Set.range v)) (affineSlice y)) D x) :
    D = gradientRow (inputProjection p) := by
  have hm : IsLocalMin (fun y => support (convexHull ℝ (Set.range v)) (affineSlice y)-
      (gradientRow (inputProjection p) y+p (Sum.inr ()))) x := by
    apply Filter.Eventually.of_forall
    intro y
    simp only [gradientRow_apply]
    have hy := dot_le_support_hull v hp (affineSlice y)
    rw [affineSlice_pairing] at he hy
    linarith
  exact sub_eq_zero.mp (hm.hasFDerivAt_eq_zero
    (hd.sub ((gradientRow (inputProjection p)).hasFDerivAt.add_const _)))

/-- Equal projections and equal objective values on one affine slice determine
all coordinates of a lifted point, including its intercept. -/
theorem lifted_eq_of_projection_pairing {p q : I ⊕ Unit → ℝ} (x : I → ℝ)
    (hproj : inputProjection p=inputProjection q)
    (he : p ⬝ᵥ affineSlice x=q ⬝ᵥ affineSlice x) : p=q := by
  have hb : p (Sum.inr ())=q (Sum.inr ()) := by
    rw [affineSlice_pairing,affineSlice_pairing,hproj] at he
    exact add_left_cancel he
  funext j
  cases j with
  | inl i => exact congrFun hproj i
  | inr u => cases u; exact hb

/-- Strict slice exposure gives a genuine derivative of the restricted support. -/
theorem slice_unique_generator_hasFDerivAt (v : A → I ⊕ Unit → ℝ)
    (x : I → ℝ) (p : I ⊕ Unit → ℝ) (hp : ∃ a, v a=p)
    (hgap : ∀ a, v a≠p → v a ⬝ᵥ affineSlice x<p ⬝ᵥ affineSlice x) :
    HasFDerivAt (fun y => support (convexHull ℝ (Set.range v)) (affineSlice y))
      (gradientRow (inputProjection p)) x := by
  have hc : ∀ q : I ⊕ Unit → ℝ, Continuous (fun y : I → ℝ => q ⬝ᵥ affineSlice y) := by
    intro q
    have he : (fun y : I → ℝ => q ⬝ᵥ affineSlice y) =
        fun y => gradientRow (inputProjection q) y+q (Sum.inr ()) := by
      funext y; rw [gradientRow_apply,affineSlice_pairing]
    rw [he]
    exact (gradientRow (inputProjection q)).continuous.add continuous_const
  have heach : ∀ a, ∀ᶠ y in 𝓝 x, v a ⬝ᵥ affineSlice y≤p ⬝ᵥ affineSlice y := by
    intro a
    by_cases he : v a=p
    · exact Filter.Eventually.of_forall fun y => by rw [he]
    · exact ((hc (v a)).continuousAt.eventually_lt (hc p).continuousAt (hgap a he)).mono
        fun _ h => h.le
  have hall := Filter.eventually_all.mpr heach
  apply ((gradientRow (inputProjection p)).hasFDerivAt.add_const (p (Sum.inr ()))).congr_of_eventuallyEq
  filter_upwards [hall] with y hy
  rw [gradientRow_apply,← affineSlice_pairing,support_convexHull]
  apply le_antisymm
  · exact finiteMax_le _ _ hy
  · obtain ⟨a,rfl⟩ := hp
    exact le_finiteMax (fun a => v a ⬝ᵥ affineSlice y) a

/-- At each input, differentiability of the restricted support is equivalent to
its lifted exposed face being a singleton. The derivative is projected to inputs. -/
theorem slice_hasFDerivAt_iff (v : A → I ⊕ Unit → ℝ) (x s : I → ℝ) :
    HasFDerivAt (fun y => support (convexHull ℝ (Set.range v)) (affineSlice y))
        (gradientRow s) x ↔
    ∃ p ∈ convexHull ℝ (Set.range v), inputProjection p=s ∧
      p ⬝ᵥ affineSlice x=support (convexHull ℝ (Set.range v)) (affineSlice x) ∧
      ∀ q ∈ convexHull ℝ (Set.range v),
        q ⬝ᵥ affineSlice x=support (convexHull ℝ (Set.range v)) (affineSlice x) → q=p := by
  constructor
  · intro hd
    obtain ⟨a,ha⟩ := finiteMax_attained (fun a => v a ⬝ᵥ affineSlice x)
    have hm := subset_convexHull ℝ (Set.range v) (Set.mem_range_self a)
    have he : v a ⬝ᵥ affineSlice x=support (convexHull ℝ (Set.range v)) (affineSlice x) := by
      rw [support_convexHull,ha]
    have hs := gradientRow_injective (slice_maximizing_point_derivative v x (v a) hm he _ hd)
    refine ⟨v a,hm,hs.symm,he,?_⟩
    intro q hq hq'
    have hqs := gradientRow_injective (slice_maximizing_point_derivative v x q hq hq' _ hd)
    exact lifted_eq_of_projection_pairing x (hqs.symm.trans hs) (hq'.trans he.symm)
  · rintro ⟨p,hp,hs,he,huniq⟩
    have hex : ∃ a, v a=p := by
      obtain ⟨a,ha⟩ := finiteMax_attained (fun a => v a ⬝ᵥ affineSlice x)
      refine ⟨a,huniq _ (subset_convexHull ℝ _ (Set.mem_range_self a)) ?_⟩
      rw [support_convexHull,ha]
    rw [← hs]
    apply slice_unique_generator_hasFDerivAt v x p hex
    intro a hne
    have hle := dot_le_support_hull v (subset_convexHull ℝ _ (Set.mem_range_self a)) (affineSlice x)
    rw [← he] at hle
    apply lt_of_le_of_ne hle
    intro heq
    exact hne (huniq _ (subset_convexHull ℝ _ (Set.mem_range_self a)) (heq.trans he))

/-- Correct attainable-gradient theorem for biased functions: exactly the input
projections of slice-visible lifted vertices, rather than all ambient vertices. -/
theorem slice_attainable_gradients (v : A → I ⊕ Unit → ℝ) (s : I → ℝ) :
    (∃ x, HasFDerivAt (fun y => support (convexHull ℝ (Set.range v)) (affineSlice y))
      (gradientRow s) x) ↔
    ∃ p, SliceVisible v p ∧ p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ ∧
      inputProjection p=s := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨p,hp,hs,he,hu⟩ := (slice_hasFDerivAt_iff v x s).mp hx
    have hv : SliceVisible v p := ⟨hp,x,he,hu⟩
    exact ⟨p,hv,sliceVisible_extreme v p hv,hs⟩
  · rintro ⟨p,⟨hp,x,he,hu⟩,_,hs⟩
    exact ⟨x,(slice_hasFDerivAt_iff v x s).mpr ⟨p,hp,hs,he,hu⟩⟩

/-- The slice theorem applied to the actual tropical-polynomial homogenization. -/
theorem Polynomial.attainable_gradients (p : Polynomial I) (s : I → ℝ) :
    (∃ x, HasFDerivAt p.eval (gradientRow s) x) ↔
    ∃ q, SliceVisible p.lift.slope q ∧ q ∈ p.lift.newton.extremePoints ℝ ∧
      inputProjection q=s := by
  have he : p.eval = fun y => support (convexHull ℝ (Set.range p.lift.slope)) (affineSlice y) :=
    funext p.lifted_support
  rw [he]
  exact slice_attainable_gradients p.lift.slope s

end Thesis.Tropical
