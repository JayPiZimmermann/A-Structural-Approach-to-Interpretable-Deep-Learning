import HiddenMonotonicity.TransformerPairCalculus

/-! Convex substitution into nonnegative doubled inputs, without an assumption
that the original signed-input lift is monotone. -/
noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity.TransformerDC
open Set

theorem convex_monotone_vector_comp_on {E ι : Type*}
    [AddCommGroup E] [Module ℝ E]
    (s : Set E) (hs : Convex ℝ s)
    (φ : ((ι → ℝ) × (ι → ℝ)) → ℝ)
    (hc : ConvexOn ℝ (Ici (0 : (ι → ℝ) × (ι → ℝ))) φ)
    (hm : MonotoneOn φ (Ici (0 : (ι → ℝ) × (ι → ℝ))))
    (p q : E → ι → ℝ)
    (hp : ∀ i, ConvexOn ℝ s (fun x => p x i))
    (hq : ∀ i, ConvexOn ℝ s (fun x => q x i))
    (hp0 : ∀ x ∈ s, 0 ≤ p x) (hq0 : ∀ x ∈ s, 0 ≤ q x) :
    ConvexOn ℝ s (fun x => φ (p x, q x)) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hinner : (p (a • x + b • y), q (a • x + b • y)) ≤
      a • (p x, q x) + b • (p y, q y) := by
    exact ⟨fun i => (hp i).2 hx hy ha hb hab,
      fun i => (hq i).2 hx hy ha hb hab⟩
  have hmix : a • x + b • y ∈ s := hs hx hy ha hb hab
  have hinner0 : (0 : (ι → ℝ) × (ι → ℝ)) ≤
      (p (a • x + b • y), q (a • x + b • y)) :=
    ⟨hp0 _ hmix, hq0 _ hmix⟩
  have houter0 : (0 : (ι → ℝ) × (ι → ℝ)) ≤
      a • (p x, q x) + b • (p y, q y) := by
    constructor
    · intro i
      exact add_nonneg (mul_nonneg ha (hp0 x hx i)) (mul_nonneg hb (hp0 y hy i))
    · intro i
      exact add_nonneg (mul_nonneg ha (hq0 x hx i)) (mul_nonneg hb (hq0 y hy i))
  exact (hm hinner0 houter0 hinner).trans
    (hc.2 ⟨hp0 x hx, hq0 x hx⟩ ⟨hp0 y hy, hq0 y hy⟩ ha hb hab)

/-- The positive and negative parts are nonnegative convex input coordinates
and preserve convexity of the resulting raw-input head. Raw-input monotonicity
is not imposed. -/
theorem convex_signed_input_lift {ι : Type*}
    (φ : ((ι → ℝ) × (ι → ℝ)) → ℝ)
    (hc : ConvexOn ℝ (Ici (0 : (ι → ℝ) × (ι → ℝ))) φ)
    (hm : MonotoneOn φ (Ici (0 : (ι → ℝ) × (ι → ℝ)))) :
    ConvexOn ℝ univ (fun x : ι → ℝ =>
      φ ((fun i => max (x i) 0), (fun i => max (-x i) 0))) := by
  apply convex_monotone_vector_comp_on univ convex_univ φ hc hm
  · intro i
    have hlin : ConvexOn ℝ univ (fun x : ι → ℝ => x i) := by
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      exact le_rfl
    exact hlin.sup (convexOn_const 0 convex_univ)
  · intro i
    have hlin : ConvexOn ℝ univ (fun x : ι → ℝ => -x i) := by
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    exact hlin.sup (convexOn_const 0 convex_univ)
  · intro x hx i
    exact le_max_right _ _
  · intro x hx i
    exact le_max_right _ _

end HiddenMonotonicity.TransformerDC
