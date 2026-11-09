import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic

/-! A convex monotone two-stream multiplication primitive. -/
noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity.TransformerDC
open Set

abbrev FourStreams := (ℝ × ℝ) × (ℝ × ℝ)

/-- Polarization replaces products of nonnegative streams by convex squares. -/
def productSplit (z : FourStreams) : ℝ × ℝ :=
  (((z.1.1 + z.2.1)^2 + (z.1.2 + z.2.2)^2) / 2,
   ((z.1.1 + z.2.2)^2 + (z.1.2 + z.2.1)^2) / 2)

theorem productSplit_exact (z : FourStreams) :
    (productSplit z).1 - (productSplit z).2 =
      (z.1.1 - z.1.2) * (z.2.1 - z.2.2) := by
  simp only [productSplit]
  ring

theorem productSplit_nonnegative (z : FourStreams) : 0 ≤ productSplit z := by
  constructor <;> dsimp [productSplit] <;> positivity

private theorem square_jensen (u v a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    (a * u + b * v)^2 ≤ a * u^2 + b * v^2 := by
  simpa only [smul_eq_mul] using
    (Even.convexOn_pow (𝕜 := ℝ) (show Even 2 from ⟨1, rfl⟩)).2
      (mem_univ u) (mem_univ v) ha hb hab

theorem productSplit_convex :
    ConvexOn ℝ univ (fun z : FourStreams => (productSplit z).1) ∧
    ConvexOn ℝ univ (fun z : FourStreams => (productSplit z).2) := by
  constructor
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have h1 := square_jensen (x.1.1 + x.2.1) (y.1.1 + y.2.1) a b ha hb hab
    have h2 := square_jensen (x.1.2 + x.2.2) (y.1.2 + y.2.2) a b ha hb hab
    dsimp [productSplit] at *
    nlinarith only [h1, h2]
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have h1 := square_jensen (x.1.1 + x.2.2) (y.1.1 + y.2.2) a b ha hb hab
    have h2 := square_jensen (x.1.2 + x.2.1) (y.1.2 + y.2.1) a b ha hb hab
    dsimp [productSplit] at *
    nlinarith only [h1, h2]

theorem productSplit_monotoneOn :
    MonotoneOn productSplit (Ici (0 : FourStreams)) := by
  intro x hx y _ hxy
  have h1 : (x.1.1 + x.2.1)^2 ≤ (y.1.1 + y.2.1)^2 :=
    pow_le_pow_left₀ (add_nonneg hx.1.1 hx.2.1) (add_le_add hxy.1.1 hxy.2.1) 2
  have h2 : (x.1.2 + x.2.2)^2 ≤ (y.1.2 + y.2.2)^2 :=
    pow_le_pow_left₀ (add_nonneg hx.1.2 hx.2.2) (add_le_add hxy.1.2 hxy.2.2) 2
  have h3 : (x.1.1 + x.2.2)^2 ≤ (y.1.1 + y.2.2)^2 :=
    pow_le_pow_left₀ (add_nonneg hx.1.1 hx.2.2) (add_le_add hxy.1.1 hxy.2.2) 2
  have h4 : (x.1.2 + x.2.1)^2 ≤ (y.1.2 + y.2.1)^2 :=
    pow_le_pow_left₀ (add_nonneg hx.1.2 hx.2.1) (add_le_add hxy.1.2 hxy.2.1) 2
  constructor <;> dsimp [productSplit] <;> linarith

/-- Convexity is preserved when the four incoming streams are nonnegative
convex functions. The nonnegative domain is essential to composition. -/
theorem productSplit_convex_composition {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Set E) (A B C D : E → ℝ)
    (hA : ConvexOn ℝ s A) (hB : ConvexOn ℝ s B)
    (hC : ConvexOn ℝ s C) (hD : ConvexOn ℝ s D)
    (hA0 : ∀ x ∈ s, 0 ≤ A x) (hB0 : ∀ x ∈ s, 0 ≤ B x)
    (hC0 : ∀ x ∈ s, 0 ≤ C x) (hD0 : ∀ x ∈ s, 0 ≤ D x) :
    ConvexOn ℝ s (fun x => (productSplit ((A x, B x), (C x, D x))).1) ∧
    ConvexOn ℝ s (fun x => (productSplit ((A x, B x), (C x, D x))).2) := by
  have hAC := (hA.add hC).pow (fun x hx => add_nonneg (hA0 x hx) (hC0 x hx)) 2
  have hBD := (hB.add hD).pow (fun x hx => add_nonneg (hB0 x hx) (hD0 x hx)) 2
  have hAD := (hA.add hD).pow (fun x hx => add_nonneg (hA0 x hx) (hD0 x hx)) 2
  have hBC := (hB.add hC).pow (fun x hx => add_nonneg (hB0 x hx) (hC0 x hx)) 2
  constructor
  · simpa [productSplit, div_eq_mul_inv, mul_comm] using
      (hAC.add hBD).smul (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  · simpa [productSplit, div_eq_mul_inv, mul_comm] using
      (hAD.add hBC).smul (by norm_num : (0 : ℝ) ≤ 2⁻¹)

theorem productSplit_monotone_composition {E : Type*} [Preorder E]
    (s : Set E) (A B C D : E → ℝ)
    (hA : MonotoneOn A s) (hB : MonotoneOn B s)
    (hC : MonotoneOn C s) (hD : MonotoneOn D s)
    (hA0 : ∀ x ∈ s, 0 ≤ A x) (hB0 : ∀ x ∈ s, 0 ≤ B x)
    (hC0 : ∀ x ∈ s, 0 ≤ C x) (hD0 : ∀ x ∈ s, 0 ≤ D x) :
    MonotoneOn (fun x => productSplit ((A x, B x), (C x, D x))) s := by
  intro x hx y hy hxy
  exact productSplit_monotoneOn
    ⟨⟨hA0 x hx, hB0 x hx⟩, ⟨hC0 x hx, hD0 x hx⟩⟩
    ⟨⟨hA0 y hy, hB0 y hy⟩, ⟨hC0 y hy, hD0 y hy⟩⟩
    ⟨⟨hA hx hy hxy, hB hx hy hxy⟩, ⟨hC hx hy hxy, hD hx hy hxy⟩⟩

end HiddenMonotonicity.TransformerDC
