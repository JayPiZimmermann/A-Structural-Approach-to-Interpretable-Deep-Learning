import HiddenMonotonicity.TransformerPairCalculus
import HiddenMonotonicity.LayerNormDCLift

/-! An explicit two-stream implementation of finite-dimensional epsilon LayerNorm. -/
noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity.TransformerDC
open Set
open scoped BigOperators

def layerMean {d : ℕ} (v : Fin d → ℝ) : ℝ := (∑ i, v i) / d

def layerVariance {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  (∑ i, (v i - layerMean v)^2) / d

/-- Population-variance LayerNorm with affine gain and bias. -/
def layerNorm {d : ℕ} (ε : ℝ) (γ β : Fin d → ℝ) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => γ i * ((v i - layerMean v) * (Real.sqrt (ε + layerVariance v))⁻¹) + β i

def meanPair {d : ℕ} (xs : Fin d → ℝ × ℝ) : ℝ × ℝ :=
  scalePair ((d : ℝ)⁻¹) (∑ i, xs i)

def centeredPair {d : ℕ} (xs : Fin d → ℝ × ℝ) (i : Fin d) : ℝ × ℝ :=
  addPair (xs i) (scalePair (-1) (meanPair xs))

def variancePair {d : ℕ} (xs : Fin d → ℝ × ℝ) : ℝ × ℝ :=
  scalePair ((d : ℝ)⁻¹) (∑ i, mulPair (centeredPair xs i) (centeredPair xs i))

def layerNormPair {d : ℕ} (ε : ℝ) (γ β : Fin d → ℝ)
    (xs : Fin d → ℝ × ℝ) : Fin d → ℝ × ℝ :=
  fun i => addPair
    (scalePair (γ i) (mulPair (centeredPair xs i)
      (SmoothDC.inverseSqrtPair ε (variancePair xs))))
    (constPair (β i))

theorem layerVariance_nonnegative {d : ℕ} (v : Fin d → ℝ) : 0 ≤ layerVariance v := by
  unfold layerVariance
  exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg d)

theorem value_meanPair {d : ℕ} (xs : Fin d → ℝ × ℝ) :
    value (meanPair xs) = layerMean (fun i => value (xs i)) := by
  rw [meanPair, value_scalePair, value_sum]
  simp [layerMean, div_eq_mul_inv, mul_comm]

theorem value_centeredPair {d : ℕ} (xs : Fin d → ℝ × ℝ) (i : Fin d) :
    value (centeredPair xs i) = value (xs i) - layerMean (fun j => value (xs j)) := by
  rw [centeredPair, value_addPair, value_scalePair, value_meanPair]
  ring

theorem value_variancePair {d : ℕ} (xs : Fin d → ℝ × ℝ) :
    value (variancePair xs) = layerVariance (fun i => value (xs i)) := by
  rw [variancePair, value_scalePair, value_sum]
  simp only [value_mulPair, value_centeredPair]
  simp [layerVariance, pow_two, div_eq_mul_inv, mul_comm]

theorem layerNormPair_exact {d : ℕ} (ε : ℝ) (hε : 0 < ε)
    (γ β : Fin d → ℝ) (xs : Fin d → ℝ × ℝ) (i : Fin d) :
    value (layerNormPair ε γ β xs i) =
      layerNorm ε γ β (fun j => value (xs j)) i := by
  have hv : 0 ≤ (variancePair xs).1 - (variancePair xs).2 := by
    change 0 ≤ value (variancePair xs)
    rw [value_variancePair]
    exact layerVariance_nonnegative _
  have hr := SmoothDC.inverseSqrtPair_difference ε hε (variancePair xs) hv
  change value (SmoothDC.inverseSqrtPair ε (variancePair xs)) =
    (Real.sqrt (ε + value (variancePair xs)))⁻¹ at hr
  rw [value_variancePair] at hr
  simp only [layerNormPair, value_addPair, value_scalePair, value_mulPair,
    value_constPair, value_centeredPair, hr, layerNorm]

section Regularity
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Preorder E]

theorem meanPair_regular {d : ℕ} (s : Set E) (hs : Convex ℝ s)
    (f : Fin d → E → ℝ × ℝ) (hf : ∀ i, Regular s (f i)) :
    Regular s (fun x => meanPair (fun i => f i x)) := by
  exact (Regular.finset_sum Finset.univ f hs (fun i _ => hf i)).scale _

theorem centeredPair_regular {d : ℕ} (s : Set E) (hs : Convex ℝ s)
    (f : Fin d → E → ℝ × ℝ) (hf : ∀ i, Regular s (f i)) (i : Fin d) :
    Regular s (fun x => centeredPair (fun j => f j x) i) := by
  exact (hf i).add ((meanPair_regular s hs f hf).scale (-1))

theorem variancePair_regular {d : ℕ} (s : Set E) (hs : Convex ℝ s)
    (f : Fin d → E → ℝ × ℝ) (hf : ∀ i, Regular s (f i)) :
    Regular s (fun x => variancePair (fun i => f i x)) := by
  exact (Regular.finset_sum Finset.univ
    (fun i x => mulPair (centeredPair (fun j => f j x) i)
      (centeredPair (fun j => f j x) i)) hs
    (fun i _ => (centeredPair_regular s hs f hf i).mul
      (centeredPair_regular s hs f hf i))).scale _

/-- The explicit LayerNorm graph preserves convex, monotone, nonnegative
streams. Only the represented variance, not the individual streams, enters the
exactness condition of the inverse-square-root primitive. -/
theorem layerNormPair_regular {d : ℕ} (s : Set E) (hs : Convex ℝ s)
    (ε : ℝ) (hε : 0 < ε) (γ β : Fin d → ℝ)
    (f : Fin d → E → ℝ × ℝ) (hf : ∀ i, Regular s (f i)) (i : Fin d) :
    Regular s (fun x => layerNormPair ε γ β (fun j => f j x) i) := by
  have hr := (variancePair_regular s hs f hf).scalar_comp
    (SmoothDC.inverseSqrtPair ε) (SmoothDC.inverseSqrtPair_convex ε hε).1
    (SmoothDC.inverseSqrtPair_convex ε hε).2
    (SmoothDC.inverseSqrtPair_monotone ε hε)
    (SmoothDC.inverseSqrtPair_nonneg ε hε)
  exact (((centeredPair_regular s hs f hf i).mul hr).scale (γ i)).add
    (Regular.const hs (β i))

end Regularity
end HiddenMonotonicity.TransformerDC
