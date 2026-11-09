import Thesis.RandomizationExpectation

/-! Routing randomization from a conditional bound on the actual ordinary-row
affinity. Strictly different random parameters do not imply this hypothesis.
The probability space, conditioning, prefix measurability, and integrability are
explicit; the conclusion concerns ordinary surviving paths. -/
noncomputable section
namespace Thesis.RoutingExpectation
open MeasureTheory Filter Finset Thesis.Games Thesis.Randomization
open Thesis.RandomizationExpectation
open scoped MeasureTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {S : Type} [Fintype S] [DecidableEq S]

omit mΩ [DecidableEq S] in
/-- The ordinary affinity of the trained row and the randomized row. -/
def rowAffinity (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ)
    (n : ℕ) (s : S) (ω : Ω) : ℝ := ∑ t, Real.sqrt (A n s t * B n ω s t)

/-- Conditional row-affinity contraction yields the complete-prefix expected bound. -/
theorem conditional_affinity_contraction (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) (s₀ : S)
    (b : ℝ) (hb : 0 ≤ b)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (rowAffinity A B n s) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s *
      rowAffinity A B n s ω) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n]
      (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (n : ℕ) (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ, μ[rowAffinity A B l s | ℱ l] ω ≤ b) :
    (∫ ω, ordinaryOverlap n A (fun l => B l ω) s₀ ∂μ) ≤ b^n := by
  have h := thesis_randomization_stopping μ ℱ hm (modelKernel A B) s₀
    (rowAffinity A B) b hb (fun _ _ _ _ => Real.sqrt_nonneg _)
    (fun _ _ _ => le_rfl) hg ha hga hgm n hcond
  simpa only [randomMass_model_overlap] using h

/-- Additional substochastic layers cannot undo contraction of the randomized prefix. -/
theorem conditional_affinity_full_depth (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hm : ∀ n, ℱ n ≤ mΩ)
    (A : ℕ → S → S → ℝ) (B : ℕ → Ω → S → S → ℝ) (s₀ : S)
    (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ n s t, 0 ≤ A n s t) (hB : ∀ n ω s t, 0 ≤ B n ω s t)
    (hArow : ∀ n s, ∑ t, A n s t ≤ 1) (hBrow : ∀ n ω s, ∑ t, B n ω s t ≤ 1)
    (hg : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (ha : ∀ n s, Integrable (rowAffinity A B n s) μ)
    (hga : ∀ n s, Integrable (fun ω => randomPrefix (modelKernel A B) s₀ n ω s *
      rowAffinity A B n s ω) μ)
    (hgm : ∀ n s, AEStronglyMeasurable[ℱ n]
      (fun ω => randomPrefix (modelKernel A B) s₀ n ω s) μ)
    (n extra : ℕ)
    (hcond : ∀ l < n, ∀ s, ∀ᵐ ω ∂μ, μ[rowAffinity A B l s | ℱ l] ω ≤ b) :
    (∫ ω, ordinaryOverlap (n+extra) A (fun l => B l ω) s₀ ∂μ) ≤ b^n := by
  have hprefix : Integrable (fun ω => ordinaryOverlap n A (fun l => B l ω) s₀) μ := by
    exact (integrable_finsetSum univ (fun s _ => hg n s)).congr
      (ae_of_all _ (fun ω => randomMass_model_overlap A B s₀ n ω))
  have hfull : Integrable (fun ω => ordinaryOverlap (n+extra) A (fun l => B l ω) s₀) μ := by
    exact (integrable_finsetSum univ (fun s _ => hg (n+extra) s)).congr
      (ae_of_all _ (fun ω => randomMass_model_overlap A B s₀ (n+extra) ω))
  have hmono := integral_mono hfull hprefix (fun ω =>
    ordinaryOverlap_antitone A (fun l => B l ω) hA (fun l u v => hB l ω u v)
      hArow (fun l u => hBrow l ω u) s₀ (Nat.le_add_right n extra))
  exact hmono.trans (conditional_affinity_contraction μ ℱ hm A B s₀ b hb hg ha hga hgm n hcond)

end Thesis.RoutingExpectation
