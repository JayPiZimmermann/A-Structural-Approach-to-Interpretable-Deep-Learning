import HiddenMonotonicity.LayerNormDC

set_option autoImplicit false
open Set HiddenMonotonicity.TransformerDC

example (c : ℝ) : layerMean (fun _ : Fin 1 => c) = c := by
  simp [layerMean]

example (c : ℝ) : layerVariance (fun _ : Fin 1 => c) = 0 := by
  simp [layerVariance, layerMean]

example (ε c : ℝ) (γ β : Fin 1 → ℝ) :
    layerNorm ε γ β (fun _ => c) 0 = β 0 := by
  simp [layerNorm, layerVariance, layerMean]

example (ε : ℝ) (hε : 0 < ε) :
    value (layerNormPair ε (fun _ : Fin 1 => -3) (fun _ => 7)
      (fun _ => (5, 1)) 0) = 7 := by
  rw [layerNormPair_exact ε hε]
  simp [layerNorm, layerVariance, layerMean, value]

example : layerVariance (![2, -2] : Fin 2 → ℝ) = 4 := by
  norm_num [layerVariance, layerMean, Fin.sum_univ_two]

example : layerNorm 5 (![-3, 2] : Fin 2 → ℝ) (![7, -1]) (![2, -2]) 0 = 5 := by
  norm_num [layerNorm, layerVariance, layerMean, Fin.sum_univ_two]

example : value (layerNormPair 5 (![-3, 2] : Fin 2 → ℝ) (![7, -1])
    (![(3, 1), (1, 3)]) 0) = 5 := by
  rw [layerNormPair_exact 5 (by norm_num)]
  norm_num [layerNorm, layerVariance, layerMean, Fin.sum_univ_two, value]

example : value (layerNormPair 1 (![-3, 2] : Fin 2 → ℝ) (![7, -1])
    (![(5, 1), (7, 3)]) 1) = -1 := by
  rw [layerNormPair_exact 1 (by norm_num)]
  norm_num [layerNorm, layerVariance, layerMean, Fin.sum_univ_two, value]

example {d : ℕ} (ε : ℝ) (hε : 0 < ε) (v : Fin d → ℝ) :
    Real.sqrt (ε + layerVariance v) ≠ 0 := by
  apply ne_of_gt
  apply Real.sqrt_pos.2
  exact add_pos_of_pos_of_nonneg hε (layerVariance_nonnegative v)

example : Regular (univ : Set ℝ)
    (fun _x => layerNormPair 1 (fun _ : Fin 1 => -3) (fun _ => 7)
      (fun _ => constPair 4) 0) := by
  apply layerNormPair_regular univ convex_univ 1 (by norm_num)
  intro i
  exact Regular.const convex_univ 4

-- The regularity conclusion exposes actual convexity, order, and range properties.
example {d : ℕ} (s : Set ℝ) (hs : Convex ℝ s) (ε : ℝ) (hε : 0 < ε)
    (γ β : Fin d → ℝ) (f : Fin d → ℝ → ℝ × ℝ)
    (hf : ∀ i, Regular s (f i)) (i : Fin d) :
    ConvexOn ℝ s (fun x => (layerNormPair ε γ β (fun j => f j x) i).1) ∧
    ConvexOn ℝ s (fun x => (layerNormPair ε γ β (fun j => f j x) i).2) ∧
    MonotoneOn (fun x => layerNormPair ε γ β (fun j => f j x) i) s ∧
    (∀ x ∈ s, 0 ≤ layerNormPair ε γ β (fun j => f j x) i) := by
  have h := layerNormPair_regular s hs ε hε γ β f hf i
  exact ⟨h.convex_fst, h.convex_snd, h.monotone, h.nonnegative⟩
