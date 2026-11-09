import HiddenMonotonicity.MultivariateMonotoneDCLift

open HiddenMonotonicity.SoftmaxDC
open scoped BigOperators

universe u

example : ∀ {ι : Type u} (f : (ι → ℝ) → ℝ),
    (∀ a v : ι → ℝ,
      ConvexOn ℝ Set.univ (fun t : ℝ => f (fun j => a j + t * v j))) →
    ConvexOn ℝ Set.univ f := @convex_from_affine_lines

example : ∀ {ι : Type u} (f : (ι → ℝ) → ℝ)
    (D : (ι → ℝ) → (ι → ℝ) → ℝ),
    (∀ (a v : ι → ℝ) (t : ℝ),
      HasDerivAt (fun s : ℝ => f (fun j => a j + s * v j))
        (D (fun j => a j + t * v j) v) t) →
    (∀ z v : ι → ℝ, (∀ j, 0 ≤ v j) → 0 ≤ D z v) →
    Monotone f := @monotone_from_affine_line_deriv

example : ∀ {ι : Type u} [Fintype ι] (P : (ι → ℝ) → ℝ) (L c : ℝ),
    ConvexOn ℝ Set.univ P →
    ConvexOn ℝ Set.univ (multivariateLift P L c) := @multivariateLift_convex

example : ∀ {ι : Type u} [Fintype ι] (P : (ι → ℝ) → ℝ) (L c : ℝ),
    Monotone P →
    Monotone (fun x : ι → ℝ => L * (∑ j, x j) - P x) →
    Monotone (multivariateLift P L c) := @multivariateLift_monotone

example : ∀ {ι : Type u} [Fintype ι] (P Q f : (ι → ℝ) → ℝ) (L c : ℝ),
    (∀ x, P x - Q x = f x) → ∀ z : (ι → ℝ) × (ι → ℝ),
    multivariateLift P L c z - multivariateLift Q L c z = f (z.1 - z.2) :=
  @multivariateLift_difference

example : ∀ {ι : Type u} [Fintype ι] (P : (ι → ℝ) → ℝ) (L c : ℝ),
    Monotone (multivariateLift P L c) → c ≤ P 0 →
    ∀ z : (ι → ℝ) × (ι → ℝ), 0 ≤ z → 0 ≤ multivariateLift P L c z :=
  @multivariateLift_nonnegative

example : Monotone (multivariateLift (fun _ : Fin 2 → ℝ => 0) 0 0) := by
  apply multivariateLift_monotone
  · intro x y hxy
    rfl
  · intro x y hxy
    simp

example (P : (Fin 0 → ℝ) → ℝ) (L c : ℝ) (z : (Fin 0 → ℝ) × (Fin 0 → ℝ)) :
    multivariateLift P L c z = P 0 - c := by
  have he : z.1 - z.2 = 0 := by ext j; exact Fin.elim0 j
  simp [multivariateLift, he]

#print axioms convex_from_affine_lines
#print axioms monotone_from_affine_line_deriv
#print axioms multivariateLift_convex
#print axioms multivariateLift_monotone
#print axioms multivariateLift_difference
#print axioms multivariateLift_nonnegative
