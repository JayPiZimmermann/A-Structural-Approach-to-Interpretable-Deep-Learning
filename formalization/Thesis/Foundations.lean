import HiddenMonotonicity.Decomposition
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Finset.Lattice.Fold

/-! Structural foundations using the same varying-width `Network` as the
split forward pass and backward identities. -/
noncomputable section
namespace Thesis.Foundations
open Finset Matrix HiddenMonotonicity

/-- Jensen convexity on the whole vector space, coordinate by coordinate. -/
def Jensen {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  ∀ x y t, 0 ≤ t → t ≤ 1 → f (mix t x y) ≤ mix t (f x) (f y)

def ScalarConvex (σ : ℝ → ℝ) : Prop :=
  ∀ x y t, 0 ≤ t → t ≤ 1 → σ (t*x+(1-t)*y) ≤ t*σ x+(1-t)*σ y

/-- Local notation for the shared evaluator, with activation written first. -/
abbrev evalWith {n m} (σ : ℝ → ℝ) (net : Network n m) := net.forwardWith σ

theorem evalWith_relu {n m} (net : Network n m) : evalWith relu net = net.eval :=
  net.forwardWith_relu

/-- Nonnegative actual weights, rather than merely nonnegative split parts. -/
def PositiveWeights {n m} : Network n m → Prop
  | .output _ => True
  | .layer wp wn _ _ tail => (∀ i j, 0 ≤ (wp-wn) i j) ∧ PositiveWeights tail

/-- First-layer weights unrestricted; all subsequent weights are nonnegative. -/
def InputConvexWeights {n m} : Network n m → Prop
  | .output _ => True
  | .layer _ _ _ _ tail => PositiveWeights tail

theorem affine_mix {n m} (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x y : Fin n → ℝ) (t : ℝ) :
    W.mulVec (mix t x y) + b = mix t (W.mulVec x+b) (W.mulVec y+b) := by
  simp only [mix, mulVec_add, mulVec_smul]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Proposition prop:monotone_represents for the full varying-width backbone. -/
theorem monotone_network {n m} (net : Network n m) (σ : ℝ → ℝ)
    (h : PositiveWeights net) (hσ : Monotone σ) : Monotone (evalWith σ net) := by
  induction net with
  | output n => exact monotone_id
  | layer wp wn bp bn tail ih =>
      intro x y hxy
      apply ih h.2
      intro i
      exact hσ (add_le_add (positive_matrix_monotone (wp-wn) h.1 hxy i) (le_refl ((bp-bn) i)))

theorem activation_jensen {n k} (W : Matrix (Fin k) (Fin n) ℝ)
    (b : Fin k → ℝ) (σ : ℝ → ℝ) (hσ : ScalarConvex σ) :
    Jensen (fun x => fun i => σ ((W.mulVec x+b) i)) := by
  intro x y t ht ht'
  dsimp only
  rw [affine_mix]
  intro i
  exact hσ _ _ t ht ht'

theorem jensen_comp {n k m} (f : (Fin n → ℝ) → (Fin k → ℝ))
    (g : (Fin k → ℝ) → (Fin m → ℝ)) (hf : Jensen f) (hg : Jensen g)
    (hm : Monotone g) : Jensen (g ∘ f) := by
  intro x y t ht ht'
  exact (hm (hf x y t ht ht')).trans (hg (f x) (f y) t ht ht')

theorem positive_network_jensen {n m} (net : Network n m) (σ : ℝ → ℝ)
    (h : PositiveWeights net) (hm : Monotone σ) (hc : ScalarConvex σ) :
    Jensen (evalWith σ net) := by
  induction net with
  | output n => intro x y t _ _; exact le_rfl
  | layer wp wn bp bn tail ih =>
      exact jensen_comp _ _ (activation_jensen (wp-wn) (bp-bn) σ hc) (ih h.2)
        (monotone_network tail σ h.2 hm)

/-- Proposition prop:icnn_convex: the first weight matrix is unconstrained. -/
theorem icnn_jensen {n m} (net : Network n m) (σ : ℝ → ℝ)
    (h : InputConvexWeights net) (hm : Monotone σ) (hc : ScalarConvex σ) :
    Jensen (evalWith σ net) := by
  cases net with
  | output n => intro x y t _ _; exact le_rfl
  | layer wp wn bp bn tail =>
      exact jensen_comp _ _ (activation_jensen (wp-wn) (bp-bn) σ hc)
        (positive_network_jensen tail σ h hm hc) (monotone_network tail σ h hm)

/-- Jensen convexity is precisely mathlib convexity of every output coordinate. -/
theorem jensen_iff_convexOn {n m} (f : (Fin n → ℝ) → (Fin m → ℝ)) :
    Jensen f ↔ ∀ i, ConvexOn ℝ Set.univ (fun x => f x i) := by
  constructor
  · intro h i
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hb' : b = 1-a := by linarith
    subst b
    exact h x y a ha (by linarith) i
  · intro h x y t ht ht' i
    exact (h i).2 (Set.mem_univ x) (Set.mem_univ y) ht
      (sub_nonneg.mpr ht') (by ring)

theorem icnn_convex {n m} (net : Network n m) (σ : ℝ → ℝ)
    (h : InputConvexWeights net) (hm : Monotone σ) (hc : ScalarConvex σ)
    (i : Fin m) : ConvexOn ℝ Set.univ (fun x => evalWith σ net x i) :=
  (jensen_iff_convexOn _).mp (icnn_jensen net σ h hm hc) i

/-- An affine final layer preserves convexity when its weights are nonnegative. -/
theorem icnn_affine_output {n m k} (net : Network n m) (σ : ℝ → ℝ)
    (h : InputConvexWeights net) (hm : Monotone σ) (hc : ScalarConvex σ)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ) (hW : ∀ i j, 0 ≤ W i j) :
    Jensen (fun x => W.mulVec (evalWith σ net x) + b) := by
  apply jensen_comp _ (fun z => W.mulVec z+b) (icnn_jensen net σ h hm hc)
  · intro x y t _ _; exact (affine_mix W b x y t).le
  · intro x y hxy; exact add_le_add (positive_matrix_monotone W hW hxy) (le_refl b)

theorem monotone_affine_output {n m k} (net : Network n m) (σ : ℝ → ℝ)
    (h : PositiveWeights net) (hm : Monotone σ)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ) (hW : ∀ i j, 0 ≤ W i j) :
    Monotone (fun x => W.mulVec (evalWith σ net x) + b) := by
  intro x y hxy
  exact add_le_add (positive_matrix_monotone W hW
    (monotone_network net σ h hm hxy)) (le_refl b)

theorem relu_monotone : Monotone relu := fun _ _ h => max_le_max h le_rfl

theorem relu_convex : ScalarConvex relu := by
  intro x y t ht ht'
  simpa [relu] using max_jensen x 0 y 0 t ht ht'

end Thesis.Foundations
