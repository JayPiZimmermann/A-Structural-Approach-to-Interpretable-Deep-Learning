import Thesis.LayeredGames
import Thesis.SupportDerivatives
import Mathlib.Tactic.FinCases

noncomputable section
namespace AdversarialFoundations
open Thesis.LayeredGames Thesis.Tropical Matrix

def tiedGame : Game Unit Bool where
  maximize := fun _ _ => true
  reward := fun _ _ _ => 0
  discount := fun _ _ => 0
  transition := fun _ _ _ _ => 1
  terminal := fun _ => 0
  discount_nonneg := by intros; exact le_rfl
  transition_nonneg := by intros; norm_num
  transition_sum := by intros; simp

def chooseFalse : Policy Unit Bool := purePolicy (fun _ _ => false)
def chooseTrue : Policy Unit Bool := purePolicy (fun _ _ => true)

theorem distinct_pure_policies : chooseFalse ≠ chooseTrue := by
  intro h
  have he := congrArg (fun p : Policy Unit Bool => p.prob 0 () false) h
  norm_num [chooseFalse, chooseTrue, purePolicy] at he

theorem every_policy_is_optimal (p q : Policy Unit Bool) (n : ℕ) (s : Unit) :
    tiedGame.payoff p q n s = tiedGame.value n s := by
  cases n with
  | zero => rfl
  | succ n => simp [Game.payoff, Game.value, Game.action, tiedGame, best]

theorem gated_output_changes_affine_logit :
    max (0 * (1 : ℝ) + 1 * 0) (1 * 1 + 0 * 0) - (1 * 1 + 0 * 0) ≠ -(1 : ℝ) := by
  norm_num

theorem halfline_has_no_finite_support_at_one :
    ¬ ∃ b : ℝ, ∀ p : ℝ, 0 ≤ p → p * 1 ≤ b := by
  rintro ⟨b, hb⟩
  have h := hb (max b 0 + 1) (by have := le_max_right b 0; linarith)
  have := le_max_left b 0
  linarith

def triangle : Fin 3 → Fin 2 → ℝ := ![![0,1], ![2,1], ![1,0]]

theorem lower_vertex_exposed :
    ∀ a, triangle a ≠ triangle 2 → triangle a ⬝ᵥ ![0,-1] < triangle 2 ⬝ᵥ ![0,-1] := by
  intro a ha
  fin_cases a <;> norm_num [triangle, dotProduct, Fin.sum_univ_succ] at *

theorem lower_vertex_is_extreme :
    triangle 2 ∈ (convexHull ℝ (Set.range triangle)).extremePoints ℝ := by
  apply (vertices_eq_attainable_gradients triangle (triangle 2)).mpr
  exact ⟨![0,-1], unique_generator_hasFDerivAt triangle ![0,-1] (triangle 2)
    ⟨2,rfl⟩ lower_vertex_exposed⟩

theorem lower_vertex_never_maximizes_on_affine_slice (x : ℝ) :
    x < max 1 (2*x+1) := by
  rcases le_total x 0 with h | h
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

theorem lower_vertex_below_support_on_slice (x : ℝ) :
    triangle 2 ⬝ᵥ ![x,1] < support (convexHull ℝ (Set.range triangle)) ![x,1] := by
  rw [support_convexHull]
  have h0 : (1 : ℝ) ≤ finiteMax (fun a => triangle a ⬝ᵥ ![x,1]) := by
    simpa [triangle, dotProduct, Fin.sum_univ_succ] using
      le_finiteMax (fun a => triangle a ⬝ᵥ ![x,1]) (0 : Fin 3)
  have h1 : 2*x+1 ≤ finiteMax (fun a => triangle a ⬝ᵥ ![x,1]) := by
    simpa [triangle, dotProduct, Fin.sum_univ_succ] using
      le_finiteMax (fun a => triangle a ⬝ᵥ ![x,1]) (1 : Fin 3)
  have h := lt_of_lt_of_le (lower_vertex_never_maximizes_on_affine_slice x) (max_le h0 h1)
  simpa [triangle, dotProduct, Fin.sum_univ_succ] using h

#print axioms distinct_pure_policies
#print axioms every_policy_is_optimal
#print axioms gated_output_changes_affine_logit
#print axioms halfline_has_no_finite_support_at_one
#print axioms lower_vertex_is_extreme
#print axioms lower_vertex_never_maximizes_on_affine_slice
#print axioms lower_vertex_below_support_on_slice
end AdversarialFoundations
