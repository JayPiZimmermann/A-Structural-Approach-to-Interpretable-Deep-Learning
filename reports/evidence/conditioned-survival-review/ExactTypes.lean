import Thesis.ConditionedSurvival
set_option pp.universes true
set_option pp.explicit true
set_option autoImplicit false
open scoped BigOperators
section
open Thesis.Games Thesis.ConditionedSurvival
example : (∀ {S : Type} [Fintype S] (n : ℕ) (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ) (hK : ∀ i s t, 0 ≤ K i s t) (hh : ∀ i s, 0 ≤ h i s) (hrec : ∀ i < n, ∀ s, h i s = ∑ t, K i s t * h (i+1) t) (s : S) (path : Paths S n), pathLaw n (kernel K h) s path * h 0 s = pathLaw n K s path * h n (endpoint n s path)) := @Thesis.ConditionedSurvival.weighted_path_identity
#check @Thesis.ConditionedSurvival.weighted_path_identity
#print axioms Thesis.ConditionedSurvival.weighted_path_identity
end
section
open Thesis.Games Thesis.ConditionedSurvival
example : (∀ {S : Type} (n : ℕ) (K : ℕ → S → S → ℝ) (h : ℕ → S → ℝ) (hh : ∀ i s, 0 ≤ h i s) (s : S) (hs : 0 < h 0 s) (path : Paths S n) (i : ℕ) (hi : i ≤ n) (hz : h i (stateAt n s path i) = 0), pathLaw n (kernel K h) s path = 0) := @Thesis.ConditionedSurvival.path_zero_at_zero_potential
#check @Thesis.ConditionedSurvival.path_zero_at_zero_potential
#print axioms Thesis.ConditionedSurvival.path_zero_at_zero_potential
end
section
open Thesis.Games Thesis.ConditionedSurvival
example : (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ) (i : ℕ) (hi : i < N) (s : S), survival N K i s = ∑ t, K i s t * survival N K (i+1) t) := @Thesis.ConditionedSurvival.survival_recurrence
#check @Thesis.ConditionedSurvival.survival_recurrence
#print axioms Thesis.ConditionedSurvival.survival_recurrence
end
section
open Thesis.Games Thesis.ConditionedSurvival
example : (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ) (s : S), survival N K 0 s = ∑ path : Paths S N, pathLaw N K s path) := @Thesis.ConditionedSurvival.survival_eq_path_mass
#check @Thesis.ConditionedSurvival.survival_eq_path_mass
#print axioms Thesis.ConditionedSurvival.survival_eq_path_mass
end
section
open Thesis.Games Thesis.ConditionedSurvival
example : (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ) (hK : ∀ i s t, 0 ≤ K i s t) (s : S) (hs : survival N K 0 s = 0) (path : Paths S N), pathLaw N K s path = 0) := @Thesis.ConditionedSurvival.survival_zero_path
#check @Thesis.ConditionedSurvival.survival_zero_path
#print axioms Thesis.ConditionedSurvival.survival_zero_path
end
section
open Thesis.Games Thesis.ConditionedSurvival
example : (∀ {S : Type} [Fintype S] (N : ℕ) (K : ℕ → S → S → ℝ) (hK : ∀ i s t, 0 ≤ K i s t) (hrow : ∀ i s, ∑ t, K i s t ≤ 1) (s : S) (hs : 0 < survival N K 0 s), (∀ i t, 0 ≤ survival N K i t ∧ survival N K i t ≤ 1) ∧ (∀ t, survival N K N t = 1) ∧ (∀ i < N, ∀ u, survival N K i u = ∑ t, K i u t * survival N K (i+1) t) ∧ (survival N K 0 s = ∑ path : Paths S N, pathLaw N K s path) ∧ (∀ i < N, ∀ u, (∑ t, kernel K (survival N K) i u t) = if 0 < survival N K i u then 1 else 0) ∧ (∀ i u t, survival N K (i+1) t = 0 → kernel K (survival N K) i u t = 0) ∧ (∀ path : Paths S N, pathLaw N (kernel K (survival N K)) s path = pathLaw N K s path / survival N K 0 s) ∧ ((∑ path : Paths S N, pathLaw N (kernel K (survival N K)) s path) = 1) ∧ (∀ (path : Paths S N) (i : ℕ), i ≤ N → survival N K i (stateAt N s path i) = 0 → pathLaw N (kernel K (survival N K)) s path = 0)) := @Thesis.ConditionedSurvival.conditioned_survival
#check @Thesis.ConditionedSurvival.conditioned_survival
#print axioms Thesis.ConditionedSurvival.conditioned_survival
end
