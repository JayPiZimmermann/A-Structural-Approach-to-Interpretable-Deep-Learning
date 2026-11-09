import Thesis.AttentionReference
set_option pp.universes true
set_option pp.explicit true
set_option autoImplicit false
open scoped BigOperators
section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
example : (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (p : Policy A) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i), objective reference contribution p = sourceValue 1 (mass reference contribution) p) := @Thesis.AttentionReference.objective_eq_sourceValue
#check @Thesis.AttentionReference.objective_eq_sourceValue
#print axioms Thesis.AttentionReference.objective_eq_sourceValue
end
section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
example : (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) (hz : 0 < ∑ i, mass reference contribution i), objective reference contribution (valuePolicy reference contribution hr hc hz) = (Real.log (∑ i, reference i * contribution i) : WithBot ℝ)) := @Thesis.AttentionReference.valuePolicy_value
#check @Thesis.AttentionReference.valuePolicy_value
#print axioms Thesis.AttentionReference.valuePolicy_value
end
section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
example : (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (p : Policy A) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) (hz : 0 < ∑ i, mass reference contribution i), objective reference contribution p = (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ↔ p.prob = (valuePolicy reference contribution hr hc hz).prob) := @Thesis.AttentionReference.valuePolicy_unique
#check @Thesis.AttentionReference.valuePolicy_unique
#print axioms Thesis.AttentionReference.valuePolicy_unique
end
section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
example : (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (p : Policy A) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) (hz : (∑ i, reference i * contribution i) = 0), objective reference contribution p = ⊥) := @Thesis.AttentionReference.zero_mass_value
#check @Thesis.AttentionReference.zero_mass_value
#print axioms Thesis.AttentionReference.zero_mass_value
end
section
universe u
open Finset Thesis.RoutingExtended Thesis.AttentionReference
example : (∀ {A : Type u} [Fintype A] (reference contribution : A → ℝ) (hr : ∀ i, 0 ≤ reference i) (hc : ∀ i, 0 ≤ contribution i) (hz : 0 < ∑ i, mass reference contribution i), IsGreatest (Set.range (objective reference contribution)) (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ∧ (∀ p : Policy A, objective reference contribution p = (Real.log (∑ i, reference i * contribution i) : WithBot ℝ) ↔ p.prob = (valuePolicy reference contribution hr hc hz).prob) ∧ (∀ i, (valuePolicy reference contribution hr hc hz).prob i = reference i * contribution i / ∑ j, reference j * contribution j)) := @Thesis.AttentionReference.attention_value_routing
#check @Thesis.AttentionReference.attention_value_routing
#print axioms Thesis.AttentionReference.attention_value_routing
end
