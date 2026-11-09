import Thesis.AttentionReference
noncomputable section
open Thesis.AttentionReference Thesis.RoutingExtended Finset
open scoped BigOperators

-- Zero reference makes a positively used action impossible, despite its
-- positive contribution. The other zero-policy term contributes nothing.
example : objective (![0,1] : Fin 2 → ℝ) (![7,1] : Fin 2 → ℝ) (Thesis.RoutingExtended.pure 0)=⊥ := by
  have h : ¬Supported (Thesis.RoutingExtended.pure (0 : Fin 2)) (![0,1] : Fin 2 → ℝ) := by
    intro h
    have bad:=h 0 (by norm_num [Thesis.RoutingExtended.pure])
    norm_num at bad
  simp [objective,h]
example : objective (![0,1] : Fin 2 → ℝ) (![7,1] : Fin 2 → ℝ) (Thesis.RoutingExtended.pure 1)=(0 : WithBot ℝ) := by
  have hr : Supported (Thesis.RoutingExtended.pure (1 : Fin 2)) (![0,1] : Fin 2 → ℝ) := by
    intro i hi
    fin_cases i <;> norm_num [Thesis.RoutingExtended.pure] at *
  have hc : Supported (Thesis.RoutingExtended.pure (1 : Fin 2)) (![7,1] : Fin 2 → ℝ) := by
    intro i hi
    fin_cases i <;> norm_num
  simp only [objective,hr,hc,and_self,ite_true]
  norm_num [Thesis.ReferencePolicy.kl,Thesis.RoutingExtended.pure,Fin.sum_univ_two]

-- A zero contribution is independently impossible even at positive reference.
example : objective (![1/2,1/2] : Fin 2 → ℝ) (![0,2] : Fin 2 → ℝ) (Thesis.RoutingExtended.pure 0)=⊥ := by
  have h : ¬Supported (Thesis.RoutingExtended.pure (0 : Fin 2)) (![0,2] : Fin 2 → ℝ) := by
    intro h
    have bad:=h 0 (by norm_num [Thesis.RoutingExtended.pure])
    norm_num at bad
  simp [objective,h]

-- Disjoint nonzero supports have zero total mass, and every policy is bottom.
example (p : Policy (Fin 2)) : objective (![1,0] : Fin 2 → ℝ) (![0,3] : Fin 2 → ℝ) p=⊥ := by
  apply zero_mass_value
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]

-- A positive-total boundary optimum assigns zero to the zero-reference action.
example : (valuePolicy (![0,1] : Fin 2 → ℝ) (![7,1] : Fin 2 → ℝ)
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by norm_num [mass,Fin.sum_univ_two])).prob 0=0 := by
  norm_num [valuePolicy,normalized,mass,Fin.sum_univ_two]

-- Both nonzero support entries: literal ratio, no supplied optimizer hypothesis.
example : (valuePolicy (![1/4,3/4] : Fin 2 → ℝ) (![2,4] : Fin 2 → ℝ)
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num)
    (by norm_num [mass,Fin.sum_univ_two])).prob 0=1/7 := by
  norm_num [valuePolicy,normalized,mass,Fin.sum_univ_two]

-- An empty action space cannot carry a normalized Policy; positive-total
-- optimizer existence is therefore never smuggled in through an empty simplex.
example : ¬Nonempty (Policy (Fin 0)) := by
  rintro ⟨p⟩
  have h:=p.normalized
  simp at h
end
