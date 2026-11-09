import Thesis.ConditionedTrajectory

noncomputable section
set_option autoImplicit false
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators

namespace ConditionedTrajectoryBoundary

/-- Both ordinary first-step states have mass one half. Only false survives
in A, while only true survives in B. Dead states are reachable before conditioning. -/
def A (i : ℕ) (s t : Bool) : ℝ :=
  if i=0 then 1/2 else if i=1 ∧ s=false ∧ t=false then 1 else 0

def B (i : ℕ) (s t : Bool) : ℝ :=
  if i=0 then 1/2 else if i=1 ∧ s=true ∧ t=true then 1 else 0

theorem A_nonnegative : ∀ i s t,0≤A i s t := by
  intro i s t; unfold A; split_ifs <;> norm_num

theorem B_nonnegative : ∀ i s t,0≤B i s t := by
  intro i s t; unfold B; split_ifs <;> norm_num

theorem A_substochastic : ∀ i s,∑ t,A i s t≤1 := by
  intro i s; cases s <;> simp only [Fintype.sum_bool,A]
  all_goals split_ifs <;> norm_num at *

theorem B_substochastic : ∀ i s,∑ t,B i s t≤1 := by
  intro i s; cases s <;> simp only [Fintype.sum_bool,B]
  all_goals split_ifs <;> norm_num at *

theorem initial_survival : survival 2 A 0 false=1/2 ∧ survival 2 B 0 false=1/2 := by
  norm_num [survival,backwardDP,A,B,Fintype.sum_bool,Paths,Finset.filter_insert,Finset.filter_singleton]

theorem dead_but_reachable : prefixMass 1 A false true=1/2 ∧ survival 2 A 1 true=0 ∧
    prefixMass 1 B false false=1/2 ∧ survival 2 B 1 false=0 := by
  norm_num [prefixMass_succ,prefixMass_zero,survival,backwardDP,A,B,
    Fintype.sum_prod_type,Fintype.sum_bool,Paths,Finset.filter_insert,Finset.filter_singleton]

/-- The theorem consumes strictly positive initial survival only: both models
have a positive original prefix mass at an intermediate zero-survival state. -/
theorem conditioned_dead_marginals :
    timeMass 2 1 (kernel A (survival 2 A)) false true=0 ∧
    timeMass 2 1 (kernel B (survival 2 B)) false false=0 := by
  have ha : 0<survival 2 A 0 false := by rw [initial_survival.1]; norm_num
  have hb : 0<survival 2 B 0 false := by rw [initial_survival.2]; norm_num
  have h := conditioned_survival_statistics 2 A B A_nonnegative B_nonnegative
    A_substochastic B_substochastic false ha hb
  have hA := (h.2.1 1 (by omega) true).1
  have hB := (h.2.1 1 (by omega) false).2
  rw [dead_but_reachable.2.1,mul_zero,zero_div] at hA
  rw [dead_but_reachable.2.2.2,mul_zero,zero_div] at hB
  exact ⟨hA,hB⟩

theorem original_overlap_zero : ordinaryOverlap 2 A B false=0 := by
  norm_num [ordinaryOverlap,backwardDP,A,B,Fintype.sum_bool,Paths,Finset.filter_insert,Finset.filter_singleton]

/-- Different conditioned supports give maximal Hellinger separation. This uses
the composed theorem, with BC computed from the original surviving sublaws. -/
theorem disjoint_conditioned_statistics :
    overlap (pathLaw 2 (kernel A (survival 2 A)) false)
      (pathLaw 2 (kernel B (survival 2 B)) false)=0 ∧
    (1/2 : ℝ)*(∑ path : Paths Bool 2,
      (Real.sqrt (pathLaw 2 (kernel A (survival 2 A)) false path)-
       Real.sqrt (pathLaw 2 (kernel B (survival 2 B)) false path))^2)=1 := by
  have ha : 0<survival 2 A 0 false := by rw [initial_survival.1]; norm_num
  have hb : 0<survival 2 B 0 false := by rw [initial_survival.2]; norm_num
  have h := conditioned_survival_statistics 2 A B A_nonnegative B_nonnegative
    A_substochastic B_substochastic false ha hb
  have ho := h.2.2.2.2.2.1
  have hh := h.2.2.2.2.2.2
  rw [original_overlap_zero,zero_div] at ho hh
  exact ⟨ho,by simpa using hh⟩

/-- Direct path enumeration independently confirms that the two actual
conditioned laws have disjoint support, each with total mass one. -/
theorem conditioned_paths_direct :
    pathLaw 2 (kernel A (survival 2 A)) false (false,false,())=1 ∧
    pathLaw 2 (kernel A (survival 2 A)) false (true,true,())=0 ∧
    pathLaw 2 (kernel B (survival 2 B)) false (false,false,())=0 ∧
    pathLaw 2 (kernel B (survival 2 B)) false (true,true,())=1 := by
  norm_num [kernel,survival,backwardDP,pathLaw,A,B,Fintype.sum_bool,Paths,Finset.filter_insert,Finset.filter_singleton]

/-- At horizon zero the actual path law is the singleton law, so no survival
positivity restriction has accidentally excluded the terminal boundary. -/
example : timeMass 0 0 (kernel A (survival 0 A)) false false=1 ∧
    overlap (pathLaw 0 (kernel A (survival 0 A)) false)
      (pathLaw 0 (kernel B (survival 0 B)) false)=1 := by
  constructor
  · rw [timeMass_zero]
    norm_num [survival,backwardDP]
  · change (∑ _ : Unit,Real.sqrt ((1 : ℝ)*1))=1
    norm_num

/-- A dead row is kept in the common state space; it is not falsely made
stochastic. The guarded geometric formula has a genuine zero denominator. -/
example : (∑ t : Bool,kernel A (survival 2 A) 1 true t)=0 ∧
    Real.sqrt (kernel A (survival 2 A) 1 true true *
      kernel B (survival 2 B) 1 true true)=0 := by
  norm_num [kernel,survival,backwardDP,A,B,Fintype.sum_bool,Paths,Finset.filter_insert,Finset.filter_singleton]

/-- Positive initial survival is necessary: the all-dead ordinary sublaw cannot
be normalized into a conditional probability law. -/
example : survival 1 (fun (_ : ℕ) (_ _ : Bool) => (0 : ℝ)) 0 false=0 ∧
    (∑ path : Paths Bool 1,pathLaw 1
      (kernel (fun (_ : ℕ) (_ _ : Bool) => (0 : ℝ))
        (survival 1 (fun (_ : ℕ) (_ _ : Bool) => (0 : ℝ)))) false path)=0 := by
  norm_num [survival,backwardDP,kernel,pathLaw,Fintype.sum_prod_type,Fintype.sum_bool,Paths,Finset.filter_insert,Finset.filter_singleton]

end ConditionedTrajectoryBoundary
