import Thesis.ConditionedTrajectory

noncomputable section
set_option autoImplicit false
open Thesis.Games Thesis.ConditionedSurvival Thesis.Randomization
open scoped BigOperators
namespace IndependentTrajectoryAudit

-- Initial survivals differ; both models can reach a dead intermediate state.
def A (i : ℕ) (s t : Bool) : ℝ :=
  if i=0 then 1/2 else if i=1 ∧ s=false then (if t then 2/5 else 1/10) else 0

def B (i : ℕ) (s t : Bool) : ℝ :=
  if i=0 then (if t then 1/4 else 3/4)
  else if i=1 ∧ s=false then (if t then 1/5 else 4/5) else 0

theorem posA : ∀ i s t,0≤A i s t := by
  intro i s t; unfold A; split_ifs <;> norm_num

theorem posB : ∀ i s t,0≤B i s t := by
  intro i s t; unfold B; split_ifs <;> norm_num

theorem initial : survival 2 A 0 false=1/4 ∧ survival 2 B 0 false=3/4 := by
  norm_num [survival,backwardDP,A,B,Fintype.sum_bool,Paths,
    Finset.filter_insert,Finset.filter_singleton]

theorem dead : prefixMass 1 A false true=1/2 ∧ survival 2 A 1 true=0 ∧
    prefixMass 1 B false true=1/4 ∧ survival 2 B 1 true=0 := by
  norm_num [prefixMass_succ,prefixMass_zero,survival,backwardDP,A,B,
    Fintype.sum_bool,Paths,Finset.filter_insert,Finset.filter_singleton]

-- Actual full-path marginal differs from the unrestricted original prefix mass.
example : timeMass 2 1 A false false=1/4 ∧ prefixMass 1 A false false=1/2 := by
  rw [timeMass_factorization 2 1 (by omega)]
  norm_num [prefixMass_succ,prefixMass_zero,survival,backwardDP,A,Fintype.sum_bool,
    Paths,Finset.filter_insert,Finset.filter_singleton]

-- No assumption of strict positivity at intermediate states is needed.
example : timeMass 2 1 (kernel A (survival 2 A)) false false=1 ∧
    timeMass 2 1 (kernel A (survival 2 A)) false true=0 := by
  have hp : 0<survival 2 A 0 false := by rw [initial.1]; norm_num
  constructor
  · rw [conditioned_time_marginal 2 1 (by omega) A posA false hp false,initial.1]
    norm_num [prefixMass_succ,prefixMass_zero,survival,backwardDP,A,
      Fintype.sum_bool,Paths,Finset.filter_insert,Finset.filter_singleton]
  · rw [conditioned_time_marginal 2 1 (by omega) A posA false hp true,dead.2.1]
    norm_num

-- Direct expansion, independent of the desired marginal/BC identities.
theorem actual_paths :
    pathLaw 2 (kernel A (survival 2 A)) false (false,false,())=1/5 ∧
    pathLaw 2 (kernel A (survival 2 A)) false (false,true,())=4/5 ∧
    pathLaw 2 (kernel B (survival 2 B)) false (false,false,())=4/5 ∧
    pathLaw 2 (kernel B (survival 2 B)) false (false,true,())=1/5 := by
  norm_num [kernel,survival,backwardDP,pathLaw,A,B,Fintype.sum_bool,Paths,
    Finset.filter_insert,Finset.filter_singleton]

theorem nontrivial_overlap :
    overlap (pathLaw 2 (kernel A (survival 2 A)) false)
      (pathLaw 2 (kernel B (survival 2 B)) false)=4/5 := by
  unfold overlap
  change (∑ path : Bool × (Bool × Unit),
    Real.sqrt (pathLaw 2 (kernel A (survival 2 A)) false path *
      pathLaw 2 (kernel B (survival 2 B)) false path)) = 4/5
  norm_num [kernel,survival,backwardDP,pathLaw,A,B,Fintype.sum_bool,
    Fintype.sum_prod_type,Paths,Finset.filter_insert,Finset.filter_singleton,Real.sqrt_div]

-- Test the actual Hellinger identity, with BC strictly between zero and one.
example : (1/2 : ℝ)*(∑ path : Paths Bool 2,
    (Real.sqrt (pathLaw 2 (kernel A (survival 2 A)) false path)-
    Real.sqrt (pathLaw 2 (kernel B (survival 2 B)) false path))^2)=1/5 := by
  have ha : 0<survival 2 A 0 false := by rw [initial.1]; norm_num
  have hb : 0<survival 2 B 0 false := by rw [initial.2]; norm_num
  rw [conditioned_hellinger 2 A B posA posB false ha hb,
    ←conditioned_overlap 2 A B posA posB false ha hb,nontrivial_overlap]
  norm_num

-- The positive initial-survival premise is substantive, not derivable for all rows.
example : ¬0<survival 2 A 1 true := by rw [dead.2.1]; norm_num
example : (∑ t : Bool,kernel A (survival 2 A) 1 true t)=0 := by
  simp [kernel,dead.2.1]

-- The empty path is normalized even when all future transitions vanish.
example : timeMass 0 0 (fun (_ : ℕ) (_ _ : Bool) => (0 : ℝ)) false false=1 := by
  rw [timeMass_zero]
  norm_num [survival,backwardDP]
end IndependentTrajectoryAudit
