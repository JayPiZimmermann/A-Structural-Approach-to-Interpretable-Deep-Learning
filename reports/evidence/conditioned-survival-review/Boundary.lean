import Thesis.ConditionedSurvival
noncomputable section
open Thesis.ConditionedSurvival Thesis.Games
open scoped BigOperators

def demoK (i : ℕ) (s t : Fin 2) : ℝ :=
  if i=0 then (if s=0 then 1/2 else if t=1 then 1 else 0)
  else if i=1 then (if s=0 ∧ t=0 then 1 else 0) else 0

theorem demoK_nonneg : ∀ i s t,0≤demoK i s t := by
  intro i s t
  unfold demoK
  split_ifs <;> norm_num

example : survival 2 demoK 0 0=1/2 := by
  dsimp [survival,backwardDP]
  simp only [Fin.sum_univ_two]
  norm_num [demoK]
example : survival 2 demoK 1 1=0 := by
  dsimp [survival,backwardDP]
  simp only [Fin.sum_univ_two]
  norm_num [demoK]
example : demoK 0 0 1=1/2 ∧ kernel demoK (survival 2 demoK) 0 0 1=0 := by
  dsimp [kernel,survival,backwardDP]
  simp only [Fin.sum_univ_two]
  norm_num [demoK]
example : kernel demoK (survival 2 demoK) 0 0 0=1 := by
  dsimp [kernel,survival,backwardDP]
  simp only [Fin.sum_univ_two]
  norm_num [demoK]
example : ¬∀ i s,0<survival 2 demoK i s := by
  intro h
  have bad:=h 1 1
  dsimp [survival,backwardDP] at bad
  simp only [Fin.sum_univ_two] at bad
  norm_num [demoK] at bad
example : (∑ path : Paths (Fin 2) 2,pathLaw 2 (kernel demoK (survival 2 demoK)) 0 path)=1 := by
  apply survival_conditioned_normalized 2 demoK demoK_nonneg 0
  dsimp [survival,backwardDP]
  simp only [Fin.sum_univ_two]
  norm_num [demoK]

-- Zero initial survival does not silently produce a probability law.
example : survival 2 demoK 0 1=0 := by
  dsimp [survival,backwardDP]
  simp only [Fin.sum_univ_two]
  norm_num [demoK]
example (path : Paths (Fin 2) 2) : pathLaw 2 demoK 1 path=0 := by
  apply survival_zero_path 2 demoK demoK_nonneg 1
  dsimp [survival,backwardDP]
  simp only [Fin.sum_univ_two]
  norm_num [demoK]
example : (∑ t : Fin 2,kernel demoK (survival 2 demoK) 0 1 t)=0 := by
  dsimp [kernel,survival,backwardDP]
  simp only [Fin.sum_univ_two]
  norm_num [demoK]

-- Empty horizon is a genuine unit-mass empty path with survival one.
example (K : ℕ → Fin 1 → Fin 1 → ℝ) : survival 0 K 0 0=1 := survival_terminal 0 K 0
example (K : ℕ → Fin 1 → Fin 1 → ℝ) :
    (∑ path : Paths (Fin 1) 0,pathLaw 0 (kernel K (survival 0 K)) 0 path)=1 := by
  change (∑ _ : Unit,(1 : ℝ))=1
  simp
end
