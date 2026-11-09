import Thesis.SoftplusCircuitOccupation

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.StoppingDAG
open scoped BigOperators

def graftPlan {d m n} (pre : Circuit d m) (prePlan : Plan pre) :
    (suffix : Circuit m n) → Plan suffix → Plan (graft pre suffix)
  | .inputs, _ => prePlan
  | .node prior _, plan => (graftPlan pre prePlan prior plan.1,plan.2)

/-- A literal shared-graph cut preserves every earlier node index and annotation. -/
theorem graft_soft {d m n} (pre : Circuit d m) (prePlan : Plan pre)
    (suffix : Circuit m n) (suffixPlan : Plan suffix) (θ : ℝ) (x : Vec d) :
    graphSoft θ (graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) x=
      graphSoft θ suffix suffixPlan (graphSoft θ pre prePlan x) := by
  induction suffix with
  | inputs => rfl
  | node prior op ih =>
      have hh := ih suffixPlan.1
      simp only [graphSoft] at hh
      simp only [graft,graftPlan,graphSoft,graphWith,hh]

theorem graft_regular {d m n} (pre : Circuit d m) (prePlan : Plan pre)
    (suffix : Circuit m n) (suffixPlan : Plan suffix) (θ : ℝ) (x : Vec d) :
    Regular θ (graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) x ↔
      Regular θ pre prePlan x ∧ Regular θ suffix suffixPlan (graphSoft θ pre prePlan x) := by
  induction suffix with
  | inputs => simp [graft,graftPlan,Regular]
  | node prior op ih => simp [graft,graftPlan,Regular,ih,graft_soft,and_assoc]

theorem graph_derivative_occupation_signed {d n} (c : Circuit d n) (plan : Plan c)
    (θ : ℝ) (hθ : 0<θ) (x : Vec d) (hx : Regular θ c plan x)
    (j : Fin n) (i : Fin d) (q : Bool) :
    (fderiv ℝ (graphSoft θ c plan) x (Pi.single i 1)) j =
      (if q then (-1 : ℝ) else 1)*
        (occupation c plan θ x j q i false-occupation c plan θ x j q i true) := by
  rw [graph_derivative_occupation c plan θ hθ x hx]
  simp only [occupation_eq_kernel]
  cases q <;> simp <;> ring

/-- The ordinary derivative with respect to an actual intermediate graph state,
evaluated at its genuine shared-prefix forward value. -/
theorem cut_derivative_occupation {d m n} (pre : Circuit d m) (prePlan : Plan pre)
    (suffix : Circuit m n) (suffixPlan : Plan suffix) (θ : ℝ) (hθ : 0<θ) (x : Vec d)
    (hx : Regular θ (graft pre suffix) (graftPlan pre prePlan suffix suffixPlan) x)
    (j : Fin n) (i : Fin m) (q : Bool) :
    (fderiv ℝ (graphSoft θ suffix suffixPlan) (graphSoft θ pre prePlan x) (Pi.single i 1)) j =
      (if q then (-1 : ℝ) else 1)*
        (occupation suffix suffixPlan θ (graphSoft θ pre prePlan x) j q i false-
         occupation suffix suffixPlan θ (graphSoft θ pre prePlan x) j q i true) :=
  graph_derivative_occupation_signed suffix suffixPlan θ hθ _
    ((graft_regular pre prePlan suffix suffixPlan θ x).mp hx).2 j i q

end Thesis.SoftplusCircuit
