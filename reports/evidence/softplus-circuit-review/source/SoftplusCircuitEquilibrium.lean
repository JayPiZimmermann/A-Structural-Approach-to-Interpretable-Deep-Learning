import Thesis.SoftplusCircuitLocal

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.Regularization Thesis.StoppingDAG
open scoped BigOperators

def canonicalStrategy {d n} (θ : ℝ) : (c : Circuit d n) → (plan : Plan c) → Vec d → Strategy c plan
  | .inputs, _, _ => ()
  | .node prior _, plan, x =>
      (canonicalStrategy θ prior plan.1 x,canonicalNode θ plan.2 (graphSoft θ prior plan.1 x))

def signedValue {d n} (θ : ℝ) : (c : Circuit d n) → (plan : Plan c) →
    Strategy c plan → Strategy c plan → PairVec d → PairVec n
  | .inputs, _, _, _, x => x
  | .node prior _, plan, plus, minus, x =>
      let v := signedValue θ prior plan.1 plus.1 minus.1 x
      let z := nodeSigned θ plan.2 plus.2 minus.2 v
      (Fin.snoc v.1 z.1,Fin.snoc v.2 z.2)

theorem optimal_lower {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0<θ)
    (x : Vec d) (v : PairVec d) (hx : (x,-x)≤v) (minus : Strategy c plan) :
    (graphSoft θ c plan x,-graphSoft θ c plan x)≤
      signedValue θ c plan (canonicalStrategy θ c plan x) minus v := by
  induction c with
  | inputs => exact hx
  | @node n prior op ih =>
      have hp := ih plan.1 minus.1
      have hn := (nodeSigned_lower θ hθ plan.2 (graphSoft θ prior plan.1 x) minus.2).trans
        (nodeSigned_monotone θ plan.2 _ _ hp)
      constructor <;> intro j <;> refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [graphSoft,graphWith,signedValue,canonicalStrategy,Fin.snoc_last] using hn.1
      · simpa only [graphSoft,graphWith,signedValue,canonicalStrategy,Fin.snoc_castSucc] using hp.1 i
      · simpa only [graphSoft,graphWith,signedValue,canonicalStrategy,Fin.snoc_last,Pi.neg_apply] using hn.2
      · simpa only [graphSoft,graphWith,signedValue,canonicalStrategy,Fin.snoc_castSucc,Pi.neg_apply] using hp.2 i

theorem optimal_upper {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0<θ)
    (x : Vec d) (v : PairVec d) (hx : v≤(x,-x)) (plus : Strategy c plan) :
    signedValue θ c plan plus (canonicalStrategy θ c plan x) v≤
      (graphSoft θ c plan x,-graphSoft θ c plan x) := by
  induction c with
  | inputs => exact hx
  | @node n prior op ih =>
      have hp := ih plan.1 plus.1
      have hn := (nodeSigned_monotone θ plan.2 _ _ hp).trans
        (nodeSigned_upper θ hθ plan.2 (graphSoft θ prior plan.1 x) plus.2)
      constructor <;> intro j <;> refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [graphSoft,graphWith,signedValue,canonicalStrategy,Fin.snoc_last] using hn.1
      · simpa only [graphSoft,graphWith,signedValue,canonicalStrategy,Fin.snoc_castSucc] using hp.1 i
      · simpa only [graphSoft,graphWith,signedValue,canonicalStrategy,Fin.snoc_last,Pi.neg_apply] using hn.2
      · simpa only [graphSoft,graphWith,signedValue,canonicalStrategy,Fin.snoc_castSucc,Pi.neg_apply] using hp.2 i

theorem canonical_value {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0<θ) (x : Vec d) :
    signedValue θ c plan (canonicalStrategy θ c plan x) (canonicalStrategy θ c plan x) (x,-x)=
      (graphSoft θ c plan x,-graphSoft θ c plan x) :=
  le_antisymm (optimal_upper c plan θ hθ x (x,-x) le_rfl _)
    (optimal_lower c plan θ hθ x (x,-x) le_rfl _)

/-- The canonical profile is a saddle against arbitrary randomized activation
and pooling decisions at every recorded state of the actual shared DAG. -/
theorem graph_saddle {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0<θ)
    (x : Vec d) (plus minus : Strategy c plan) :
    signedValue θ c plan plus (canonicalStrategy θ c plan x) (x,-x)≤
      (graphSoft θ c plan x,-graphSoft θ c plan x) ∧
    signedValue θ c plan (canonicalStrategy θ c plan x) (canonicalStrategy θ c plan x) (x,-x)=
      (graphSoft θ c plan x,-graphSoft θ c plan x) ∧
    (graphSoft θ c plan x,-graphSoft θ c plan x)≤
      signedValue θ c plan (canonicalStrategy θ c plan x) minus (x,-x) :=
  ⟨optimal_upper c plan θ hθ x (x,-x) le_rfl plus,canonical_value c plan θ hθ x,
    optimal_lower c plan θ hθ x (x,-x) le_rfl minus⟩

def NodeNash {n e} (θ : ℝ) (spec : NodeSpec (n := n) e)
    (plus minus : NodePolicy spec) (v : PairVec n) : Prop :=
  (∀ a : NodePolicy spec,(nodeSigned θ spec a minus v).1≤(nodeSigned θ spec plus minus v).1) ∧
  (∀ b : NodePolicy spec,(nodeSigned θ spec plus minus v).2≤(nodeSigned θ spec plus b v).2)

def SubgamePerfect {d n} (θ : ℝ) : (c : Circuit d n) → (plan : Plan c) →
    Strategy c plan → Strategy c plan → PairVec d → Prop
  | .inputs, _, _, _, _ => True
  | .node prior _, plan, plus, minus, x =>
      SubgamePerfect θ prior plan.1 plus.1 minus.1 x ∧
      NodeNash θ plan.2 plus.2 minus.2 (signedValue θ prior plan.1 plus.1 minus.1 x)

theorem canonical_node_nash {n e} (θ : ℝ) (hθ : 0<θ) (spec : NodeSpec (n := n) e) (x : Vec n) :
    NodeNash θ spec (canonicalNode θ spec x) (canonicalNode θ spec x) (x,-x) := by
  have he := le_antisymm (nodeSigned_upper θ hθ spec x (canonicalNode θ spec x))
    (nodeSigned_lower θ hθ spec x (canonicalNode θ spec x))
  constructor
  · intro a; rw [he]; exact (nodeSigned_upper θ hθ spec x a).1
  · intro b; rw [he]; exact (nodeSigned_lower θ hθ spec x b).2

/-- Full subgame-perfect existence, with source-ordered hard pool choices and
sigmoid activation policies; local optimality uses actual profile payoffs. -/
theorem canonical_spne {d n} (c : Circuit d n) (plan : Plan c) (θ : ℝ) (hθ : 0<θ) (x : Vec d) :
    SubgamePerfect θ c plan (canonicalStrategy θ c plan x) (canonicalStrategy θ c plan x) (x,-x) := by
  induction c with
  | inputs => trivial
  | node prior op ih =>
      refine ⟨ih plan.1,?_⟩
      simp only [canonicalStrategy]
      rw [canonical_value prior plan.1 θ hθ x]
      exact canonical_node_nash θ hθ plan.2 _

end Thesis.SoftplusCircuit
