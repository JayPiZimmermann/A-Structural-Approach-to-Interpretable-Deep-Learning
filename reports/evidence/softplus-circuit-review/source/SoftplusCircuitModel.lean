import Thesis.SoftplusTransitionPayoff
import Thesis.StoppingOrderedPool
import Thesis.RoutingExtended

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.Regularization Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators

/-- A source operator certificate for the EXISTING expression at a Circuit node.
The activation constructor identifies a ReLU gate explicitly; a pool containing
zero remains a hard pool rather than being accidentally smoothed. -/
inductive NodeSpec {n : ℕ} : SignedExpr (Fin n) → Type
  | affine (w : Vec n) (b : ℝ) : NodeSpec (SignedExpr.affine w b)
  | activation (w : Vec n) (b : ℝ) : NodeSpec (.maximum (SignedExpr.affine w b) (.constant 0))
  | addition (i j : Fin n) : NodeSpec (.add (.input i) (.input j))
  | pool {k : ℕ} (inputs : Fin (k+1) → Fin n) : NodeSpec (orderedInputPool inputs)

/-- Operator annotations on the existing shared graph. This is not a separate
network datatype: every annotation certifies the actual original node syntax. -/
def Plan {d n} : Circuit d n → Type
  | .inputs => Unit
  | .node prior op => Plan prior × NodeSpec op

def nodeWith {n e} (σ : ℝ → ℝ) : NodeSpec (n := n) e → Vec n → ℝ
  | .affine w b, x => (SignedExpr.affine w b).eval x
  | .activation w b, x => σ ((SignedExpr.affine w b).eval x)
  | .addition i j, x => x i+x j
  | .pool inputs, x => (orderedInputPool inputs).eval x

def graphWith {d n} (σ : ℝ → ℝ) : (c : Circuit d n) → Plan c → Vec d → Vec n
  | .inputs, _, x => x
  | .node prior _, plan, x =>
      let v := graphWith σ prior plan.1 x
      Fin.snoc v (nodeWith σ plan.2 v)

def graphSoft {d n} (θ : ℝ) (c : Circuit d n) (plan : Plan c) : Vec d → Vec n :=
  graphWith (softplus θ) c plan

theorem nodeWith_relu {n e} (spec : NodeSpec (n := n) e) (x : Vec n) :
    nodeWith relu spec x=e.eval x := by
  cases spec <;> rfl

/-- The hard interpretation is exactly the original shared Circuit, including
all residual references and the proved source-ordered finite pool expression. -/
theorem graphWith_relu {d n} (c : Circuit d n) (plan : Plan c) (x : Vec d) :
    graphWith relu c plan x=c.eval x := by
  induction c with
  | inputs => rfl
  | node prior op ih => simp only [graphWith,Circuit.eval,ih,nodeWith_relu]

def nodeSplit {n e} (θ : ℝ) : NodeSpec (n := n) e → PairVec n → ℝ × ℝ
  | .affine w b, x => stoppingExpr (SignedExpr.affine w b) x
  | .activation w b, x =>
      let z := stoppingExpr (SignedExpr.affine w b) x
      softSplit θ z.1 z.2
  | .addition i j, x => stoppingExpr (.add (.input i) (.input j)) x
  | .pool inputs, x => stoppingExpr (orderedInputPool inputs) x

def graphSplit {d n} (θ : ℝ) : (c : Circuit d n) → Plan c → PairVec d → PairVec n
  | .inputs, _, x => x
  | .node prior _, plan, x =>
      let v := graphSplit θ prior plan.1 x
      let z := nodeSplit θ plan.2 v
      (Fin.snoc v.1 z.1,Fin.snoc v.2 z.2)

theorem nodeSplit_recovery {n e} (θ : ℝ) (hθ : 0<θ) (spec : NodeSpec (n := n) e) (x : PairVec n) :
    (nodeSplit θ spec x).1-(nodeSplit θ spec x).2=nodeWith (softplus θ) spec (x.1-x.2) := by
  cases spec with
  | affine w b => exact stoppingExpr_recovery _ _
  | activation w b =>
      change (softSplit θ _ _).1-(softSplit θ _ _).2=softplus θ _
      rw [softSplit_recovery θ _ _ hθ,stoppingExpr_recovery]
  | addition i j => exact stoppingExpr_recovery _ _
  | pool inputs => exact stoppingExpr_recovery _ _

/-- Actual all-node Softplus decomposition recovery on the same shared graph. -/
theorem graphSplit_recovery {d n} (c : Circuit d n) (plan : Plan c)
    (θ : ℝ) (hθ : 0<θ) (x : PairVec d) :
    (graphSplit θ c plan x).1-(graphSplit θ c plan x).2=graphSoft θ c plan (x.1-x.2) := by
  induction c with
  | inputs => rfl
  | @node n prior op ih =>
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [graphSplit,graphSoft,graphWith,Fin.snoc_last,Pi.sub_apply]
        rw [nodeSplit_recovery θ hθ,ih]
        rfl
      · simpa only [graphSplit,graphSoft,graphWith,Fin.snoc_castSucc,Pi.sub_apply]
          using congrFun (ih plan.1) i

theorem nodeSpec_additive {n e} (spec : NodeSpec (n := n) e) : e.Additive := by
  cases spec with
  | affine w b => exact SignedExpr.affine_additive w b
  | activation w b => exact ⟨SignedExpr.affine_additive w b,trivial⟩
  | addition i j => exact ⟨trivial,trivial⟩
  | pool inputs => exact orderedPool_additive _ (fun _ => trivial)

theorem plan_additive {d n} (c : Circuit d n) (plan : Plan c) : c.Additive := by
  induction c with
  | inputs => trivial
  | node prior op ih => exact ⟨ih plan.1,nodeSpec_additive plan.2⟩

/-- The source decision sets: forced affine/addition nodes, mixed activation
choices, and arbitrary normalized finite pool choices (without entropy there). -/
def NodePolicy {n e} : NodeSpec (n := n) e → Type
  | .affine _ _ => Unit
  | .activation _ _ => Set.Icc (0 : ℝ) 1
  | .addition _ _ => Unit
  | @NodeSpec.pool _ k _ => Thesis.RoutingExtended.Policy (Fin (k+1))

def Strategy {d n} : (c : Circuit d n) → Plan c → Type
  | .inputs, _ => Unit
  | .node prior _, plan => Strategy prior plan.1 × NodePolicy plan.2

end Thesis.SoftplusCircuit
