import Thesis.SoftplusCircuitEquilibrium

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.Regularization Thesis.StoppingCircuit Thesis.StoppingDAG
open scoped BigOperators

def baseExpr {n e} : NodeSpec (n := n) e → SignedExpr (Fin n)
  | .affine w b => SignedExpr.affine w b
  | .activation w b => SignedExpr.affine w b
  | .addition i j => .add (.input i) (.input j)
  | .pool inputs => orderedInputPool inputs

def nodeWeights {n e} (spec : NodeSpec (n := n) e) (x : Vec n) : PairVec n :=
  expressionKernel (baseExpr spec) (x,0)

def continuationProbability {n e} (θ : ℝ) : NodeSpec (n := n) e → Vec n → ℝ
  | .activation w b, x => gate θ ((SignedExpr.affine w b).eval x)
  | _, _ => 1

def nodeDiscount {n e} (spec : NodeSpec (n := n) e) (x : Vec n) : ℝ :=
  localDiscount (nodeWeights spec x)

def nodeProbability {n e} (θ : ℝ) (spec : NodeSpec (n := n) e) (x : Vec n)
    (target : Option (Fin n × Bool)) : ℝ :=
  (if target=none then 1-continuationProbability θ spec x else 0)+
    continuationProbability θ spec x*localProbability (nodeWeights spec x) target

def selectedWeights {n e} (θ : ℝ) (spec : NodeSpec (n := n) e) (x : Vec n) : PairVec n :=
  continuationProbability θ spec x • nodeWeights spec x

theorem baseExpr_additive {n e} (spec : NodeSpec (n := n) e) : (baseExpr spec).Additive := by
  cases spec with
  | affine w b => exact SignedExpr.affine_additive w b
  | activation w b => exact SignedExpr.affine_additive w b
  | addition i j => exact ⟨trivial,trivial⟩
  | pool inputs => exact orderedPool_additive _ (fun _ => trivial)

theorem nodeWeights_nonnegative {n e} (spec : NodeSpec (n := n) e) (x : Vec n) : 0≤nodeWeights spec x :=
  expressionKernel_nonnegative _ (baseExpr_additive spec) _

theorem continuationProbability_mem {n e} (θ : ℝ) (spec : NodeSpec (n := n) e) (x : Vec n) :
    0≤continuationProbability θ spec x ∧ continuationProbability θ spec x≤1 := by
  cases spec <;> simp only [continuationProbability]
  all_goals first | exact ⟨(gate_pos θ _).le,(gate_lt_one θ _).le⟩ | norm_num

theorem nodeProbability_normalized {n e} (θ : ℝ) (spec : NodeSpec (n := n) e) (x : Vec n) :
    (∑ target,nodeProbability θ spec x target)=1 := by
  simp only [nodeProbability,Finset.sum_add_distrib,← Finset.mul_sum,
    localProbability_normalized,mul_one]
  simp

theorem nodeProbability_nonnegative {n e} (θ : ℝ) (spec : NodeSpec (n := n) e)
    (x : Vec n) (target : Option (Fin n × Bool)) : 0≤nodeProbability θ spec x target := by
  have hg := continuationProbability_mem θ spec x
  apply add_nonneg
  · split_ifs
    · exact sub_nonneg.mpr hg.2
    · exact le_rfl
  · exact mul_nonneg hg.1 (localProbability_nonnegative _ (nodeWeights_nonnegative spec x) target)

theorem nodeDiscount_nonnegative {n e} (spec : NodeSpec (n := n) e) (x : Vec n) :
    0≤nodeDiscount spec x := localDiscount_nonnegative _ (nodeWeights_nonnegative spec x)

theorem node_discount_recovery {n e} (θ : ℝ) (spec : NodeSpec (n := n) e)
    (x : Vec n) (i : Fin n) (b : Bool) :
    nodeDiscount spec x*nodeProbability θ spec x (some (i,b))=
      if b then (selectedWeights θ spec x).2 i else (selectedWeights θ spec x).1 i := by
  simp only [nodeDiscount,nodeProbability,Option.some_ne_none,ite_false,zero_add]
  rw [show ∀ a b c : ℝ,a*(b*c)=b*(a*c) by intros; ring,
    local_discount_recovery _ (nodeWeights_nonnegative spec x)]
  cases b <;> rfl

/-- Only finite pool winner uniqueness is needed; Softplus activation nodes
are smooth even at zero preactivation and zero fan-in. -/
def NodeRegular {n e} : NodeSpec (n := n) e → Vec n → Prop
  | .pool inputs, x => ∀ i,i≠earliestWinner (fun j => x (inputs j)) →
      x (inputs i)<x (inputs (earliestWinner (fun j => x (inputs j))))
  | _, _ => True

def Regular {d n} (θ : ℝ) : (c : Circuit d n) → Plan c → Vec d → Prop
  | .inputs, _, _ => True
  | .node prior _, plan, x => Regular θ prior plan.1 x ∧
      NodeRegular plan.2 (graphSoft θ prior plan.1 x)

def rowMap {n} (k : PairVec n) : Row n := coefficientRow k.1-coefficientRow k.2

theorem expr_eval_hasFDerivAt {n} (e : SignedExpr (Fin n)) (he : e.Additive) (x : Vec n)
    (hx : ExpressionRegular e (x,0)) :
    HasFDerivAt e.eval (rowMap (expressionKernel e (x,0))) x := by
  have hd := (stoppingExpr_hasFDerivAt e he (x,0) hx).comp x (liftCLM n).hasFDerivAt
  convert hd.fst.sub hd.snd using 1
  · funext y
    change e.eval y=(stoppingExpr e (y,0)).1-(stoppingExpr e (y,0)).2
    simpa only [sub_zero] using (stoppingExpr_recovery e (y,0)).symm
  · apply ContinuousLinearMap.ext
    intro v
    change coefficientRow (expressionKernel e (x,0)).1 v-coefficientRow (expressionKernel e (x,0)).2 v=
      (kernelMap (expressionKernel e (x,0)) (v,0)).1-(kernelMap (expressionKernel e (x,0)) (v,0)).2
    simp [kernelMap_apply]

theorem baseExpr_regular {n e} (spec : NodeSpec (n := n) e) (x : Vec n) (hx : NodeRegular spec x) :
    ExpressionRegular (baseExpr spec) (x,0) := by
  cases spec with
  | affine w b => exact ExpressionRegular_affine w b (x,0)
  | activation w b => exact ExpressionRegular_affine w b (x,0)
  | addition i j => exact ⟨trivial,trivial⟩
  | pool inputs =>
      apply orderedInputPool_regular inputs (x,0) (earliestWinner (fun j => x (inputs j)))
      simpa only [NodeRegular,Pi.zero_apply,sub_zero] using hx

theorem rowMap_smul {n} (g : ℝ) (k : PairVec n) : rowMap (g • k)=g • rowMap k := by
  simp only [rowMap,Prod.smul_fst,Prod.smul_snd,coefficientRow_smul,smul_sub]

/-- Actual local ordinary derivative. The sigmoid is part of the path
continuation probability; the source structural discount stays unchanged. -/
theorem nodeWith_hasFDerivAt {n e} (θ : ℝ) (hθ : 0<θ) (spec : NodeSpec (n := n) e)
    (x : Vec n) (hx : NodeRegular spec x) :
    HasFDerivAt (nodeWith (softplus θ) spec) (rowMap (selectedWeights θ spec x)) x := by
  have hd := expr_eval_hasFDerivAt _ (baseExpr_additive spec) x (baseExpr_regular spec x hx)
  cases spec with
  | affine w b =>
      change HasFDerivAt (fun y => (SignedExpr.affine w b).eval y)
        (rowMap (1 • expressionKernel (SignedExpr.affine w b) (x,0))) x
      simpa only [one_smul,baseExpr] using hd
  | activation w b =>
      change HasFDerivAt (fun y => softplus θ ((SignedExpr.affine w b).eval y))
        (rowMap (gate θ ((SignedExpr.affine w b).eval x) •
          expressionKernel (SignedExpr.affine w b) (x,0))) x
      have h := (hasDerivAt_softplus θ ((SignedExpr.affine w b).eval x) hθ).comp_hasFDerivAt x hd
      simpa only [rowMap_smul,baseExpr,Function.comp_def] using h
  | addition i j =>
      change HasFDerivAt (fun y => y i+y j)
        (rowMap (1 • expressionKernel (.add (.input i) (.input j)) (x,0))) x
      simpa only [one_smul,baseExpr,SignedExpr.eval] using hd
  | pool inputs =>
      change HasFDerivAt (fun y => (orderedInputPool inputs).eval y)
        (rowMap (1 • expressionKernel (orderedInputPool inputs) (x,0))) x
      simpa only [one_smul,baseExpr] using hd

end Thesis.SoftplusCircuit
