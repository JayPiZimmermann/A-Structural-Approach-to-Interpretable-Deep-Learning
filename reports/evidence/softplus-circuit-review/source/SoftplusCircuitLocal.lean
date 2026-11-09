import Thesis.SoftplusCircuitModel

noncomputable section
namespace Thesis.SoftplusCircuit
open HiddenMonotonicity Thesis.Regularization Thesis.StoppingDAG
open scoped BigOperators

def canonicalNode {n e} (θ : ℝ) (spec : NodeSpec (n := n) e) (x : Vec n) : NodePolicy spec :=
  match spec with
  | .affine _ _ => ()
  | .activation w b => Thesis.SoftplusGame.gibbsProbability θ ((SignedExpr.affine w b).eval x)
  | .addition _ _ => ()
  | .pool inputs => Thesis.RoutingExtended.pure (earliestWinner (fun i => x (inputs i)))

def affineSigned {n} (w : Vec n) (b : ℝ) (v : PairVec n) : ℝ × ℝ :=
  kernelMap (fun i => max (w i) 0,fun i => max (-w i) 0) v+(b,-b)

/-- Signed profile payoff at one actual source operator. Maxpool choices are
unregularized; entropy occurs only at explicitly marked activation states. -/
def nodeSigned {n e} (θ : ℝ) (spec : NodeSpec (n := n) e)
    (plus minus : NodePolicy spec) (v : PairVec n) : ℝ × ℝ :=
  match spec with
  | .affine w b => affineSigned w b v
  | .activation w b =>
      let z := affineSigned w b v
      (plus.val*z.1+θ*Real.binEntropy plus.val,
       minus.val*z.2-θ*Real.binEntropy minus.val)
  | .addition i j => (v.1 i+v.1 j,v.2 i+v.2 j)
  | .pool inputs => (∑ i,plus.prob i*v.1 (inputs i),∑ i,minus.prob i*v.2 (inputs i))

theorem coefficientRow_monotone {n} (w : Vec n) (hw : ∀ i,0≤w i) : Monotone (coefficientRow w) := by
  intro p q hpq
  simp only [coefficientRow_apply]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpq i) (hw i))

theorem kernelMap_monotone {n} (k : PairVec n) (hk : 0≤k) : Monotone (kernelMap k) := by
  intro p q hpq
  simp only [kernelMap_apply]
  exact ⟨add_le_add (coefficientRow_monotone k.1 hk.1 hpq.1)
      (coefficientRow_monotone k.2 hk.2 hpq.2),
    add_le_add (coefficientRow_monotone k.2 hk.2 hpq.1)
      (coefficientRow_monotone k.1 hk.1 hpq.2)⟩

theorem affineSigned_monotone {n} (w : Vec n) (b : ℝ) : Monotone (affineSigned w b) := by
  intro p q hpq
  have hk : (0 : PairVec n)≤(fun i => max (w i) 0,fun i => max (-w i) 0) :=
    ⟨fun i => le_max_right _ _,fun i => le_max_right _ _⟩
  have h := kernelMap_monotone _ hk hpq
  exact ⟨add_le_add h.1 le_rfl,add_le_add h.2 le_rfl⟩

theorem affineSigned_original {n} (w : Vec n) (b : ℝ) (x : Vec n) :
    affineSigned w b (x,-x)=((SignedExpr.affine w b).eval x,-(SignedExpr.affine w b).eval x) := by
  simp only [affineSigned,kernelMap_apply,coefficientRow_apply,Prod.fst_add,Prod.snd_add,
    Pi.neg_apply,mul_neg,SignedExpr.affine_eval]
  have he : ∑ i,w i*x i=(∑ i,max (w i) 0*x i)-(∑ i,max (-w i) 0*x i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_mul,(canonical_weight_split (w i)).1]
  simp only [Finset.sum_neg_distrib]
  apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> linarith

theorem nodeSigned_monotone {n e} (θ : ℝ) (spec : NodeSpec (n := n) e)
    (plus minus : NodePolicy spec) : Monotone (nodeSigned θ spec plus minus) := by
  intro v u hvu
  cases spec with
  | affine w b => exact affineSigned_monotone w b hvu
  | activation w b =>
      have h := affineSigned_monotone w b hvu
      exact ⟨add_le_add (mul_le_mul_of_nonneg_left h.1 plus.property.1) le_rfl,
        sub_le_sub_right (mul_le_mul_of_nonneg_left h.2 minus.property.1) _⟩
  | addition i j => exact ⟨add_le_add (hvu.1 i) (hvu.1 j),add_le_add (hvu.2 i) (hvu.2 j)⟩
  | pool inputs =>
      change (∑ i,plus.prob i*v.1 (inputs i))≤(∑ i,plus.prob i*u.1 (inputs i)) ∧
        (∑ i,minus.prob i*v.2 (inputs i))≤(∑ i,minus.prob i*u.2 (inputs i))
      exact ⟨Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hvu.1 _) (plus.nonnegative i)),
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hvu.2 _) (minus.nonnegative i))⟩

theorem average_le_max {k} (v : Fin (k+1) → ℝ) (p : Thesis.RoutingExtended.Policy (Fin (k+1))) :
    (∑ i,p.prob i*v i)≤v (earliestWinner v) := by
  calc
    _ ≤ ∑ i,p.prob i*v (earliestWinner v) := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (earliestWinner_maximal v i) (p.nonnegative i))
    _ = _ := by rw [← Finset.sum_mul,p.normalized,one_mul]

theorem min_le_average_neg {k} (v : Fin (k+1) → ℝ) (p : Thesis.RoutingExtended.Policy (Fin (k+1))) :
    -v (earliestWinner v)≤∑ i,p.prob i*(-v i) := by
  have h := average_le_max v p
  simpa only [mul_neg,Finset.sum_neg_distrib,neg_le_neg_iff] using neg_le_neg h

theorem pure_average {k} (i : Fin (k+1)) (v : Fin (k+1) → ℝ) :
    (∑ j,(Thesis.RoutingExtended.pure i).prob j*v j)=v i := by
  simp [Thesis.RoutingExtended.pure]

/-- One-step saddle at the actual source operator, for arbitrary local mixed
activation and pool policies. The source pool tie convention is in canonicalNode. -/
theorem nodeSigned_lower {n e} (θ : ℝ) (hθ : 0<θ) (spec : NodeSpec (n := n) e)
    (x : Vec n) (minus : NodePolicy spec) :
    (nodeWith (softplus θ) spec x,-nodeWith (softplus θ) spec x)≤
      nodeSigned θ spec (canonicalNode θ spec x) minus (x,-x) := by
  cases spec with
  | affine w b => exact le_of_eq (affineSigned_original w b x).symm
  | activation w b =>
      simp only [nodeSigned,affineSigned_original,canonicalNode,nodeWith,Thesis.SoftplusGame.gibbsProbability]
      exact ⟨le_of_eq (entropy_gate_value θ _ hθ).symm,
        Thesis.SoftplusGame.entropy_min_bound θ _ hθ minus⟩
  | addition i j =>
      constructor
      · exact le_rfl
      · change -(x i+x j)≤ -x i+ -x j; linarith
  | pool inputs =>
      simp only [nodeWith,orderedInputPool,orderedPool_eval,SignedExpr.eval,nodeSigned,canonicalNode,
        pure_average,Pi.neg_apply]
      exact ⟨le_rfl,min_le_average_neg (fun i => x (inputs i)) minus⟩

theorem nodeSigned_upper {n e} (θ : ℝ) (hθ : 0<θ) (spec : NodeSpec (n := n) e)
    (x : Vec n) (plus : NodePolicy spec) :
    nodeSigned θ spec plus (canonicalNode θ spec x) (x,-x)≤
      (nodeWith (softplus θ) spec x,-nodeWith (softplus θ) spec x) := by
  cases spec with
  | affine w b => exact le_of_eq (affineSigned_original w b x)
  | activation w b =>
      simp only [nodeSigned,affineSigned_original,canonicalNode,nodeWith,Thesis.SoftplusGame.gibbsProbability]
      exact ⟨entropy_policy_le_softplus θ _ plus.val hθ plus.property.1 plus.property.2,
        le_of_eq (Thesis.SoftplusGame.entropy_min_value θ _ hθ)⟩
  | addition i j =>
      constructor
      · exact le_rfl
      · change -x i+ -x j≤ -(x i+x j); linarith
  | pool inputs =>
      simp only [nodeWith,orderedInputPool,orderedPool_eval,SignedExpr.eval,nodeSigned,canonicalNode,
        pure_average,Pi.neg_apply]
      exact ⟨average_le_max (fun i => x (inputs i)) plus,le_rfl⟩

end Thesis.SoftplusCircuit
