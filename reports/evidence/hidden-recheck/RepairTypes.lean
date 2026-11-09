import HiddenMonotonicity.AffineChunk
import HiddenMonotonicity.AffineHeads
import HiddenMonotonicity.AlmostEverywhere
import HiddenMonotonicity.DifferentiableBackward
import HiddenMonotonicity.DifferentiableHeads
import HiddenMonotonicity.MaxPool
import HiddenMonotonicity.PoolingCircuit
import HiddenMonotonicity.PrefixSources

section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (rp rn : Row m) (bp bn : ℝ) (x : PairVec n),
 (net.affineHeads rp rn bp bn x).1 - (net.affineHeads rp rn bp bn x).2 = net.affineLogit rp rn bp bn (x.1-x.2) := @HiddenMonotonicity.Network.affine_heads_recovery
#check @HiddenMonotonicity.Network.affine_heads_recovery
#print axioms HiddenMonotonicity.Network.affine_heads_recovery
end

section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : Vec n) (hx : net.Strict x) (rp rn : Row m) (bp bn : ℝ),
 HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1)
 ((1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac - (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x ∧
 HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2)
 ((-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac + (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x := @HiddenMonotonicity.Network.affine_plain_head_formulas
#check @HiddenMonotonicity.Network.affine_plain_head_formulas
#print axioms HiddenMonotonicity.Network.affine_plain_head_formulas
end

section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : Vec n) (w : Vec m) (head : Bool),
 ((net.originalTrace x).run (fun _ => 0) (affineReadoutSeed (coefficientRow (fun i => max (w i) 0)) (coefficientRow (fun i => max (-w i) 0)) 0 head)).1 +
 ((net.originalTrace x).run (fun _ => 0) (affineReadoutSeed (coefficientRow (fun i => max (w i) 0)) (coefficientRow (fun i => max (-w i) 0)) 0 head)).2 =
 (coefficientRow (fun i => |w i|)).comp net.absoluteMap := @HiddenMonotonicity.Network.affine_canonical_mass
#check @HiddenMonotonicity.Network.affine_canonical_mass
#print axioms HiddenMonotonicity.Network.affine_canonical_mass
end

section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
 (hw : ∀ i j, 0≤wp i j ∧ 0≤wn i j) (hb : 0≤bp ∧ 0≤bn),
 (∀ x, (affineChunk wp wn bp bn x).1-(affineChunk wp wn bp bn x).2 = affineLayer wp wn bp bn (x.1-x.2)) ∧
 (∀ x, 0≤x → 0≤affineChunk wp wn bp bn x) ∧ Monotone (affineChunk wp wn bp bn) ∧
 (∀ x y (a b : ℝ), a+b=1 → affineChunk wp wn bp bn (a • x+b • y) = a • affineChunk wp wn bp bn x+b • affineChunk wp wn bp bn y) ∧
 (∀ i, ConvexOn ℝ Set.univ (fun x => (affineChunk wp wn bp bn x).1 i) ∧ ConvexOn ℝ Set.univ (fun x => (affineChunk wp wn bp bn x).2 i)) := @HiddenMonotonicity.linear_chunk_properties
#check @HiddenMonotonicity.linear_chunk_properties
#print axioms HiddenMonotonicity.linear_chunk_properties
end

section
universe u
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι],
 (∀ x, (finitePool (ι := ι) x).1-(finitePool x).2 = Finset.univ.sup' Finset.univ_nonempty (fun j => x.1 j-x.2 j)) ∧
 (∀ x, 0≤x → 0≤finitePool (ι := ι) x) ∧ Monotone (finitePool (ι := ι)) ∧
 ConvexOn ℝ Set.univ (fun x => (finitePool (ι := ι) x).1) ∧ ConvexOn ℝ Set.univ (fun x => (finitePool (ι := ι) x).2) := @HiddenMonotonicity.maxpool_properties
#check @HiddenMonotonicity.maxpool_properties
#print axioms HiddenMonotonicity.maxpool_properties
end

section
universe u
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {ι : Type u} [Fintype ι] [Nonempty ι] (x : (ι → ℝ) × (ι → ℝ)),
 (winnerPool x).1-(winnerPool x).2 = Finset.univ.sup' Finset.univ_nonempty (fun j => x.1 j-x.2 j) := @HiddenMonotonicity.winnerPool_recovery
#check @HiddenMonotonicity.winnerPool_recovery
#print axioms HiddenMonotonicity.winnerPool_recovery
end

section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {d n : ℕ} (c : Circuit d n) (pooling : ℕ → PoolingRule) (center : ℕ → Bool) (x : Fin d × Bool → ℝ),
 (c.splitWithPolicy pooling center x).1-(c.splitWithPolicy pooling center x).2 = c.eval (fun i => x (i,false)-x (i,true)) := @HiddenMonotonicity.Circuit.split_policy_correct
#check @HiddenMonotonicity.Circuit.split_policy_correct
#print axioms HiddenMonotonicity.Circuit.split_policy_correct
end

section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {d n : ℕ} (c : Circuit d n) (pooling : ℕ → PoolingRule) (center : ℕ → Bool) (x : Fin d × Bool → ℝ) (hx : 0≤x),
 0≤c.splitWithPolicy pooling center x := @HiddenMonotonicity.Circuit.split_policy_nonnegative
#check @HiddenMonotonicity.Circuit.split_policy_nonnegative
#print axioms HiddenMonotonicity.Circuit.split_policy_nonnegative
end

section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {d n : ℕ} (c : Circuit d n) (center : Bool) (x : Fin d × Bool → ℝ),
 c.splitWithPolicy (fun _ => PoolingRule.convex) (fun _ => center) x = c.split center x := @HiddenMonotonicity.Circuit.split_policy_convex_eq
#check @HiddenMonotonicity.Circuit.split_policy_convex_eq
#print axioms HiddenMonotonicity.Circuit.split_policy_convex_eq
end

section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (x : PairVec n) (rp rn : Row m)
 (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ) (head : Bool)
 (hd : DifferentiableAt ℝ (fun y => if head then (net.affineHeads rp rn bp bn y).1 else (net.affineHeads rp rn bp bn y).2) x),
 HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn y).1 else (net.affineHeads rp rn bp bn y).2)
 (assemble ((net.originalTrace (x.1-x.2)).run (fun _ => 0) (affineReadoutSeed rp rn 0 head))) x := @HiddenMonotonicity.Network.affine_head_derivative_of_differentiable
#check @HiddenMonotonicity.Network.affine_head_derivative_of_differentiable
#print axioms HiddenMonotonicity.Network.affine_head_derivative_of_differentiable
end

section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (x : Vec n) (rp rn : Row m)
 (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ) (head : Bool)
 (hd : DifferentiableAt ℝ (fun y => if head then (net.affineHeads rp rn bp bn (balancedLift n y)).1 else (net.affineHeads rp rn bp bn (balancedLift n y)).2) x),
 HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn (balancedLift n y)).1 else (net.affineHeads rp rn bp bn (balancedLift n y)).2)
 (unified ((net.originalTrace x).run (fun _ => 0) (affineReadoutSeed rp rn 0 head))) x := @HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable
#check @HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable
#print axioms HiddenMonotonicity.Network.affine_symmetric_derivative_of_differentiable
end

section
open HiddenMonotonicity
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (x : Vec n) (rp rn : Row m)
 (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ)
 (hg : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1) x)
 (hh : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2) x)
 (α : ℕ → ℝ) (β : ℝ),
 HasFDerivAt (net.affineLogit rp rn bp bn) ((rp-rn).comp (net.originalTrace x).originalJac) x ∧
 ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).1-((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).1 = (rp-rn).comp (net.originalTrace x).originalJac ∧
 ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).2-((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).2 = -((rp-rn).comp (net.originalTrace x).originalJac) := @HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable
#check @HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable
#print axioms HiddenMonotonicity.Network.affine_backward_invariants_of_differentiable
end

section
open HiddenMonotonicity
open MeasureTheory
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ),
 ∀ᵐ x : Vec n, ∀ head : Bool,
 HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn (balancedLift n y)).1 else (net.affineHeads rp rn bp bn (balancedLift n y)).2)
 (unified ((net.originalTrace x).run (fun _ => 0) (affineReadoutSeed rp rn 0 head))) x := @HiddenMonotonicity.Network.affine_heads_ae_derivatives
#check @HiddenMonotonicity.Network.affine_heads_ae_derivatives
#print axioms HiddenMonotonicity.Network.affine_heads_ae_derivatives
end

section
open HiddenMonotonicity
open MeasureTheory
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ),
 ∀ᵐ x : Vec n, ∀ (α : ℕ → ℝ) (β : ℝ),
 HasFDerivAt (net.affineLogit rp rn bp bn) ((rp-rn).comp (net.originalTrace x).originalJac) x ∧
 ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).1-((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).1 = (rp-rn).comp (net.originalTrace x).originalJac ∧
 ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).2-((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).2 = -((rp-rn).comp (net.originalTrace x).originalJac) := @HiddenMonotonicity.Network.affine_ae_backward_invariants
#check @HiddenMonotonicity.Network.affine_ae_backward_invariants
#print axioms HiddenMonotonicity.Network.affine_ae_backward_invariants
end

section
open HiddenMonotonicity
open MeasureTheory
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hw : net.Nonnegative),
 ∀ᵐ x : Vec n, HasFDerivAt net.eval (net.originalTrace x).originalJac x := @HiddenMonotonicity.Network.originalTrace_ae_derivative
#check @HiddenMonotonicity.Network.originalTrace_ae_derivative
#print axioms HiddenMonotonicity.Network.originalTrace_ae_derivative
end

section
open HiddenMonotonicity
open MeasureTheory
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (α : ℕ → ℝ),
 ∀ᵐ x : Vec n, ∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x := @HiddenMonotonicity.Network.absoluteQSources_ae_derivatives
#check @HiddenMonotonicity.Network.absoluteQSources_ae_derivatives
#print axioms HiddenMonotonicity.Network.absoluteQSources_ae_derivatives
end

section
open HiddenMonotonicity
open MeasureTheory
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : Vec n) (α : ℕ → ℝ) (rp rn : Row m) (β : ℝ),
unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)) =
 (1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac - (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum) ∧
 unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)) =
 (-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac + (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum) := @HiddenMonotonicity.Network.affine_Q_row_formulas
#check @HiddenMonotonicity.Network.affine_Q_row_formulas
#print axioms HiddenMonotonicity.Network.affine_Q_row_formulas
end

section
open HiddenMonotonicity
open MeasureTheory
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (α : ℕ → ℝ) (rp rn : Row m) (bp bn β : ℝ),
 ∀ᵐ x : Vec n,
 (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
 HasFDerivAt (net.affineLogit rp rn bp bn) ((rp-rn).comp (net.originalTrace x).originalJac) x ∧
unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)) =
 (1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac - (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum) ∧
 unified ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)) =
 (-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac + (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rp+rn))).sum) := @HiddenMonotonicity.Network.affine_Q_closed_form_ae
#check @HiddenMonotonicity.Network.affine_Q_closed_form_ae
#print axioms HiddenMonotonicity.Network.affine_Q_closed_form_ae
end

section
open HiddenMonotonicity
open MeasureTheory
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ),
 ∀ᵐ x : Vec n,
 (∀ q ∈ net.absoluteQSources x (fun _ => 0), HasFDerivAt q.value q.jacobian x) ∧
HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1)
 ((1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac - (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x ∧
 HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2)
 ((-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac + (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x := @HiddenMonotonicity.Network.affine_plain_Q_gradients_ae
#check @HiddenMonotonicity.Network.affine_plain_Q_gradients_ae
#print axioms HiddenMonotonicity.Network.affine_plain_Q_gradients_ae
end

section
open HiddenMonotonicity
open MeasureTheory
open scoped BigOperators
example : ∀ {n m : ℕ} (net : Network n m) (hc : net.Canonical) (x : Vec n) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ)
 (hg : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1) x)
 (hh : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2) x),
HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1)
 ((1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac - (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x ∧
 HasFDerivAt (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2)
 ((-1/2 : ℝ) • ((rp-rn).comp (net.originalTrace x).originalJac + (sourceRows (net.absoluteQSources x (fun _ => 0)) (rp+rn)).sum)) x := @HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable
#check @HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable
#print axioms HiddenMonotonicity.Network.affine_plain_formulas_of_differentiable
end
