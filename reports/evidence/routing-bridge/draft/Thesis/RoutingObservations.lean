import Thesis.RoutingPolicyBridge
import HiddenMonotonicity.PrefixSources

/-! Marked-state observations on the actual complete routing histories.
The outside and bias histories are retained by `RoutingHistory.probability`;
they receive zero observation when measuring ordinary-neuron occupation. -/
noncomputable section
namespace Thesis.RoutingObservations
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingExtended
open Thesis.RoutingNetwork Thesis.RoutingHistory Thesis.RoutingPolicyBridge
open Thesis.RoutingBackward Thesis.BackwardGames
open scoped BigOperators

def extendObservation {n : ℕ} (outside bias : Tree) (child : Fin n → Tree)
    (outsideObs : Observation outside) (biasObs : Observation bias)
    (obs : (i : Fin n) → Observation (child i)) :
    (i : Fin (n+2)) → Observation (extend outside bias child i) :=
  Fin.cases outsideObs (Fin.cases biasObs obs)

/-- Mark ordinary child histories and leave outside/bias absorption unmarked. -/
def routeObservation {n : ℕ} (q : Bool) (ε b : ℝ) (w : Fin n → ℝ)
    (child : Fin n → Tree) (hε : 0≤ε) (hb : 0≤b) (hw : ∀ i,0≤w i)
    (obs : (i : Fin n) → Observation (child i)) :
    Observation (route q ε b w child hε hb hw) :=
  (0, extendObservation (.terminal (signed q 1)) (.terminal (signed q 1)) child
    (0 : ℝ) (0 : ℝ) obs)

theorem canonicalIntegral_route {n : ℕ} (θ α β : ℝ) (q : Bool) (ε b : ℝ)
    (w : Fin n → ℝ) (child : Fin n → Tree)
    (hε : 0≤ε) (hb : 0≤b) (hw : ∀ i,0≤w i)
    (obs : (i : Fin n) → Observation (child i)) :
    canonicalIntegral θ α β (route q ε b w child hε hb hw)
      (routeObservation q ε b w child hε hb hw obs) =
    ∑ i, (canonical θ (route q ε b w child hε hb hw)).1.prob i.succ.succ *
      canonicalIntegral θ α β (child i) (obs i) := by
  let rp := (canonical θ (route q ε b w child hε hb hw)).1
  unfold canonicalIntegral routeObservation route
  erw [integral_routing]
  simp [canonical, extendObservation, extend, Fin.sum_univ_succ]
  change rp.prob 0 * integral α β (.terminal (signed q 1)) () () (0 : ℝ) +
    (rp.prob 1 * integral α β (.terminal (signed q 1)) () () (0 : ℝ) +
      ∑ i, rp.prob i.succ.succ * integral α β (child i) (canonical θ (child i))
        (canonical θ (child i)) (obs i)) =
    ∑ i, rp.prob i.succ.succ * integral α β (child i) (canonical θ (child i))
      (canonical θ (child i)) (obs i)
  erw [integral_terminal]
  simp only [mul_zero, zero_add]

theorem canonicalIntegral_activation (θ α β : ℝ) (q : Bool) (p n : Tree)
    (op : Observation p) (on : Observation n) :
    canonicalIntegral θ α β (.activation q p n) (0,op,on) =
    if (canonical θ (.activation q p n)).1 then
      α*canonicalIntegral θ α β p op + β*canonicalIntegral θ α β n on else 0 := by
  unfold canonicalIntegral
  erw [integral_activation]
  simp only [canonical, ite_self, zero_add]
  rfl

def inputLayerObservation {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0≤ε) (x : Vec n)
    (mark : Fin n → Bool → ℝ) (j : Fin k) (q : Bool) :
    Observation (inputLayerGames wp wn bp bn ε hε x j q) :=
  (0,
    routeObservation q ε (max (bp j-bn j) 0) (posContribution wp wn x j)
      (fun _ => .terminal (signed q 1)) hε (le_max_right _ _) (fun _ => le_max_right _ _)
      (fun i => mark i q),
    routeObservation (!q) ε (max (-(bp j-bn j)) 0) (negContribution wp wn x j)
      (fun _ => .terminal (signed (!q) 1)) hε (le_max_right _ _) (fun _ => le_max_right _ _)
      (fun i => mark i (!q)))

def layerObservation {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (ε : ℝ) (hε : 0≤ε) (input : Fin n → Bool → Tree)
    (obs : (i : Fin n) → (q : Bool) → Observation (input i q))
    (j : Fin k) (q : Bool) : Observation (layerGames wp wn bp bn ε hε input j q) :=
  (0,
    routeObservation q ε (max (bp j-bn j) 0) (fun i => max (wp j i-wn j i) 0)
      (fun i => input i q) hε (le_max_right _ _) (fun _ => le_max_right _ _)
      (fun i => obs i q),
    routeObservation (!q) ε (max (-(bp j-bn j)) 0) (fun i => max (-(wp j i-wn j i)) 0)
      (fun i => input i (!q)) hε (le_max_right _ _) (fun _ => le_max_right _ _)
      (fun i => obs i (!q)))

/-- Independent propagation of scalar marks through the existing signed trace. -/
def traceObservation {n m : ℕ} : MaskedTrace n m → (Fin n → Bool → ℝ) → Fin m → Bool → ℝ
  | .output _, mark => mark
  | .layer wp wn g tail, mark => traceObservation tail (fun j q =>
      if g j then (∑ i, wp j i * mark i q) + (∑ i, wn j i * mark i (!q)) else 0)

def localObservation {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (α β ε : ℝ) (x : Vec n) (mark : Fin n → Bool → ℝ)
    (j : Fin k) (q : Bool) : ℝ :=
  if 0 < preactivation wp wn bp bn x j then
    (∑ i, (α * posContribution wp wn x j i / posDenominator wp wn bp bn ε x j) * mark i q) +
    (∑ i, (β * negContribution wp wn x j i / negDenominator wp wn bp bn ε x j) * mark i (!q))
  else 0

theorem inputLayer_integral {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (α β ε : ℝ) (hε : 0≤ε) (x : Vec n)
    (mark : Fin n → Bool → ℝ) (j : Fin k) (q : Bool) :
    canonicalIntegral 1 α β (inputLayerGames wp wn bp bn ε hε x j q)
      (inputLayerObservation wp wn bp bn ε hε x mark j q) =
    localObservation wp wn bp bn α β ε x mark j q := by
  change canonicalIntegral 1 α β (.activation q _ _) (0,_,_) = _
  rw [canonicalIntegral_activation]
  change (if (canonical 1 (inputLayerGames wp wn bp bn ε hε x j q)).1 then _ else _) = _
  rw [inputLayerGames_selected_gate]
  simp only [decide_eq_true_eq, localObservation]
  split_ifs with hg
  · erw [canonicalIntegral_route, canonicalIntegral_route]
    simp only [canonicalIntegral, integral_terminal]
    change α*(∑ i, (inputPositive wp wn bp bn ε hε x j q).prob i.succ.succ * mark i q) +
      β*(∑ i, (inputNegative wp wn bp bn ε hε x j q).prob i.succ.succ * mark i (!q)) = _
    simp_rw [(input_policy_probabilities wp wn bp bn ε hε x j q _).1,
      (input_policy_probabilities wp wn bp bn ε hε x j q _).2]
    simp only [Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  · rfl

theorem layer_integral {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (α β ε : ℝ) (hε : 0≤ε) (input : Fin n → Bool → Tree)
    (x : Vec n) (hx : ∀ i,0≤x i) (hv : ∀ i q,value 1 (input i q)=signed q (x i))
    (obs : (i : Fin n) → (q : Bool) → Observation (input i q))
    (j : Fin k) (q : Bool) :
    canonicalIntegral 1 α β (layerGames wp wn bp bn ε hε input j q)
      (layerObservation wp wn bp bn ε hε input obs j q) =
    localObservation wp wn bp bn α β ε x
      (fun i r => canonicalIntegral 1 α β (input i r) (obs i r)) j q := by
  change canonicalIntegral 1 α β (.activation q _ _) (0,_,_) = _
  rw [canonicalIntegral_activation]
  change (if (canonical 1 (layerGames wp wn bp bn ε hε input j q)).1 then _ else _) = _
  rw [layerGames_selected_gate wp wn bp bn ε hε input x hx hv]
  simp only [decide_eq_true_eq, localObservation]
  split_ifs with hg
  · rw [canonicalIntegral_route, canonicalIntegral_route]
    change α*(∑ i, (layerPositive wp wn bp bn ε hε input j q).prob i.succ.succ *
        canonicalIntegral 1 α β (input i q) (obs i q)) +
      β*(∑ i, (layerNegative wp wn bp bn ε hε input j q).prob i.succ.succ *
        canonicalIntegral 1 α β (input i (!q)) (obs i (!q))) = _
    simp_rw [(layer_policy_probabilities wp wn bp bn ε hε input x hx hv j q _).1,
      (layer_policy_probabilities wp wn bp bn ε hε input x hx hv j q _).2]
    simp only [Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  · rfl

def propagateObservation (ε : ℝ) (hε : 0≤ε) : {n m : ℕ} → (net : Network n m) →
    (input : Fin n → Bool → Tree) →
    ((i : Fin n) → (q : Bool) → Observation (input i q)) →
    (j : Fin m) → (q : Bool) → Observation (propagate ε hε net input j q)
  | _, _, .output _, _, obs => obs
  | _, _, .layer wp wn bp bn tail, input, obs =>
      propagateObservation ε hε tail (layerGames wp wn bp bn ε hε input)
        (layerObservation wp wn bp bn ε hε input obs)

theorem propagate_integral {n m : ℕ} (net : Network n m) (α β ε : ℝ) (hε : 0≤ε)
    (input : Fin n → Bool → Tree) (x : Vec n) (hx : ∀ i,0≤x i)
    (hv : ∀ i q,value 1 (input i q)=signed q (x i))
    (obs : (i : Fin n) → (q : Bool) → Observation (input i q))
    (j : Fin m) (q : Bool) :
    canonicalIntegral 1 α β (propagate ε hε net input j q)
      (propagateObservation ε hε net input obs j q) =
    traceObservation (routingTrace α β ε net x)
      (fun i r => canonicalIntegral 1 α β (input i r) (obs i r)) j q := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      change canonicalIntegral 1 α β (propagate ε hε tail (layerGames wp wn bp bn ε hε input) j q)
        (propagateObservation ε hε tail (layerGames wp wn bp bn ε hε input)
          (layerObservation wp wn bp bn ε hε input obs) j q) = _
      rw [ih _ _ (fun _ => le_max_right _ _)
        (layerGames_value wp wn bp bn ε hε input x hx hv)]
      simp only [routingTrace, traceObservation]
      congr 1
      funext a r
      rw [layer_integral wp wn bp bn α β ε hε input x hx hv obs]
      simp only [localObservation, decide_eq_true_eq]

def networkObservation {n m : ℕ} (net : Network n m) (ε : ℝ) (hε : 0≤ε)
    (x : Vec n) (mark : Fin n → Bool → ℝ) :
    (j : Fin m) → (q : Bool) → Observation (networkGame net ε hε x j q) :=
  match net with
  | .output _ => mark
  | .layer wp wn bp bn tail =>
      propagateObservation ε hε tail (inputLayerGames wp wn bp bn ε hε x)
        (inputLayerObservation wp wn bp bn ε hε x mark)

theorem network_integral {n m : ℕ} (net : Network n m) (α β ε : ℝ) (hε : 0≤ε)
    (x : Vec n) (mark : Fin n → Bool → ℝ) (j : Fin m) (q : Bool) :
    canonicalIntegral 1 α β (networkGame net ε hε x j q)
      (networkObservation net ε hε x mark j q) =
    traceObservation (routingTrace α β ε net x) mark j q := by
  cases net with
  | output n => exact integral_terminal α β _ _ _ _
  | layer wp wn bp bn tail =>
      change canonicalIntegral 1 α β (propagate ε hε tail (inputLayerGames wp wn bp bn ε hε x) j q)
        (propagateObservation ε hε tail (inputLayerGames wp wn bp bn ε hε x)
          (inputLayerObservation wp wn bp bn ε hε x mark) j q) = _
      rw [propagate_integral tail α β ε hε _ _
        (fun _ => le_max_right _ _) (inputLayerGames_value wp wn bp bn ε hε x)]
      simp only [routingTrace, traceObservation]
      congr 1
      funext a r
      rw [inputLayer_integral]
      simp only [localObservation, decide_eq_true_eq]

theorem traceObservation_kernels {n m : ℕ} (tr : MaskedTrace n m)
    (mark : Fin n → Bool → ℝ) (j : Fin m) (q : Bool) :
    traceObservation tr mark j q =
      (∑ i, (occupations tr).1 j i * mark i q) +
      (∑ i, (occupations tr).2 j i * mark i (!q)) := by
  induction tr with
  | output n => simp [traceObservation, occupations, Matrix.one_apply]
  | @layer n k m wp wn g tail ih =>
      rw [traceObservation, ih]
      have row (r : Bool) (a : Fin k) :
          (if g a then (∑ i, wp a i * mark i r) + (∑ i, wn a i * mark i (!r)) else 0) =
          (∑ i, gated g wp a i * mark i r) + (∑ i, gated g wn a i * mark i (!r)) := by
        cases hg : g a <;> simp [hg, gated]
      simp_rw [row]
      simp only [Bool.not_not]
      have commute (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin k) (Fin n) ℝ)
          (r : Fin n → ℝ) :
          (∑ i, ∑ a, A j a * B a i * r i) =
          ∑ a, A j a * (∑ i, B a i * r i) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum, mul_assoc]
      simp only [occupations, Matrix.add_apply, Matrix.mul_apply, add_mul,
        Finset.sum_add_distrib, Finset.sum_mul]
      rw [commute, commute, commute, commute]
      simp only [mul_add, Finset.sum_add_distrib]
      ring

/-- Actual discounted complete-history occupation of a particular input/owner.
All activation-stop, bias and outside histories remain present with zero mark. -/
def networkOccupation {n m : ℕ} (net : Network n m) (α β ε : ℝ) (hε : 0≤ε)
    (x : Vec n) (j : Fin m) (q : Bool) (i : Fin n) (r : Bool) : ℝ :=
  canonicalIntegral 1 α β (networkGame net ε hε x j q)
    (networkObservation net ε hε x (fun a owner => if a=i ∧ owner=r then 1 else 0) j q)

theorem networkOccupation_eq_rgOccupation {n m : ℕ} (net : Network n m)
    (α β ε : ℝ) (hε : 0≤ε) (x : Vec n)
    (j : Fin m) (q : Bool) (i : Fin n) (r : Bool) :
    networkOccupation net α β ε hε x j q i r =
      rgOccupation net α β ε x j i (Bool.xor q r) := by
  rw [networkOccupation, network_integral, traceObservation_kernels]
  cases q <;> cases r <;>
    simp [← (rg_occupation_kernels net α β ε x j i).1,
      ← (rg_occupation_kernels net α β ε x j i).2]

theorem networkOccupation_nonnegative {n m : ℕ} (net : Network n m)
    (α β ε : ℝ) (hα : 0≤α) (hβ : 0≤β) (hε : 0≤ε) (x : Vec n)
    (j : Fin m) (q : Bool) (i : Fin n) (r : Bool) :
    0 ≤ networkOccupation net α β ε hε x j q i r := by
  rw [networkOccupation_eq_rgOccupation]
  exact Thesis.RoutingTransitions.occupation_nonnegative net α β ε hα hβ hε x j i _

/-- The alpha-beta rule is recovered from occupations of the actual canonical
game histories, with source ownership reversal on negative routes. -/
theorem network_alpha_beta_recovery {n m : ℕ} (net : Network n m)
    (α β ε : ℝ) (hε : 0≤ε) (x : Vec n) (R : Vec m) (i : Fin n) :
    lrp α β ε net x R i = ∑ j, R j *
      (networkOccupation net α β ε hε x j true i true -
       networkOccupation net α β ε hε x j true i false) := by
  simp only [networkOccupation_eq_rgOccupation, Bool.true_xor, Bool.not_true, Bool.not_false]
  exact thesis_alpha_beta_recovery net α β ε x R i

theorem propagate_append {d n m : ℕ} (pre : Network d n) (suffix : Network n m)
    (ε : ℝ) (hε : 0≤ε) (input : Fin d → Bool → Tree) :
    propagate ε hε (pre.append suffix) input =
      propagate ε hε suffix (propagate ε hε pre input) := by
  induction pre with
  | output d => rfl
  | layer wp wn bp bn tail ih =>
      exact ih suffix (layerGames wp wn bp bn ε hε input)

/-- For a nonempty prefix, the composed source tree is literally the game of
the appended network, including every lower prefix subtree. -/
theorem networkGame_append_layer {d k n m : ℕ}
    (wp wn : Matrix (Fin k) (Fin d) ℝ) (bp bn : Vec k)
    (pre : Network k n) (suffix : Network n m) (ε : ℝ) (hε : 0≤ε) (x : Vec d) :
    networkGame ((Network.layer wp wn bp bn pre).append suffix) ε hε x =
      propagate ε hε suffix (networkGame (Network.layer wp wn bp bn pre) ε hε x) := by
  exact propagate_append pre suffix ε hε (inputLayerGames wp wn bp bn ε hε x)

/-- A marked prefix state is observed inside each complete original history.
Continuation through its whole prefix subtree is still sampled and integrated. -/
def intermediateOccupation {n m : ℕ} (suffix : Network n m)
    (α β ε : ℝ) (hε : 0≤ε) (input : Fin n → Bool → Tree)
    (j : Fin m) (q : Bool) (i : Fin n) (r : Bool) : ℝ :=
  canonicalIntegral 1 α β (propagate ε hε suffix input j q)
    (propagateObservation ε hε suffix input
      (fun a owner => rootObservation (input a owner) (if a=i ∧ owner=r then 1 else 0)) j q)

theorem intermediateOccupation_eq_rgOccupation {n m : ℕ} (suffix : Network n m)
    (α β ε : ℝ) (hε : 0≤ε) (input : Fin n → Bool → Tree) (x : Vec n)
    (hx : ∀ i,0≤x i) (hv : ∀ i q,value 1 (input i q)=signed q (x i))
    (j : Fin m) (q : Bool) (i : Fin n) (r : Bool) :
    intermediateOccupation suffix α β ε hε input j q i r =
      rgOccupation suffix α β ε x j i (Bool.xor q r) := by
  rw [intermediateOccupation, propagate_integral suffix α β ε hε input x hx hv]
  simp only [canonicalIntegral, integral_root]
  rw [traceObservation_kernels]
  cases q <;> cases r <;>
    simp [← (rg_occupation_kernels suffix α β ε x j i).1,
      ← (rg_occupation_kernels suffix α β ε x j i).2]

/-- The actual full appended-network histories recover intermediate occupation.
`networkGame_append_layer` identifies the complete tree with the original game;
no independently truncated replacement history is used on the left. -/
theorem network_intermediateOccupation {d k n m : ℕ}
    (wp wn : Matrix (Fin k) (Fin d) ℝ) (bp bn : Vec k)
    (pre : Network k n) (suffix : Network n m)
    (α β ε : ℝ) (hε : 0≤ε) (x : Vec d)
    (j : Fin m) (q : Bool) (i : Fin n) (r : Bool) :
    intermediateOccupation suffix α β ε hε
      (networkGame (Network.layer wp wn bp bn pre) ε hε x) j q i r =
    rgOccupation suffix α β ε ((Network.layer wp wn bp bn pre).eval x)
      j i (Bool.xor q r) := by
  apply intermediateOccupation_eq_rgOccupation
  · exact eval_nonnegative pre _ (fun _ => le_max_right _ _)
  · exact networkGame_value (Network.layer wp wn bp bn pre) ε hε x

end Thesis.RoutingObservations
