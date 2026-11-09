import Thesis.ReLUNetEquilibrium
import Thesis.SoftplusBoundary
import Thesis.SoftplusDecomposition
import Thesis.GeneralRegularization

noncomputable section
namespace Thesis.SoftplusGame
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward
open Thesis.ReLUNetGame Thesis.RoutingBackward Matrix
open scoped BigOperators

/-- The existing source stop/continue strategy space, with both pure and mixed
policies. The sigmoid selection is normalized at every temperature. -/
def gibbsProbability (θ z : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨gate θ z,⟨(gate_pos θ z).le,(gate_lt_one θ z).le⟩⟩

def gibbsStrategy {n m} (θ : ℝ) : (net : Network n m) → Vec n → Strategy net
  | .output _, _ => ()
  | .layer wp wn bp bn tail, x =>
      (fun j => gibbsProbability θ (preactivation wp wn bp bn x j),
        gibbsStrategy θ tail (softLayer θ wp wn bp bn x))

/-- Arbitrary randomized stop/continue followed by the existing total signed
weight kernel. Zero-fan-in continuation goes to the same cemetery as stopping. -/
def mixedTransition {n k} (r : Set.Icc (0 : ℝ) 1)
    (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool)
    (target : Option (Fin n × Bool)) : ℝ :=
  (if target=none then 1-r.val else 0)+r.val*
    Thesis.StoppingBoundary.transition wp wn (fun _ => true) j turn target

theorem mixedTransition_normalized {n k} (r : Set.Icc (0 : ℝ) 1)
    (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool) :
    (∑ target,mixedTransition r wp wn j turn target)=1 := by
  simp only [mixedTransition,Finset.sum_add_distrib,← Finset.mul_sum,
    Thesis.StoppingBoundary.transition_normalized,mul_one]
  simp

theorem mixedTransition_nonnegative {n k} (r : Set.Icc (0 : ℝ) 1)
    (wp wn : Matrix (Fin k) (Fin n) ℝ) (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i)
    (j : Fin k) (turn : Bool) (target : Option (Fin n × Bool)) :
    0≤mixedTransition r wp wn j turn target := by
  apply add_nonneg
  · split_ifs
    · exact sub_nonneg.mpr r.property.2
    · exact le_rfl
  · exact mul_nonneg r.property.1
      (Thesis.StoppingBoundary.transition_nonnegative wp wn (fun _ => true) hw j turn target)

theorem gibbsTransition_eq_source {n k} (θ z : ℝ)
    (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool) :
    mixedTransition (gibbsProbability θ z) wp wn j turn =
      Thesis.SoftplusBoundary.transition θ z wp wn j turn := rfl

theorem mixed_zero_fanIn_absorbs {n k} (r : Set.Icc (0 : ℝ) 1)
    (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool)
    (hz : Thesis.BackwardGames.fanIn wp wn j=0) :
    mixedTransition r wp wn j turn none=1 := by
  simp [mixedTransition,Thesis.StoppingBoundary.transition,hz]

theorem continuation_recovery_total {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (b : Vec k) (p q : Vec n) (j : Fin k) :
    continuation wp wn b p q j=((wp *ᵥ p+wn *ᵥ q)+b) j := by
  by_cases hz : rowDiscount wp wn j=0
  · have he := Thesis.StoppingBoundary.zero_fanIn_weights wp wn hw j hz
    simp [continuation,hz,Matrix.mulVec,dotProduct,he]
  · exact continuation_recovery wp wn b p q j hz

theorem continuation_mono_total {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (b : Vec k)
    {p q p' q' : Vec n} (hp : p≤p') (hq : q≤q') (j : Fin k) :
    continuation wp wn b p q j≤continuation wp wn b p' q' j := by
  rw [continuation_recovery_total wp wn hw,continuation_recovery_total wp wn hw]
  exact add_le_add (add_le_add
    (positive_matrix_monotone wp (fun j i => (hw j i).1) hp j)
    (positive_matrix_monotone wn (fun j i => (hw j i).2) hq j)) le_rfl

theorem continuation_signed_total {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (bp bn : Vec k) (x : Vec n) (j : Fin k) :
    continuation wp wn (bp-bn) x (-x) j=preactivation wp wn bp bn x j ∧
    continuation wn wp (bn-bp) x (-x) j= -preactivation wp wn bp bn x j := by
  constructor
  · rw [continuation_recovery_total wp wn hw]
    simp only [preactivation,Matrix.sub_mulVec,Matrix.mulVec_neg]
    rfl
  · rw [continuation_recovery_total wn wp (fun j i => ⟨(hw j i).2,(hw j i).1⟩)]
    simp only [preactivation,Matrix.mulVec_neg,Matrix.sub_mulVec,Pi.add_apply,Pi.sub_apply,Pi.neg_apply]
    ring

/-- Signed (player-plus minus player-minus) expected payoff. Each active plus
state receives +theta H; each active minus state receives -theta H. -/
def policyValue {n m} (θ : ℝ) : (net : Network n m) → Strategy net → Strategy net →
    Vec n → Vec n → PairVec m
  | .output _, _, _, p, q => (p,q)
  | .layer wp wn bp bn tail, plus, minus, p, q =>
      policyValue θ tail plus.2 minus.2
        (fun j => (plus.1 j).val*continuation wp wn (bp-bn) p q j+
          θ*Real.binEntropy (plus.1 j).val)
        (fun j => (minus.1 j).val*continuation wn wp (bn-bp) p q j-
          θ*Real.binEntropy (minus.1 j).val)

theorem entropy_min_bound (θ z : ℝ) (hθ : 0<θ) (r : Set.Icc (0 : ℝ) 1) :
    -softplus θ z≤r.val*(-z)-θ*Real.binEntropy r.val := by
  have h := entropy_policy_le_softplus θ z r.val hθ r.property.1 r.property.2
  linarith

theorem entropy_min_value (θ z : ℝ) (hθ : 0<θ) :
    gate θ z*(-z)-θ*Real.binEntropy (gate θ z)= -softplus θ z := by
  have h := entropy_gate_value θ z hθ
  linarith

/-- Local optimality against every randomized binary action. -/
def MaximizesEntropy (θ z : ℝ) (r : Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ a : Set.Icc (0 : ℝ) 1,a.val*z+θ*Real.binEntropy a.val≤r.val*z+θ*Real.binEntropy r.val

theorem maximizesEntropy_iff (θ z : ℝ) (hθ : 0<θ) (r : Set.Icc (0 : ℝ) 1) :
    MaximizesEntropy θ z r ↔ r=gibbsProbability θ z := by
  constructor
  · intro h
    apply Subtype.ext
    apply (entropy_gate_unique θ z r.val hθ r.property.1 r.property.2).mp
    apply le_antisymm (entropy_policy_le_softplus θ z r.val hθ r.property.1 r.property.2)
    have hl := h (gibbsProbability θ z)
    simpa only [gibbsProbability,entropy_gate_value θ z hθ] using hl
  · rintro rfl a
    rw [show (gibbsProbability θ z).val=gate θ z from rfl,entropy_gate_value θ z hθ]
    exact entropy_policy_le_softplus θ z a.val hθ a.property.1 a.property.2

theorem minimizesEntropy_neg_iff (θ z : ℝ) (hθ : 0<θ) (r : Set.Icc (0 : ℝ) 1) :
    (∀ a : Set.Icc (0 : ℝ) 1,r.val*(-z)-θ*Real.binEntropy r.val≤
      a.val*(-z)-θ*Real.binEntropy a.val) ↔ r=gibbsProbability θ z := by
  rw [← maximizesEntropy_iff θ z hθ]
  unfold MaximizesEntropy
  constructor <;> intro h a <;> have hh := h a <;> linarith

end Thesis.SoftplusGame
