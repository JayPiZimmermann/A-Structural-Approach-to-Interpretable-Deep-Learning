import Thesis.Regularization
import Thesis.StoppingDecomposition
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Binary stop/continue regularizers on the actual probability interval.
The maximum is constructed from lower semicontinuity and compactness; its
properties are derived, not fields of the regularizer. Different maximizer
selections can change the two streams but never their reconstructed difference.
-/
noncomputable section
set_option autoImplicit false
namespace Thesis.GeneralRegularization
open HiddenMonotonicity Set Filter Matrix
open scoped Topology

/-- A finite closed convex nonpositive cost on the probability interval. -/
structure Regularizer where
  cost : ℝ → ℝ
  closed : LowerSemicontinuousOn cost (Icc 0 1)
  convex : ConvexOn ℝ (Icc 0 1) cost
  nonpos : ∀ p ∈ Icc (0 : ℝ) 1, cost p ≤ 0

def objective (R : Regularizer) (z p : ℝ) : ℝ := p * z - R.cost p

theorem exists_optimizer (R : Regularizer) (z : ℝ) :
    ∃ p ∈ Icc (0 : ℝ) 1, IsMaxOn (objective R z) (Icc 0 1) p := by
  have hn : UpperSemicontinuousOn (fun p => -R.cost p) (Icc (0 : ℝ) 1) := by
    intro x hx y hy
    have h := R.closed x hx (-y) (by linarith)
    filter_upwards [h] with p hp
    linarith
  have hc : ContinuousOn (fun p : ℝ => p * z) (Icc 0 1) := by fun_prop
  have hu := hc.upperSemicontinuousOn.add hn
  exact hu.exists_isMaxOn ⟨0, by simp⟩ isCompact_Icc

/-- One fixed maximizer. The unregularized corollary below explicitly selects
stopping at ties instead of depending on this arbitrary choice. -/
def gate (R : Regularizer) (z : ℝ) : ℝ := (exists_optimizer R z).choose

theorem gate_mem (R : Regularizer) (z : ℝ) : gate R z ∈ Icc (0 : ℝ) 1 :=
  (exists_optimizer R z).choose_spec.1

theorem gate_optimal (R : Regularizer) (z : ℝ) :
    IsMaxOn (objective R z) (Icc 0 1) (gate R z) :=
  (exists_optimizer R z).choose_spec.2

/-- The maximum value of the regularized stop/continue objective. -/
def activation (R : Regularizer) (z : ℝ) : ℝ := objective R z (gate R z)

theorem objective_le (R : Regularizer) (z p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    objective R z p ≤ activation R z := gate_optimal R z hp

theorem activation_isGreatest (R : Regularizer) (z : ℝ) :
    IsGreatest (objective R z '' Icc (0 : ℝ) 1) (activation R z) := by
  refine ⟨⟨gate R z, gate_mem R z, rfl⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact objective_le R z p hp

theorem activation_eq_sup (R : Regularizer) (z : ℝ) :
    activation R z = sSup (objective R z '' Icc (0 : ℝ) 1) :=
  (activation_isGreatest R z).csSup_eq.symm

theorem activation_convex (R : Regularizer) : ConvexOn ℝ univ (activation R) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  let p := gate R (a*x+b*y)
  have hx := mul_le_mul_of_nonneg_left (objective_le R x p (gate_mem R _)) ha
  have hy := mul_le_mul_of_nonneg_left (objective_le R y p (gate_mem R _)) hb
  change p * (a*x+b*y) - R.cost p ≤ _
  unfold objective at hx hy
  have hh : (a+b)*R.cost p = R.cost p := by rw [hab, one_mul]
  nlinarith only [hx, hy, hh]

theorem activation_monotone (R : Regularizer) : Monotone (activation R) := by
  intro x y hxy
  have hp := gate_mem R x
  have h := objective_le R y (gate R x) hp
  have hm := mul_le_mul_of_nonneg_left hxy hp.1
  change gate R x*x-R.cost (gate R x) ≤ _
  unfold objective at h
  linarith

theorem activation_sub_le (R : Regularizer) (x y : ℝ) :
    activation R x - activation R y ≤ |x-y| := by
  have hp := gate_mem R x
  have h := objective_le R y (gate R x) hp
  have hm : gate R x * (x-y) ≤ |x-y| := by
    by_cases hxy : 0 ≤ x-y
    · rw [abs_of_nonneg hxy]
      simpa using mul_le_mul_of_nonneg_right hp.2 hxy
    · have hneg : x-y ≤ 0 := le_of_not_ge hxy
      have hm := mul_nonpos_of_nonneg_of_nonpos hp.1 hneg
      exact hm.trans (abs_nonneg _)
  change gate R x*x-R.cost (gate R x) - _ ≤ _
  unfold objective at h
  nlinarith

theorem activation_lipschitz (R : Regularizer) : LipschitzWith 1 (activation R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  apply abs_le.mpr
  constructor
  · have h := activation_sub_le R y x
    rw [abs_sub_comm y x] at h
    linarith
  · exact activation_sub_le R x y

/-- Every optimizer is a genuine supporting slope, including at a tie. -/
theorem optimizer_supports (R : Regularizer) (x p : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (ho : IsMaxOn (objective R x) (Icc 0 1) p)
    (y : ℝ) : activation R x + p*(y-x) ≤ activation R y := by
  have he : objective R x p = activation R x :=
    le_antisymm (objective_le R x p hp) (ho (gate_mem R x))
  have h := objective_le R y p hp
  unfold objective at he h
  linarith

/-- Wherever the value is differentiable, every maximizing gate is its derivative. -/
theorem optimizer_eq_deriv (R : Regularizer) (x p : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (ho : IsMaxOn (objective R x) (Icc 0 1) p)
    (hd : DifferentiableAt ℝ (activation R) x) : p = deriv (activation R) x := by
  have hm : IsLocalMin (fun y => activation R y - p*y) x := by
    apply Filter.Eventually.of_forall
    intro y
    have h := optimizer_supports R x p hp ho y
    dsimp
    linarith
  have he := hm.hasDerivAt_eq_zero (hd.hasDerivAt.sub ((hasDerivAt_id x).const_mul p))
  simp only [mul_one] at he
  linarith

def pairWith (R : Regularizer) (π : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (π (z.1-z.2)*z.1-R.cost (π (z.1-z.2)), π (z.1-z.2)*z.2)

/-- Any fixed maximizing selection yields a valid pair activation. -/
theorem pairWith_valid (R : Regularizer) (π : ℝ → ℝ)
    (hπ : ∀ z, π z ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (objective R z) (Icc 0 1) (π z)) :
    ValidPairActivation (activation R) (pairWith R π) := by
  intro u v
  have he : objective R (u-v) (π (u-v)) = activation R (u-v) :=
    le_antisymm (objective_le R _ _ (hπ _).1) ((hπ _).2 (gate_mem R _))
  dsimp [pairWith, objective] at *
  linarith

theorem pairWith_nonnegative (R : Regularizer) (π : ℝ → ℝ)
    (hπ : ∀ z, π z ∈ Icc (0 : ℝ) 1) : NonnegativePairActivation (pairWith R π) := by
  intro u v hu hv
  have hc := R.nonpos _ (hπ (u-v))
  exact ⟨sub_nonneg.mpr (hc.trans (mul_nonneg (hπ _).1 hu)), mul_nonneg (hπ _).1 hv⟩

/-- The full shared MLP, with its actual biases and arbitrary width sequence. -/
theorem network_recovery (R : Regularizer) (π : ℝ → ℝ)
    (hπ : ∀ z, π z ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (objective R z) (Icc 0 1) (π z))
    {n m : ℕ} (net : Network n m) (x : PairVec n) :
    (net.decomposeWith (pairWith R π) x).1-(net.decomposeWith (pairWith R π) x).2 =
      net.forwardWith (activation R) (x.1-x.2) :=
  net.valid_decomposition_recovery _ _ (pairWith_valid R π hπ) x

/-- The final affine output is ungated and retains its signed weight and bias. -/
theorem affine_readout_recovery (R : Regularizer) (π : ℝ → ℝ)
    (hπ : ∀ z, π z ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (objective R z) (Icc 0 1) (π z))
    {n m k : ℕ} (net : Network n m) (x : PairVec n)
    (wp wn : Matrix (Fin k) (Fin m) ℝ) (bp bn : Vec k) :
    preP wp wn (net.decomposeWith (pairWith R π) x)+bp -
      (preN wp wn (net.decomposeWith (pairWith R π) x)+bn) =
    affineLayer wp wn bp bn (net.forwardWith (activation R) (x.1-x.2)) := by
  rw [preactivation_difference, network_recovery R π hπ]

def zeroRegularizer : Regularizer where
  cost := fun _ => 0
  closed := continuous_const.continuousOn.lowerSemicontinuousOn
  convex := convexOn_const 0 (convex_Icc 0 1)
  nonpos := fun _ _ => le_rfl

/-- The author-selected hard gate: stop at zero as well as at negative values. -/
def hardGate (z : ℝ) : ℝ := if 0 < z then 1 else 0

theorem hardGate_optimal (z : ℝ) :
    hardGate z ∈ Icc (0 : ℝ) 1 ∧
      IsMaxOn (objective zeroRegularizer z) (Icc 0 1) (hardGate z) := by
  constructor
  · by_cases hz : 0 < z <;> simp [hardGate, hz]
  · intro p hp
    dsimp [objective, zeroRegularizer]
    by_cases hz : 0 < z
    · simpa [hardGate, hz] using mul_le_mul_of_nonneg_right hp.2 hz.le
    · simpa [hardGate, hz] using mul_nonpos_of_nonneg_of_nonpos hp.1 (le_of_not_gt hz)

theorem zero_activation (z : ℝ) : activation zeroRegularizer z = relu z := by
  have he : objective zeroRegularizer z (hardGate z) = activation zeroRegularizer z :=
    le_antisymm (objective_le _ _ _ (hardGate_optimal z).1)
      ((hardGate_optimal z).2 (gate_mem _ _))
  rw [← he]
  by_cases hz : 0 < z
  · simp [objective, zeroRegularizer, hardGate, hz, relu, max_eq_left hz.le]
  · simp [objective, zeroRegularizer, hardGate, hz, relu, max_eq_right (le_of_not_gt hz)]

/-- cor:freg_stop, with literal equality of the two pair activations and
stopping selected at the log-space boundary. -/
theorem zero_pair_is_stopping :
    pairWith zeroRegularizer hardGate = Thesis.StoppingDecomposition.stopPair := by
  funext z
  have hz : 0 < z.1-z.2 ↔ z.2 < z.1 := sub_pos
  by_cases h : z.2 < z.1 <;>
    simp [pairWith, hardGate, zeroRegularizer, Thesis.StoppingDecomposition.stopPair, hz, h]

/-- Negative binary entropy is an admissible regularizer. -/
def entropyRegularizer (θ : ℝ) (hθ : 0 < θ) : Regularizer where
  cost := fun p => -θ * Real.binEntropy p
  closed := (Real.binEntropy_continuous.const_mul (-θ)).continuousOn.lowerSemicontinuousOn
  convex := by
    have h := Real.strictConcave_binEntropy.concaveOn.neg.smul hθ.le
    simpa [smul_eq_mul] using h
  nonpos := fun p hp => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ.le)
    (Real.binEntropy_nonneg hp.1 hp.2)

theorem sigmoid_optimal (θ : ℝ) (hθ : 0 < θ) (z : ℝ) :
    Thesis.Regularization.gate θ z ∈ Icc (0 : ℝ) 1 ∧
    IsMaxOn (objective (entropyRegularizer θ hθ) z) (Icc 0 1)
      (Thesis.Regularization.gate θ z) := by
  refine ⟨⟨(Thesis.Regularization.gate_pos θ z).le,
    (Thesis.Regularization.gate_lt_one θ z).le⟩, ?_⟩
  intro p hp
  have h := Thesis.Regularization.entropy_policy_le_softplus θ z p hθ hp.1 hp.2
  have he := Thesis.Regularization.entropy_gate_value θ z hθ
  dsimp [objective, entropyRegularizer]
  linarith

theorem entropy_activation (θ : ℝ) (hθ : 0 < θ) (z : ℝ) :
    activation (entropyRegularizer θ hθ) z = Thesis.Regularization.softplus θ z := by
  have he : objective (entropyRegularizer θ hθ) z (Thesis.Regularization.gate θ z) =
      activation (entropyRegularizer θ hθ) z :=
    le_antisymm (objective_le _ _ _ (sigmoid_optimal θ hθ z).1)
      ((sigmoid_optimal θ hθ z).2 (gate_mem _ _))
  have hg := Thesis.Regularization.entropy_gate_value θ z hθ
  rw [← he]
  simpa only [objective, entropyRegularizer, neg_mul, sub_neg_eq_add] using hg

theorem entropy_pair_is_softSplit (θ : ℝ) (hθ : 0 < θ) (z : ℝ × ℝ) :
    pairWith (entropyRegularizer θ hθ) (Thesis.Regularization.gate θ) z =
      Thesis.Regularization.softSplit θ z.1 z.2 := by
  simp [pairWith, entropyRegularizer, Thesis.Regularization.softSplit]

/-- A bundled source-facing theorem, including the full activation claim and
the shared network's ungated affine output. -/
theorem regularized_decomposition_validity (R : Regularizer) (π : ℝ → ℝ)
    (hπ : ∀ z, π z ∈ Icc (0 : ℝ) 1 ∧ IsMaxOn (objective R z) (Icc 0 1) (π z))
    {n m k : ℕ} (net : Network n m) (x : PairVec n)
    (wp wn : Matrix (Fin k) (Fin m) ℝ) (bp bn : Vec k) :
    ValidPairActivation (activation R) (pairWith R π) ∧
    NonnegativePairActivation (pairWith R π) ∧
    ConvexOn ℝ univ (activation R) ∧ Monotone (activation R) ∧
    LipschitzWith 1 (activation R) ∧
    (∀ z, DifferentiableAt ℝ (activation R) z → π z = deriv (activation R) z) ∧
    (preP wp wn (net.decomposeWith (pairWith R π) x)+bp -
      (preN wp wn (net.decomposeWith (pairWith R π) x)+bn) =
      affineLayer wp wn bp bn (net.forwardWith (activation R) (x.1-x.2))) :=
  ⟨pairWith_valid R π hπ, pairWith_nonnegative R π (fun z => (hπ z).1),
    activation_convex R, activation_monotone R, activation_lipschitz R,
    fun z hd => optimizer_eq_deriv R z (π z) (hπ z).1 (hπ z).2 hd,
    affine_readout_recovery R π hπ net x wp wn bp bn⟩

end Thesis.GeneralRegularization
