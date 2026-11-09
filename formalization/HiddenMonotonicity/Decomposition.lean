import HiddenMonotonicity.OriginalTrace
import HiddenMonotonicity.Chunks
import HiddenMonotonicity.Convexity

namespace HiddenMonotonicity
open Matrix

/-- Evaluate the same finite MLP parameters with an arbitrary scalar activation. -/
noncomputable def Network.forwardWith {n m} : Network n m → (ℝ → ℝ) → Vec n → Vec m
  | .output _, _, x => x
  | .layer wp wn bp bn tail, σ, x =>
      tail.forwardWith σ (fun i => σ (affineLayer wp wn bp bn x i))

/-- A neuron-local pair activation, used consistently on the same MLP parameters. -/
noncomputable def Network.decomposeWith {n m} : Network n m → ((ℝ × ℝ) → ℝ × ℝ) →
    PairVec n → PairVec m
  | .output _, _, x => x
  | .layer wp wn bp bn tail, φ, x =>
      tail.decomposeWith φ
        ((fun i => (φ ((preP wp wn x+bp) i,(preN wp wn x+bn) i)).1),
         (fun i => (φ ((preP wp wn x+bp) i,(preN wp wn x+bn) i)).2))

/-- The scalar difference identity required of a valid pair activation. -/
def ValidPairActivation (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ) : Prop :=
  ∀ p q, (φ (p,q)).1-(φ (p,q)).2=σ (p-q)

/-- Thesis prop:validity_recovery: local validity implies full network recovery,
for every finite width sequence, activation function, and split biases. -/
theorem Network.valid_decomposition_recovery {n m} (net : Network n m)
    (σ : ℝ → ℝ) (φ : (ℝ × ℝ) → ℝ × ℝ) (hv : ValidPairActivation σ φ) (x : PairVec n) :
    (net.decomposeWith φ x).1-(net.decomposeWith φ x).2=net.forwardWith σ (x.1-x.2) := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [Network.decomposeWith, Network.forwardWith]
      rw [ih]
      congr 1
      funext i
      change (φ ((preP wp wn x+bp) i,(preN wp wn x+bn) i)).1-
        (φ ((preP wp wn x+bp) i,(preN wp wn x+bn) i)).2 = _
      rw [hv]
      have he := congrFun (preactivation_difference wp wn bp bn x) i
      exact congrArg σ he

theorem Network.forwardWith_relu {n m} (net : Network n m) : net.forwardWith relu=net.eval := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih => simp only [Network.forwardWith, Network.eval, ih]; rfl

noncomputable def mixPair (η : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (η*max x.1 x.2+(1-η)*x.1,η*x.2+(1-η)*min x.1 x.2)

theorem mixPair_valid (η : ℝ) : ValidPairActivation relu (mixPair η) := by
  intro p q
  exact mixing_correct p q η

/-- Thesis thm:mixing_recovery, for the full network, every layer width and all biases.
Arithmetic recovery holds for every η; [0,1] is required only for nonnegativity. -/
theorem Network.mixing_recovery {n m} (net : Network n m) (η : ℝ) (x : PairVec n) :
    (net.decomposeWith (mixPair η) x).1-(net.decomposeWith (mixPair η) x).2 =
      net.eval (x.1-x.2) := by
  rw [← net.forwardWith_relu]
  exact net.valid_decomposition_recovery relu _ (mixPair_valid η) x

/-- η=1 is exactly the established DC split, not merely a related construction. -/
theorem Network.mixing_one_is_split {n m} (net : Network n m) (x : PairVec n) :
    net.decomposeWith (mixPair 1) x=net.split x.1 x.2 := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [Network.decomposeWith, mixPair, one_mul, sub_self, zero_mul, add_zero,
        Network.split]
      exact ih _

def NonnegativePairActivation (φ : (ℝ × ℝ) → ℝ × ℝ) : Prop :=
  ∀ p q, 0≤p → 0≤q → 0≤(φ (p,q)).1 ∧ 0≤(φ (p,q)).2

def Network.NonnegativeParameters {n m} : Network n m → Prop
  | .output _ => True
  | .layer wp wn bp bn tail => (∀ i j, 0≤wp i j ∧ 0≤wn i j) ∧
      (∀ i, 0≤bp i ∧ 0≤bn i) ∧ tail.NonnegativeParameters

theorem Network.decomposition_nonnegative {n m} (net : Network n m)
    (hp : net.NonnegativeParameters) (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hφ : NonnegativePairActivation φ) (x : PairVec n) (hx : 0≤x.1 ∧ 0≤x.2) :
    0≤(net.decomposeWith φ x).1 ∧ 0≤(net.decomposeWith φ x).2 := by
  induction net with
  | output n => exact hx
  | layer wp wn bp bn tail ih =>
      apply ih hp.2.2
      constructor <;> intro i
      · apply (hφ _ _ ?_ ?_).1
        · change 0≤(wp.mulVec x.1+wn.mulVec x.2+bp) i
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
          exact add_nonneg (add_nonneg
            (Finset.sum_nonneg (fun j _ => mul_nonneg (hp.1 i j).1 (hx.1 j)))
            (Finset.sum_nonneg (fun j _ => mul_nonneg (hp.1 i j).2 (hx.2 j)))) (hp.2.1 i).1
        · change 0≤(wn.mulVec x.1+wp.mulVec x.2+bn) i
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
          exact add_nonneg (add_nonneg
            (Finset.sum_nonneg (fun j _ => mul_nonneg (hp.1 i j).2 (hx.1 j)))
            (Finset.sum_nonneg (fun j _ => mul_nonneg (hp.1 i j).1 (hx.2 j)))) (hp.2.1 i).2
      · apply (hφ _ _ ?_ ?_).2
        · change 0≤(wp.mulVec x.1+wn.mulVec x.2+bp) i
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
          exact add_nonneg (add_nonneg
            (Finset.sum_nonneg (fun j _ => mul_nonneg (hp.1 i j).1 (hx.1 j)))
            (Finset.sum_nonneg (fun j _ => mul_nonneg (hp.1 i j).2 (hx.2 j)))) (hp.2.1 i).1
        · change 0≤(wn.mulVec x.1+wp.mulVec x.2+bn) i
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
          exact add_nonneg (add_nonneg
            (Finset.sum_nonneg (fun j _ => mul_nonneg (hp.1 i j).2 (hx.1 j)))
            (Finset.sum_nonneg (fun j _ => mul_nonneg (hp.1 i j).1 (hx.2 j)))) (hp.2.1 i).2

theorem mixPair_nonnegative (η : ℝ) (hη : 0≤η) (hη' : η≤1) :
    NonnegativePairActivation (mixPair η) := by
  intro p q hp hq
  constructor
  · exact add_nonneg (mul_nonneg hη (le_trans hp (le_max_left p q)))
      (mul_nonneg (sub_nonneg.mpr hη') hp)
  · exact add_nonneg (mul_nonneg hη hq)
      (mul_nonneg (sub_nonneg.mpr hη') (le_min hp hq))

end HiddenMonotonicity
