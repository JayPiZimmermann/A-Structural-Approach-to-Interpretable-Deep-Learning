import Thesis.RoutingBackward
import Thesis.AffineOutputBackward

/-! Bridge to the source's ungated alpha-beta recurrence. Ordinary output seeds
vanish at zero activations. Under exactly this support condition the source
recurrence and the stopping-gated recurrence agree, including empty streams with
the real-division convention 0/0=0. -/
noncomputable section
namespace Thesis.RoutingSupport
open HiddenMonotonicity Matrix Finset Thesis.RoutingBackward

def sourceLayer {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k)
    (α β ε : ℝ) (x : Vec n) : Matrix (Fin k) (Fin n) ℝ := fun j i =>
  α * posContribution wp wn x j i / posDenominator wp wn bp bn ε x j -
    β * negContribution wp wn x j i / negDenominator wp wn bp bn ε x j

def sourceLRP {n m} (α β ε : ℝ) : (net : Network n m) → Vec n → Vec m → Vec n
  | .output _, _, R => R
  | .layer wp wn bp bn tail, x, R =>
      sourceLRP α β ε tail (fun j => relu (preactivation wp wn bp bn x j)) R ᵥ*
        sourceLayer wp wn bp bn α β ε x

theorem sourceLayer_zero_input {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (α β ε : ℝ) (x : Vec n) (j : Fin k) (i : Fin n) (hx : x i = 0) :
    sourceLayer wp wn bp bn α β ε x j i = 0 := by
  simp [sourceLayer, posContribution, negContribution, hx]

theorem sourceLRP_zero_input {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (R : Vec m) (hR : ∀ j, net.eval x j = 0 → R j = 0)
    (i : Fin n) (hx : x i = 0) : sourceLRP α β ε net x R i = 0 := by
  cases net with
  | output n => exact hR i hx
  | layer wp wn bp bn tail =>
      change (∑ j, sourceLRP α β ε tail
        (fun j => relu (preactivation wp wn bp bn x j)) R j *
        sourceLayer wp wn bp bn α β ε x j i) = 0
      simp [sourceLayer_zero_input wp wn bp bn α β ε x _ i hx]

/-- The literal source recurrence agrees with the gated recurrence on supported seeds. -/
theorem sourceLRP_eq_lrp {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (R : Vec m) (hR : ∀ j, net.eval x j = 0 → R j = 0) :
    sourceLRP α β ε net x R = lrp α β ε net x R := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      have htR : ∀ j, tail.eval (fun j => relu (preactivation wp wn bp bn x j)) j = 0 → R j = 0 := hR
      simp only [sourceLRP, lrp]
      rw [← ih _ R htR]
      funext i
      change (∑ j, sourceLRP α β ε tail
        (fun j => relu (preactivation wp wn bp bn x j)) R j *
        sourceLayer wp wn bp bn α β ε x j i) =
        ∑ j, sourceLRP α β ε tail (fun j => relu (preactivation wp wn bp bn x j)) R j *
          lrpLayer wp wn bp bn α β ε x j i
      apply Finset.sum_congr rfl
      intro j _
      by_cases hz : 0 < preactivation wp wn bp bn x j
      · simp [sourceLayer, lrpLayer, hz]
      · have ha : relu (preactivation wp wn bp bn x j) = 0 :=
          max_eq_right (le_of_not_gt hz)
        have hzero := sourceLRP_zero_input tail α β ε
          (fun j => relu (preactivation wp wn bp bn x j)) R htR j ha
        simp [hzero]

/-- Source alpha-beta recovery, with its actual recurrence and explicit seed support. -/
theorem source_alpha_beta_recovery {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (R : Vec m) (hR : ∀ j, net.eval x j = 0 → R j = 0) (i : Fin n) :
    sourceLRP α β ε net x R i = ∑ j, R j *
      (rgOccupation net α β ε x j i false - rgOccupation net α β ε x j i true) := by
  rw [sourceLRP_eq_lrp net α β ε x R hR]
  exact thesis_alpha_beta_recovery net α β ε x R i

theorem source_alpha_beta_output_seed {n m} (net : Network n m) (α β ε : ℝ)
    (x : Vec n) (i : Fin n) :
    sourceLRP α β ε net x (net.eval x) i = ∑ j, net.eval x j *
      (rgOccupation net α β ε x j i false - rgOccupation net α β ε x j i true) :=
  source_alpha_beta_recovery net α β ε x (net.eval x) (fun _ h => h) i

/-- An ungated affine readout followed by the literal ungated source recurrence. -/
def sourceAffineOutputLRP {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (α β ε : ℝ) (x : Vec n) (R : Vec r) : Vec n :=
  sourceLRP α β ε net x (R ᵥ* Thesis.AttentionBackward.affineRule C b α β ε (net.eval x))

/-- The affine readout automatically gives zero relevance to zero backbone activations. -/
theorem sourceAffineOutputLRP_eq {n m r} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ) (x : Vec n) (R : Vec r) :
    sourceAffineOutputLRP net C b α β ε x R =
      Thesis.AffineOutputBackward.affineOutputLRP net C b α β ε x R := by
  apply sourceLRP_eq_lrp
  intro j hj
  simp [Matrix.vecMul, dotProduct, Thesis.AttentionBackward.affineRule,
    posContribution, negContribution, hj]

/-- Source recurrence recovery with a genuine ungated signed affine output. -/
theorem source_affine_output_lrp {n m r} (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α β ε : ℝ)
    (x : Vec n) (R : Vec r) (i : Fin n) :
    sourceAffineOutputLRP net C b α β ε x R i = ∑ u, R u *
      (Thesis.AffineOutputBackward.readoutOccupation net C b α β ε x u i false -
       Thesis.AffineOutputBackward.readoutOccupation net C b α β ε x u i true) := by
  rw [sourceAffineOutputLRP_eq]
  exact Thesis.AffineOutputBackward.thesis_affine_output_lrp net C b α β ε x R i

end Thesis.RoutingSupport
