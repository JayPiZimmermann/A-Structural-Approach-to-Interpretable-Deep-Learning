import Thesis.AttentionBackward
import HiddenMonotonicity.OriginalTrace

/-! Ungated final affine readouts. These wrappers avoid treating a target logit
as another ReLU and retain arbitrary signed readout rows and readout biases. -/
noncomputable section
namespace Thesis.AffineOutputBackward
open HiddenMonotonicity Matrix Finset Thesis.BackwardGames Thesis.RoutingBackward Thesis.AttentionBackward

theorem originalJac_sg_coordinate {n m} (tr : MaskedTrace n m)
    (hγ : PositiveFanIn tr) (j : Fin m) (i : Fin n) :
    tr.originalJac (Pi.single i 1) j = sgOccupation tr j i false - sgOccupation tr j i true := by
  simp only [sgOccupation, sg_path_discount_recovery tr hγ]
  exact originalJac_coordinate_paths tr j i

def affineOutput {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (x : Vec n) : Vec r := C.mulVec (net.eval x) + b

theorem affineOutput_hasFDerivAt {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (x : Vec n) (hx : net.Strict x) :
    HasFDerivAt (affineOutput net C b) ((matrixCLM C).comp (net.originalTrace x).originalJac) x :=
  ((matrixCLM C).hasFDerivAt.comp x (net.hasFDerivAt_originalTrace x hx)).add_const b

/-- The SG gradient representation with the source paper's actual affine logit. -/
theorem thesis_affine_output_gradient {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (x : Vec n) (hx : net.Strict x) (hγ : PositiveFanIn (net.originalTrace x))
    (u : Fin r) (i : Fin n) :
    fderiv ℝ (affineOutput net C b) x (Pi.single i 1) u =
      ∑ j, C u j * (sgOccupation (net.originalTrace x) j i false -
        sgOccupation (net.originalTrace x) j i true) := by
  rw [(affineOutput_hasFDerivAt net C b x hx).fderiv]
  change (∑ j, C u j * (net.originalTrace x).originalJac (Pi.single i 1) j) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [originalJac_sg_coordinate _ hγ j i]

/-- A final ungated affine alpha-beta layer, followed by complete backbone LRP. -/
def affineOutputLRP {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (α β ε : ℝ) (x : Vec n) (R : Vec r) : Vec n :=
  lrp α β ε net x (R ᵥ* affineRule C b α β ε (net.eval x))

def readoutPos {m r} (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (α ε : ℝ)
    (a : Vec m) (u : Fin r) (j : Fin m) : ℝ :=
  α * posContribution C 0 a u j / posDenominator C 0 b 0 ε a u

def readoutNeg {m r} (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (β ε : ℝ)
    (a : Vec m) (u : Fin r) (j : Fin m) : ℝ :=
  β * negContribution C 0 a u j / negDenominator C 0 b 0 ε a u

/-- Concatenated discounted occupation: the affine readout can preserve or switch parity. -/
def readoutOccupation {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (α β ε : ℝ) (x : Vec n) (u : Fin r) (i : Fin n) (p : Bool) : ℝ :=
  ∑ j, (readoutPos C b α ε (net.eval x) u j * rgOccupation net α β ε x j i p +
    readoutNeg C b β ε (net.eval x) u j * rgOccupation net α β ε x j i (!p))

/-- Complete source-facing LRP recovery including an ungated signed affine logit. -/
theorem thesis_affine_output_lrp {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (α β ε : ℝ) (x : Vec n) (R : Vec r) (i : Fin n) :
    affineOutputLRP net C b α β ε x R i = ∑ u, R u *
      (readoutOccupation net C b α β ε x u i false -
       readoutOccupation net C b α β ε x u i true) := by
  rw [affineOutputLRP, thesis_alpha_beta_recovery]
  simp only [Matrix.vecMul, dotProduct]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [readoutOccupation, Bool.not_false, Bool.not_true,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [affineRule, readoutPos, readoutNeg]
  ring

theorem readoutOccupation_nonneg {n m r} (net : Network n m) (C : Matrix (Fin r) (Fin m) ℝ)
    (b : Vec r) (α β ε : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 < ε)
    (x : Vec n) (u : Fin r) (i : Fin n) (p : Bool) :
    0 ≤ readoutOccupation net C b α β ε x u i p := by
  unfold readoutOccupation
  apply Finset.sum_nonneg
  intro j _
  apply add_nonneg
  · apply mul_nonneg _ (rgOccupation_nonneg net α β ε hα hβ hε x j i p)
    exact div_nonneg (mul_nonneg hα (le_max_right _ _)) (posDenominator_pos C 0 b 0 ε hε _ _).le
  · apply mul_nonneg _ (rgOccupation_nonneg net α β ε hα hβ hε x j i (!p))
    exact div_nonneg (mul_nonneg hβ (le_max_right _ _)) (negDenominator_pos C 0 b 0 ε hε _ _).le

end Thesis.AffineOutputBackward
