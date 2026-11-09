import HiddenMonotonicity.Convolution
import Mathlib.Tactic

/- Independent semantic checks. These are small concrete consumers of the
literal tensor evaluator, not evaluations of the matrix bridge theorem. -/
noncomputable section
open HiddenMonotonicity HiddenMonotonicity.Convolution Matrix

namespace ConvolutionReview

def repeatedKernel : Fin 1 → Fin 1 → Fin 2 → ℝ := fun _ _ t => if t = 0 then 1 else -1
def repeatedStencil : Fin 1 → Fin 2 → Option (Fin 1) := fun _ _ => some 0

/-- Opposite taps at one input site cancel in the ordinary matrix. -/
example : kernelMatrix repeatedKernel repeatedStencil 0 0 = 0 := by
  norm_num [kernelMatrix, repeatedKernel, repeatedStencil, unflat,
    finProdFinEquiv, Fin.modNat, Fin.divNat, Fin.sum_univ_two]

/-- Kernel signs are split before aggregation: the positive matrix is not
the positive part of the already aggregated ordinary matrix. -/
example : kernelMatrix (positiveKernel repeatedKernel) repeatedStencil 0 0 = 1 := by
  norm_num [kernelMatrix, positiveKernel, repeatedKernel, repeatedStencil, unflat,
    finProdFinEquiv, Fin.modNat, Fin.divNat, Fin.sum_univ_two]

example : kernelMatrix (negativeKernel repeatedKernel) repeatedStencil 0 0 = 1 := by
  norm_num [kernelMatrix, negativeKernel, repeatedKernel, repeatedStencil, unflat,
    finProdFinEquiv, Fin.modNat, Fin.divNat, Fin.sum_univ_two]

example (p q : ℝ) :
    (splitKernel repeatedKernel repeatedStencil (fun _ => -3)
      ((fun _ => p), (fun _ => q))).1 0 = p + q ∧
    (splitKernel repeatedKernel repeatedStencil (fun _ => -3)
      ((fun _ => p), (fun _ => q))).2 0 = q + p + 3 := by
  norm_num [splitKernel, applyKernel, positiveKernel, negativeKernel,
    repeatedKernel, repeatedStencil, sample, unflat, finProdFinEquiv,
    Fin.modNat, Fin.divNat, Fin.sum_univ_two, add_comm]

def channelsKernel : Fin 1 → Fin 2 → Fin 2 → ℝ :=
  fun _ c t => if c = 0 then (if t = 0 then 1 else 2)
    else (if t = 0 then 3 else 4)
def channelsStencil : Fin 2 → Fin 2 → Option (Fin 2) :=
  fun o t => if o = 0 then (if t = 0 then some 0 else none)
    else (if t = 0 then some 0 else some 1)
def channelsInput : Vec (2*2) := ![1,2,3,4]

/-- Channel-major flattening: first row samples the first position from
both channels and zero-pads the second tap. The second row uses both taps.
The same channel kernel and output bias are shared across the two rows. -/
example :
    applyKernel channelsKernel channelsStencil channelsInput 0 - 5 = 5 ∧
    applyKernel channelsKernel channelsStencil channelsInput 1 - 5 = 25 := by
  norm_num [applyKernel, channelsKernel, channelsStencil, channelsInput,
    sample, flat, unflat, finProdFinEquiv, Fin.modNat, Fin.divNat, Fin.sum_univ_two]

example (K : Fin 2 → Fin 0 → Fin 3 → ℝ)
    (s : Fin 4 → Fin 3 → Option (Fin 5)) (x : Vec (0*5)) :
    applyKernel K s x = 0 := by
  funext u
  simp [applyKernel]

example (K : Fin 2 → Fin 3 → Fin 0 → ℝ)
    (s : Fin 4 → Fin 0 → Option (Fin 5)) (x : Vec (3*5)) :
    applyKernel K s x = 0 := by
  funext u
  simp [applyKernel]

/-- No input positions forces every well-typed sample to be padding. -/
example (K : Fin 2 → Fin 3 → Fin 2 → ℝ)
    (s : Fin 4 → Fin 2 → Option (Fin 0)) (x : Vec (3*0)) :
    applyKernel K s x = 0 := by
  funext u
  simp only [applyKernel, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro c _
  apply Finset.sum_eq_zero
  intro t _
  have hs : s (unflat u).2 t = none := by
    cases h : s (unflat u).2 t with
    | none => rfl
    | some j => exact Fin.elim0 j
  simp [hs, sample]

example (K : Fin 0 → Fin 3 → Fin 2 → ℝ)
    (s : Fin 4 → Fin 2 → Option (Fin 5)) (b : Fin 0 → ℝ)
    (x : PairVec (3*5)) : splitKernel K s b x = (0,0) := by
  apply Prod.ext <;> funext u <;> exact Fin.elim0 u

end ConvolutionReview
