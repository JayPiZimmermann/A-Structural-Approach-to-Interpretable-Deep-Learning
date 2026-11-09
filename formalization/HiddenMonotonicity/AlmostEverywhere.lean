import HiddenMonotonicity.DifferentiableHeads
import Mathlib.Analysis.Calculus.Rademacher

namespace HiddenMonotonicity
open MeasureTheory

/-- Global Lipschitz regularity of the actual max/affine layer. -/
theorem layerFun_lipschitz {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) : ∃ C, LipschitzWith C (layerFun wp wn bp bn) := by
  have hp := (preP wp wn).lipschitz.add (LipschitzWith.const bp)
  have hn := (preN wp wn).lipschitz.add (LipschitzWith.const bn)
  have hm : LipschitzWith (max (‖preP wp wn‖₊+0) (‖preN wp wn‖₊+0))
      (fun x i => max ((preP wp wn x+bp) i) ((preN wp wn x+bn) i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
    intro i
    have hi := ((LipschitzWith.eval i).comp hp).max ((LipschitzWith.eval i).comp hn)
    simpa only [one_mul, Function.comp_apply, Function.eval] using hi.dist_le_mul x y
  exact ⟨_, hm.prodMk hn⟩

theorem Network.split_lipschitz {n m} (net : Network n m) :
    ∃ C, LipschitzWith C (fun x : PairVec n => net.split x.1 x.2) := by
  induction net with
  | output n => exact ⟨1,LipschitzWith.id⟩
  | layer wp wn bp bn tail ih =>
      obtain ⟨C,hC⟩ := ih
      obtain ⟨D,hD⟩ := layerFun_lipschitz wp wn bp bn
      refine ⟨C*D, ?_⟩
      have he : (fun x : PairVec _ => (Network.layer wp wn bp bn tail).split x.1 x.2) =
          (fun x : PairVec _ => tail.split x.1 x.2) ∘ layerFun wp wn bp bn := by
        funext x
        rfl
      rw [he]
      exact hC.comp hD

theorem Network.affine_heads_lipschitz {n m} (net : Network n m)
    (rp rn : Row m) (bp bn : ℝ) :
    ∃ C, LipschitzWith C (fun x => net.affineHeads rp rn bp bn (balancedLift n x)) := by
  obtain ⟨C,hC⟩ := net.split_lipschitz
  have ho := (((assemble (rp,rn)).prod (assemble (rn,rp))).lipschitz.add
    (LipschitzWith.const (bp,bn))).comp (hC.comp (balancedLift n).lipschitz)
  refine ⟨(‖(assemble (rp,rn)).prod (assemble (rn,rp))‖₊+0)*(C*‖balancedLift n‖₊), ?_⟩
  simpa [Network.affineHeads, Function.comp_def, assemble] using ho

/-- Almost-everywhere actual head gradients, including networks with identically
zero internal preactivations. No strict-gate hypothesis is used. -/
theorem Network.affine_heads_ae_derivatives {n m} (net : Network n m)
    (hw : net.Nonnegative) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn)
    (bp bn : ℝ) :
    ∀ᵐ x : Vec n, ∀ head : Bool,
      HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn (balancedLift n y)).1
        else (net.affineHeads rp rn bp bn (balancedLift n y)).2)
        (unified ((net.originalTrace x).run (fun _ => 0)
          (affineReadoutSeed rp rn 0 head))) x := by
  obtain ⟨C,hC⟩ := net.affine_heads_lipschitz rp rn bp bn
  filter_upwards [hC.ae_differentiableAt (μ := volume)] with x hx
  intro head
  apply net.affine_symmetric_derivative_of_differentiable hw x rp rn hp hn bp bn head
  cases head
  · exact hx.snd
  · exact hx.fst

/-- Actual affine-logit derivatives and both partial invariants hold almost
everywhere, simultaneously for all fixed backward shifts. -/
theorem Network.affine_ae_backward_invariants {n m} (net : Network n m)
    (hw : net.Nonnegative) (rp rn : Row m) (hp : Monotone rp) (hn : Monotone rn)
    (bp bn : ℝ) :
    ∀ᵐ x : Vec n, ∀ (α : ℕ → ℝ) (β : ℝ),
      HasFDerivAt (net.affineLogit rp rn bp bn) ((rp-rn).comp (net.originalTrace x).originalJac) x ∧
      ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).1-
        ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).1 =
        (rp-rn).comp (net.originalTrace x).originalJac ∧
      ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).2-
        ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).2 =
        -((rp-rn).comp (net.originalTrace x).originalJac) := by
  obtain ⟨C,hC⟩ := net.affine_heads_lipschitz rp rn bp bn
  filter_upwards [hC.ae_differentiableAt (μ := volume)] with x hx
  exact net.affine_backward_invariants_of_differentiable hw x rp rn hp hn bp bn hx.fst hx.snd

end HiddenMonotonicity
