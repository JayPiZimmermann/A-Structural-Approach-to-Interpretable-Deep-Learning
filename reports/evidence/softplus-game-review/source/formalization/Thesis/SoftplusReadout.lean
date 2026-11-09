import Thesis.SoftplusPlayerValues

noncomputable section
namespace Thesis.SoftplusGame
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward
open Thesis.ReLUNetGame Thesis.RoutingBackward Matrix
open scoped BigOperators

/-- A forced affine output, with no sigmoid policy or entropy bonus at readout. -/
def affineOutput {n m r} (θ : ℝ) (net : Network n m)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (x : Vec n) : Vec r :=
  C *ᵥ softEval θ net x+b

theorem affine_saddle {n m r} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net)
    (wp wn : Matrix (Fin r) (Fin m) ℝ) (hrow : ∀ j i,0≤wp j i ∧ 0≤wn j i)
    (b : Vec r) (j : Fin r) :
    let read := fun v : PairVec m => continuation wp wn b v.1 v.2 j
    read (policyValue θ net plus (gibbsStrategy θ net x) x (-x))≤affineOutput θ net (wp-wn) b x j ∧
    read (policyValue θ net (gibbsStrategy θ net x) (gibbsStrategy θ net x) x (-x))=
      affineOutput θ net (wp-wn) b x j ∧
    affineOutput θ net (wp-wn) b x j≤read (policyValue θ net (gibbsStrategy θ net x) minus x (-x)) := by
  dsimp only
  have hs := softplus_saddle net θ hθ hw x plus minus
  have he : continuation wp wn b (softEval θ net x) (-softEval θ net x) j=
      affineOutput θ net (wp-wn) b x j := by
    rw [continuation_recovery_total wp wn hrow]
    simp only [affineOutput,Matrix.sub_mulVec,Matrix.mulVec_neg]
    rfl
  refine ⟨?_,?_,?_⟩
  · rw [← he]
    exact continuation_mono_total wp wn hrow b hs.1 hs.2.1 j
  · rw [hs.2.2.1]
    exact he
  · rw [← he]
    exact continuation_mono_total wp wn hrow b hs.2.2.2.1 hs.2.2.2.2 j

theorem affineOutput_hasFDerivAt {n m r} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (x : Vec n) :
    HasFDerivAt (affineOutput θ net C b)
      ((matrixCLM C).comp (softTrace θ net x).originalJac) x := by
  exact ((matrixCLM C).hasFDerivAt.comp x (softEval_hasFDerivAt net θ hθ x)).add_const b

/-- Under the unique SPNE the ordinary signed affine logit derivative is the
signed weighted occupation difference, including all zero-fan-in neurons. -/
theorem spne_affine_gradient {n m r} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net)
    (hsp : SubgamePerfect θ net plus minus x (-x))
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (j : Fin r) (i : Fin n) :
    plus=gibbsStrategy θ net x ∧ minus=gibbsStrategy θ net x ∧
      fderiv ℝ (affineOutput θ net C b) x (Pi.single i 1) j=
        ∑ h,C j h*(softOccupation net θ x h i false-softOccupation net θ x h i true) := by
  have hs := (subgamePerfect_iff net θ hθ hw x plus minus).mp hsp
  refine ⟨hs.1,hs.2,?_⟩
  rw [(affineOutput_hasFDerivAt net θ hθ C b x).fderiv]
  change (∑ h,C j h*(softTrace θ net x).originalJac (Pi.single i 1) h)=_
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  rw [← (softEval_hasFDerivAt net θ hθ x).fderiv]
  exact Thesis.SoftplusBoundary.gradient_occupation net θ hθ hw x h i

/-- Source forward theorem: full-game existence and uniqueness plus the actual
player-specific decomposition coordinates, not merely arithmetic pair recovery. -/
theorem softplus_forward_spne {n m} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x : PairVec n) :
    SubgamePerfect θ net (gibbsStrategy θ net (x.1-x.2)) (gibbsStrategy θ net (x.1-x.2))
      (x.1-x.2) (-(x.1-x.2)) ∧
    (∀ plus minus : Strategy net,SubgamePerfect θ net plus minus (x.1-x.2) (-(x.1-x.2)) ↔
      plus=gibbsStrategy θ net (x.1-x.2) ∧ minus=gibbsStrategy θ net (x.1-x.2)) ∧
    playerValue θ net (gibbsStrategy θ net (x.1-x.2)) (gibbsStrategy θ net (x.1-x.2)) (pairValues x)=
      pairValues (net.decomposeWith (fun z => softSplit θ z.1 z.2) x) ∧
    (net.decomposeWith (fun z => softSplit θ z.1 z.2) x).1-
      (net.decomposeWith (fun z => softSplit θ z.1 z.2) x).2=softEval θ net (x.1-x.2) := by
  exact ⟨gibbs_subgamePerfect net θ hθ hw _,subgamePerfect_iff net θ hθ hw _,
    playerValue_gibbs net θ hθ hw x,
    Thesis.SoftplusDecomposition.thesis_softplus_forward net θ hθ x⟩

end Thesis.SoftplusGame
