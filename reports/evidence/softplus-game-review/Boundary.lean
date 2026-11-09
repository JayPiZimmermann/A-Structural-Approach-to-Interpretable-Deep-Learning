import Thesis.SoftplusTransitionPayoff
noncomputable section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward
open Thesis.ReLUNetGame Thesis.SoftplusGame Thesis.RoutingBackward Matrix
open scoped BigOperators

def halfProbability : Set.Icc (0 : ℝ) 1 := ⟨1/2,by norm_num⟩
def stopProbability : Set.Icc (0 : ℝ) 1 := ⟨0,by norm_num⟩

-- Every real-temperature binary Gibbs value is a probability, and zero score
-- is exactly one half, including the zero-fan-in positive-temperature game.
example : (gibbsProbability 1 0).val=1/2 := by
  norm_num [gibbsProbability,gate,Real.sigmoid]
example : mixedTransition halfProbability (0 : Matrix (Fin 1) (Fin 0) ℝ) 0 0 false none=1 := by
  apply mixed_zero_fanIn_absorbs
  simp [Thesis.BackwardGames.fanIn]

-- Cemetery continuation still pays the continuation-scaled bias, and only
-- the active player receives the actual binary entropy bonus.
example : playerStep 1 (0 : Matrix (Fin 1) (Fin 0) ℝ) 0 (fun _ => 2) (fun _ => 1)
    (fun _ => halfProbability) (fun _ => halfProbability) (fun _ _ => 0) false false 0 =
      1+Real.binEntropy (1/2) := by
  norm_num [playerStep,playerContinuation,continuation,rowDiscount,halfProbability]
example : playerStep 1 (0 : Matrix (Fin 1) (Fin 0) ℝ) 0 (fun _ => 2) (fun _ => 1)
    (fun _ => halfProbability) (fun _ => halfProbability) (fun _ _ => 0) true false 0 =1/2 := by
  norm_num [playerStep,playerContinuation,continuation,rowDiscount,halfProbability]

def zeroNet : Network 0 1 := .layer 0 0 0 0 (.output 1)
theorem zeroNet_nonnegative : zeroNet.Nonnegative := by
  constructor
  · intro j i; simp
  constructor
  · intro j i; simp
  · trivial

def stopProfile : Strategy zeroNet := (fun _ => stopProbability,())
example : SubgamePerfect 1 zeroNet (gibbsStrategy 1 zeroNet 0) (gibbsStrategy 1 zeroNet 0) 0 0 := by
  simpa using gibbs_subgamePerfect zeroNet 1 (by norm_num) zeroNet_nonnegative 0
example : ¬SubgamePerfect 1 zeroNet stopProfile stopProfile 0 0 := by
  intro h
  have hh := (subgamePerfect_iff zeroNet 1 (by norm_num) zeroNet_nonnegative 0 stopProfile stopProfile).mp (by simpa using h)
  have he := congrArg (fun p : Strategy zeroNet => (p.1 0).val) hh.1
  change (0 : ℝ) = (gibbsProbability 1 (preactivation (0 : Matrix (Fin 1) (Fin 0) ℝ) 0 0 0 0 0)).val at he
  norm_num [gibbsProbability,gate,preactivation,Real.sigmoid,Matrix.mulVec,dotProduct] at he

-- Actual forced signed affine output remains negative and retains its bias.
example : affineOutput 1 (Network.output 1) (fun (_ : Fin 1) (_ : Fin 1) => (-2 : ℝ)) (fun _ => -3) (fun _ => 2) 0 = -7 := by
  norm_num [affineOutput,softEval,Matrix.mulVec,dotProduct]

-- Both pure endpoint actions occur in the deviation strategy space.
example : (stopProbability : ℝ)=0 := rfl
example : ∃ p : Set.Icc (0 : ℝ) 1,p.val=1 := ⟨⟨1,by norm_num⟩,rfl⟩
end
