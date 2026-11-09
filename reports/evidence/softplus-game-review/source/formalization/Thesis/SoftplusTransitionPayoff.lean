import Thesis.SoftplusSubgames

noncomputable section
namespace Thesis.SoftplusGame
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward
open Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix
open scoped BigOperators

/-- Expected next-state value under the actual normalized mixed kernel, with
cemetery value zero. This identity does not require nonzero fan-in. -/
theorem mixed_expected_value {n k} (r : Set.Icc (0 : ℝ) 1)
    (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool) (v : Bool → Vec n) :
    (∑ target : Option (Fin n × Bool),mixedTransition r wp wn j turn target*
      target.elim 0 (fun t => v t.2 t.1)) =
      r.val*∑ i,(wp j i/rowDiscount wp wn j*v turn i+
        wn j i/rowDiscount wp wn j*v (!turn) i) := by
  cases turn <;>
    simp [mixedTransition,Thesis.StoppingBoundary.transition,Fintype.sum_option,
      Fintype.sum_prod_type,Finset.mul_sum,fanIn,rowDiscount]
  all_goals
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Full source payoff equation for every profile: the continuation probability
scales the actual split bias, only the active player receives entropy, and the
remaining term is a normalized discounted transition expectation. -/
theorem playerStep_transition {n k} (θ : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (plus minus : Fin k → Set.Icc (0 : ℝ) 1) (v : PlayerValues n)
    (player turn : Bool) (j : Fin k) :
    let r := if turn then minus j else plus j
    playerStep θ wp wn bp bn plus minus v player turn j =
      r.val*(if player=turn then bp j else bn j)+
      (if player=turn then θ*Real.binEntropy r.val else 0)+
      rowDiscount wp wn j*∑ target : Option (Fin n × Bool),
        mixedTransition r wp wn j turn target*target.elim 0 (fun t => v player t.2 t.1) := by
  dsimp only
  rw [mixed_expected_value]
  cases player <;> cases turn <;>
    simp [playerStep,playerContinuation,continuation] <;> ring

end Thesis.SoftplusGame
