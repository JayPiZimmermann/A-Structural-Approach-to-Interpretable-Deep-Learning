import Thesis.SoftplusBackward
import HiddenMonotonicity.Decomposition

/-! The smooth game and the common neuron-pair decomposition interface evaluate
exactly the same `Network` parameters; this file supplies the explicit bridge. -/
noncomputable section
namespace Thesis.SoftplusDecomposition
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward

theorem softEval_eq_forwardWith {n m} (net : Network n m) (θ : ℝ) :
    softEval θ net = net.forwardWith (softplus θ) := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      funext x
      simp only [softEval, Network.forwardWith, ih]
      rfl

/-- Thesis `ptnb:thm:softplus-forward`, decomposition-recovery part, over the full MLP. -/
theorem thesis_softplus_forward {n m} (net : Network n m) (θ : ℝ) (hθ : 0 < θ)
    (x : PairVec n) :
    (net.decomposeWith (fun z => softSplit θ z.1 z.2) x).1 -
      (net.decomposeWith (fun z => softSplit θ z.1 z.2) x).2 = softEval θ net (x.1-x.2) := by
  rw [softEval_eq_forwardWith]
  apply net.valid_decomposition_recovery
  intro p q
  exact softSplit_recovery θ p q hθ

end Thesis.SoftplusDecomposition
