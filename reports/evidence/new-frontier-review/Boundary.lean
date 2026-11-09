import HiddenMonotonicity.DistributionalRegularity
import HiddenMonotonicity.ModernActivationCorollary
import Thesis.RoutingNetwork
import Thesis.StoppingPaths
import Thesis.StoppingCircuit

noncomputable section
open HiddenMonotonicity HiddenMonotonicity.SmoothDC
open Thesis.RoutingExtended Thesis.RoutingProfiles Thesis.RoutingNetwork
open Thesis.StoppingStructure Thesis.StoppingCircuit
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

-- Primitive weak regularity is exactly a test identity, not a reconstruction hypothesis.
example (f q : ℝ → ℝ) : HasSecondDistributionalDerivative f q ↔
    LocallyIntegrable f ∧ LocallyIntegrable q ∧
      ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ x, f x * deriv (deriv φ) x) = ∫ x, q x * φ x := Iff.rfl

-- Nontrivial, non-globally-integrable curvature is allowed by the weak local bridge.
example : HasSecondDistributionalDerivative
    (localPrimitive (localPrimitive (fun _ : ℝ => (1 : ℝ)))) (fun _ => 1) :=
  localPrimitive_twice_distributional _ continuous_const.locallyIntegrable

-- A datum for every named activation exists without analytic assumptions in its constructor.
example : ModernActivation := .gaussianGelu
example : ModernActivation := .swish 1 (by norm_num)
example : ModernActivation := .mish
example : ModernActivation := .softplus 1 (by norm_num)

-- An empty action type has no normalized policy; a route itself always adds two actions.
example (p : Policy (Fin 0)) : False := by
  have h := p.normalized
  simpa using h

-- The zero stream absorbs even though its simplex has many policies.
example : gibbs 1 (fun _ : Fin 2 => (0 : ℝ)) 0 = pure 0 :=
  empty_stream_absorbs _ _ _ (fun _ => le_rfl)

-- Negative continuation is a log-space tie, so both player copies select stop.
example (θ : ℝ) :
    (canonical θ (.activation true (.terminal (-3)) (.terminal 1))).1 = false := by
  norm_num [canonical, value, signed, Thesis.RoutingGate.chosenLogAction_eq_positive]
example (θ : ℝ) :
    (canonical θ (.activation false (.terminal 3) (.terminal (-1)))).1 = false := by
  norm_num [canonical, value, signed, Thesis.RoutingGate.chosenLogAction_eq_positive]

-- Signed raw input, negative edge, positive bias: ReLU((-2)*(-3)+1)=7.
def rawSignedNet : Network 1 1 :=
  .layer 0 (Matrix.of (fun _ _ => 2)) (fun _ => 1) (fun _ => 0) (.output 1)
example (ε : ℝ) (hε : 0 ≤ ε) :
    value 1 (networkGame rawSignedNet ε hε (fun _ => -3) 0 true) = 7 := by
  rw [networkGame_value]
  norm_num [signed,rawSignedNet,Network.eval,Matrix.mulVec,dotProduct,relu,Fin.sum_univ_one,Matrix.of_apply]


-- A zero-width input layer still yields a real, biased and nonvacuous routing game.
def noInputNet : Network 0 1 :=
  .layer (fun _ _ => 0) (fun _ _ => 0) (fun _ => 2) (fun _ => 0) (.output 1)
example : value 1 (networkGame noInputNet 0 (by norm_num) (fun i => Fin.elim0 i) 0 true) = 2 := by
  rw [networkGame_value]
  norm_num [signed,noInputNet,Network.eval,Matrix.mulVec,dotProduct,relu]

-- Parity is actual negative-edge parity, including two negatives and zero weights.
def twoNegative : MaskedTrace 1 1 :=
  .layer (k := 1) (fun _ _ => 0) (fun _ _ => 2) (fun _ => true)
    (.layer (k := 1) (fun _ _ => 0) (fun _ _ => 3) (fun _ => true) (.output 1))
example : negativeEdgeCount twoNegative 0 (0,0,()) = 2 := by
  change (0 + (if (0 : ℝ)-3<0 then 1 else 0) + (if (0 : ℝ)-2<0 then 1 else 0) : ℕ) = 2
  norm_num
example : geometricParity twoNegative 0 (0,0,()) = false := by
  change Bool.xor (decide ((0 : ℝ)-2<0)) (Bool.xor (decide ((0 : ℝ)-3<0)) false) = false
  norm_num
example : geometricWeight twoNegative 0 0 (0,0,()) = 6 := by
  change ((if true then |(0 : ℝ)-2| else 0) * ((if true then |(0 : ℝ)-3| else 0) * (if (0 : Fin 1)=0 then 1 else 0))) = 6
  norm_num

-- Both tied streams are annihilated by an actual graph ReLU.
example : stoppingExpr (.maximum (.input (0 : Fin 1)) (.constant 0))
    ((fun _ => 5),(fun _ => 5)) = (0,0) := by
  norm_num [stoppingExpr,winnerPair]

-- A general max tie picks one whole pair, never coordinatewise maxima.
example : stoppingExpr (.maximum (.input (0 : Fin 2)) (.input 1))
    ((fun i => if i=0 then 8 else 3),(fun i => if i=0 then 5 else 0)) = (3,0) := by
  norm_num [stoppingExpr,winnerPair]

-- Tiny off-tie differences can move the entire pair; no ordinary derivative at ties is asserted.
example : winnerPair (3,0) (8,5) = (3,0) := by norm_num [winnerPair]
example : winnerPair (3,0) (8+(1/1000 : ℝ),5) = (8+(1/1000 : ℝ),5) := by
  norm_num [winnerPair]

end
