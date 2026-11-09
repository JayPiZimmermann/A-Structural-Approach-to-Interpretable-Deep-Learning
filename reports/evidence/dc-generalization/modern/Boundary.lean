import HiddenMonotonicity.ModernMonotoneDC

set_option autoImplicit false
open HiddenMonotonicity HiddenMonotonicity.SmoothDC

-- Formula-specific consumers have no analytic hypotheses to discharge.
example : ValidPairActivation gaussianGelu (curvatureLiftPair gaussianGelu) :=
  (modern_curvature_pair .gaussianGelu).2.2.1

example (β : ℝ) (hβ : 0 < β) :
    ValidPairActivation (swish β) (curvatureLiftPair (swish β)) :=
  (modern_curvature_pair (.swish β hβ)).2.2.1

example : NonnegativePairActivation (curvatureLiftPair Real.sigmoid) :=
  (modern_curvature_pair .sigmoid).2.2.2

example (θ : ℝ) (hθ : 0 < θ) :
    ConvexPairActivation (curvatureLiftPair (Thesis.Regularization.softplus θ)) :=
  (modern_curvature_pair (.softplus θ hθ)).1

-- Empty widths are admitted by the actual finite network, not excluded by
-- an unmentioned positivity constraint on dimensions.
example (a : ModernActivation) :
    Monotone ((Network.output 0).decomposeWith (curvatureLiftPair a.eval)) :=
  (modern_curvature_network (.output 0) trivial a).1

-- A negative bias and signed input still preserve global convexity and recovery.
-- Nonnegative stream values are deliberately not inferred from this example.
example (a : ModernActivation) :
    ∀ x : PairVec 1,
      ((Network.output 1).affineDecomposeWith (k := 1) (curvatureLiftPair a.eval)
        (fun _ _ => 0) (fun _ _ => 1) (fun _ => -3) (fun _ => 2) x).1 -
      ((Network.output 1).affineDecomposeWith (k := 1) (curvatureLiftPair a.eval)
        (fun _ _ => 0) (fun _ _ => 1) (fun _ => -3) (fun _ => 2) x).2 =
      affineLayer (k := 1) (fun _ _ => 0) (fun _ _ => 1) (fun _ => -3) (fun _ => 2)
        ((Network.output 1).forwardWith a.eval (x.1 - x.2)) :=
  (modern_curvature_affine_network (.output 1) trivial a
    (fun _ _ => 0) (fun _ _ => 1) (by intros; norm_num) (by intros; norm_num)
    (fun _ => -3) (fun _ => 2)).2.2.2

#print axioms modern_curvature_pair
#print axioms modern_curvature_network
#print axioms modern_curvature_network_nonnegative
#print axioms modern_curvature_affine_network
