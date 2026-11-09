import HiddenMonotonicity.ClosedFormMonotoneDC

set_option autoImplicit false
open HiddenMonotonicity HiddenMonotonicity.SmoothDC

example (x y : ℝ) : ClosedFormActivation.relu.pair (x,y) = (max x y,y) :=
  ClosedFormActivation.relu_pair x y

-- These witnesses force the actual closed formulas, not merely an existential
-- decomposition or a second set of unspecified activation functions.
example : ValidPairActivation gaussianGelu explicitGaussianGeluPair :=
  (closed_form_activation_properties .gaussianGelu).2.2.1

example (β : ℝ) (hβ : 0 < β) :
    ValidPairActivation (swish β) (explicitSwishPair β) :=
  (closed_form_activation_properties (.swish β hβ)).2.2.1

example : ConvexPairActivation explicitSigmoidSmoothPair :=
  (closed_form_activation_properties .sigmoid).1

example (θ : ℝ) (hθ : 0 < θ) :
    NonnegativePairActivation (explicitSoftplusPair θ) :=
  (closed_form_activation_properties (.softplus θ hθ)).2.2.2

example (a : ClosedFormActivation) :
    Monotone ((Network.output 0).affineDecomposeWith a.pair
      (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 0 0) :=
  (closed_form_affine_network (.output 0) trivial a 0 0
    (by intros; simp) (by intros; simp) 0 0).1

example (a : ClosedFormActivation) :
    Monotone (fun x : Vec 1 => (Network.output 1).affineDecomposeWith a.pair
      (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 1)
      (fun _ => -3) (fun _ => 2) (x,0)) :=
  (closed_form_affine_dc (.output 1) trivial a 0 (fun _ _ => 1)
    (by intros; simp) (by intros; norm_num) (fun _ => -3) (fun _ => 2)).1

#print axioms closed_form_activation_properties
#print axioms closed_form_affine_network
#print axioms closed_form_affine_dc
