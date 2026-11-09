import Thesis.SourceFoundationsStatements
import Thesis.SourceGeometryStatements
import Thesis.ConvexCPWL
import Thesis.AffineSliceGeometry
noncomputable section
open Finset Matrix HiddenMonotonicity Thesis.Tropical Thesis.PiecewiseLinear Thesis Thesis.SourceFoundations Thesis.SourceGeometry Thesis.ReLUNetGame
open scoped Pointwise NNReal

-- FOUNDATION-SOURCE-monotone_represents
example : ∀ {n m k : ℕ} (net : Network n m) (σ : ℝ → ℝ)
    (hw : Foundations.PositiveWeights net) (hm : Monotone σ)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ) (hW : ∀ i j, 0 ≤ W i j),
    Monotone (fun x => W.mulVec (net.forwardWith σ x)+b) := @Thesis.SourceFoundations.monotone_represents
#check @Thesis.SourceFoundations.monotone_represents
#print axioms Thesis.SourceFoundations.monotone_represents

-- FOUNDATION-SOURCE-icnn_represents_convex
example : ∀ {n m k : ℕ} (net : Network n m) (σ : ℝ → ℝ)
    (hw : Foundations.InputConvexWeights net) (hm : Monotone σ) (hc : Foundations.ScalarConvex σ)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ) (hW : ∀ i j, 0 ≤ W i j),
    ∀ i, ConvexOn ℝ Set.univ (fun x => (W.mulVec (net.forwardWith σ x)+b) i) := @Thesis.SourceFoundations.icnn_represents_convex
#check @Thesis.SourceFoundations.icnn_represents_convex
#print axioms Thesis.SourceFoundations.icnn_represents_convex

-- FOUNDATION-SOURCE-maxout_special_cases
example : ∀ {I A : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype A] [Nonempty A] (w : I → ℝ) (b : ℝ) (p : Tropical.Polynomial I),
    (∀ x, relu (w ⬝ᵥ x+b) =
      ((Tropical.Polynomial.monomial w b).max (Tropical.Polynomial.monomial 0 0)).eval x) ∧
    (∀ x, (poolingPolynomial (I := I)).eval x = finiteMax x) ∧
    ConvexOn ℝ Set.univ p.eval ∧ Monotone (finiteMax (A := A)) := @Thesis.SourceFoundations.maxout_special_cases
#check @Thesis.SourceFoundations.maxout_special_cases
#print axioms Thesis.SourceFoundations.maxout_special_cases

-- FOUNDATION-SOURCE-bellman_equations
example : ∀ {S A : Type} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (M : Bellman.MDP S A) (π : Bellman.Policy S A),
    ((∑' n, (M.discount : ℝ)^n • (M.markovOperator π)^[n] (M.policyReward π)) = M.policyValue π) ∧
    (M.policyBellman π (M.policyValue π) = M.policyValue π) ∧
    (∀ v, M.policyBellman π v=v → v=M.policyValue π) ∧
    (M.bellman M.optimalValue=M.optimalValue) ∧
    (∀ v, M.bellman v=v → v=M.optimalValue) ∧
    (M.policyValue (Bellman.pure M.greedy)=M.optimalValue) ∧
    (∀ ρ : Bellman.Policy S A, M.policyValue ρ ≤ M.optimalValue) ∧
    (∀ choice : S → A, (∀ s, M.action M.optimalValue s (choice s)=M.optimalValue s) →
      M.policyValue (Bellman.pure choice)=M.optimalValue) := @Thesis.SourceFoundations.bellman_equations
#check @Thesis.SourceFoundations.bellman_equations
#print axioms Thesis.SourceFoundations.bellman_equations

-- FOUNDATION-SOURCE-shapley_bellman
example : ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    (G : LayeredGames.Game S A),
    (∀ v : ℕ → S → ℝ, v 0=G.terminal →
      (∀ n s, v (n+1) s=LayeredGames.best (G.maximize n s) (fun a => G.action n s a (v n))) →
      v=G.value) ∧
    ∀ plus minus : LayeredGames.Policy S A, ∀ n s,
      G.payoff plus G.optimalPolicy n s ≤ G.value n s ∧
      G.payoff G.optimalPolicy G.optimalPolicy n s=G.value n s ∧
      G.value n s ≤ G.payoff G.optimalPolicy minus n s := @Thesis.SourceFoundations.shapley_bellman
#check @Thesis.SourceFoundations.shapley_bellman
#print axioms Thesis.SourceFoundations.shapley_bellman

-- FOUNDATION-SOURCE-subdifferential_face
example : ∀ {I A : Type} [Fintype I] [Fintype A] [Nonempty A]
    (v : A → I → ℝ) (x : I → ℝ),
    (∀ s, Subgradient (support (convexHull ℝ (Set.range v))) x s ↔
      s ∈ convexHull ℝ (Set.range v) ∧ s ⬝ᵥ x=support (convexHull ℝ (Set.range v)) x) ∧
    (DifferentiableAt ℝ (support (convexHull ℝ (Set.range v))) x ↔
      ∃ p, p ∈ convexHull ℝ (Set.range v) ∧
        p ⬝ᵥ x=support (convexHull ℝ (Set.range v)) x ∧
        ∀ q ∈ convexHull ℝ (Set.range v), q ⬝ᵥ x=support (convexHull ℝ (Set.range v)) x → q=p) ∧
    (∀ p, HasFDerivAt (support (convexHull ℝ (Set.range v))) (gradientRow p) x →
      p ∈ convexHull ℝ (Set.range v)) := @Thesis.SourceFoundations.subdifferential_face
#check @Thesis.SourceFoundations.subdifferential_face
#print axioms Thesis.SourceFoundations.subdifferential_face

-- FOUNDATION-SOURCE-split_tropical_rational_affine
example : ∀ {n m k : ℕ} (net : Network n m)
    (hn : net.Nonnegative) (hb : BiasFree net)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j),
    let hidden := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
    let g := polynomialAffine wp wn 0 hidden.1 hidden.2
    let h := polynomialAffine wn wp 0 hidden.1 hidden.2
    (∀ i, (g i).ZeroIntercepts ∧ (h i).ZeroIntercepts ∧
      (g i).NonnegativeSlopes ∧ (h i).NonnegativeSlopes ∧
      Monotone (g i).eval ∧ Monotone (h i).eval ∧
      ConvexOn ℝ Set.univ (g i).eval ∧ ConvexOn ℝ Set.univ (h i).eval ∧
      (∀ c : ℝ, 0 ≤ c → ∀ x, (g i).eval (c • x)=c*(g i).eval x ∧
        (h i).eval (c • x)=c*(h i).eval x)) ∧
    (∀ p q, (fun i => (g i).eval (Sum.elim p q))=
        wp.mulVec (net.split p q).1+wn.mulVec (net.split p q).2 ∧
      (fun i => (h i).eval (Sum.elim p q))=
        wn.mulVec (net.split p q).1+wp.mulVec (net.split p q).2) ∧
    (∀ p q i, (g i).eval (Sum.elim p q)-(h i).eval (Sum.elim p q)=
      (wp-wn).mulVec (net.eval (p-q)) i) ∧
    (∀ i, (g i).newton=(∑ j, wp i j • (hidden.1 j).newton)+
        (∑ j, wn i j • (hidden.2 j).newton) ∧
      (h i).newton=(∑ j, wn i j • (hidden.1 j).newton)+
        (∑ j, wp i j • (hidden.2 j).newton)) := @Thesis.SourceFoundations.split_tropical_rational_affine
#check @Thesis.SourceFoundations.split_tropical_rational_affine
#print axioms Thesis.SourceFoundations.split_tropical_rational_affine

-- FOUNDATION-SOURCE-biased_vertices_gradients
example : ∀ {I : Type} [Fintype I] (p : Thesis.Tropical.Polynomial I) (s : I → ℝ),
    (∃ x, HasFDerivAt p.eval (gradientRow s) x) ↔
      ∃ q, SliceVisible p.lift.slope q ∧ q ∈ p.lift.newton.extremePoints ℝ ∧
        inputProjection q=s := @Thesis.SourceFoundations.biased_vertices_gradients
#check @Thesis.SourceFoundations.biased_vertices_gradients
#print axioms Thesis.SourceFoundations.biased_vertices_gradients

-- FOUNDATION-SOURCE-relu_net_game_value_affine
example : ∀ {n m k : ℕ} (net : Network n m) (hn : net.Nonnegative)
    (hr : ReLUNetGame.NonzeroRows net) (x : Fin n → ℝ)
    (plus minus : ReLUNetGame.Strategy net) (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (b : Fin k → ℝ) (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j)
    (hrow : ∀ i, ReLUNetGame.rowDiscount wp wn i≠0) (i : Fin k),
    let read := fun v : (Fin m → ℝ) × (Fin m → ℝ) => ReLUNetGame.continuation wp wn b v.1 v.2 i
    let logit := ((wp-wn).mulVec (net.eval x)+b) i
    read (ReLUNetGame.policyValue net plus (ReLUNetGame.optimalStrategy net x) x (-x)) ≤ logit ∧
    read (ReLUNetGame.policyValue net (ReLUNetGame.optimalStrategy net x)
      (ReLUNetGame.optimalStrategy net x) x (-x))=logit ∧
    logit ≤ read (ReLUNetGame.policyValue net (ReLUNetGame.optimalStrategy net x) minus x (-x)) ∧
    (ReLUNetGame.SubgamePerfect net plus minus x (-x) ↔
      ReLUNetGame.GateOptimalStrategy net x plus ∧ ReLUNetGame.GateOptimalStrategy net x minus) ∧
    (ReLUNetGame.SubgamePerfect net plus minus x (-x) →
      read (ReLUNetGame.policyValue net plus minus x (-x))=logit) := @Thesis.SourceFoundations.relu_net_game_value_affine
#check @Thesis.SourceFoundations.relu_net_game_value_affine
#print axioms Thesis.SourceFoundations.relu_net_game_value_affine

-- FOUND-13-SUPPORT
example : ∀ {I A : Type} [Fintype I] [Fintype A] [Nonempty A] (P Q : Set (I → ℝ)) (hP : IsCompact P) (hneP : P.Nonempty)
    (hcP : Convex ℝ P) (hQ : IsCompact Q) (hneQ : Q.Nonempty) (hcQ : Convex ℝ Q),
    ConvexOn ℝ Set.univ (support P) ∧
    (∀ c : ℝ, 0 ≤ c → ∀ x, support P (c • x) = c*support P x) ∧
    (∀ x, support (P+Q) x = support P x+support Q x) ∧
    (∀ x, support (convexHull ℝ (P∪Q)) x = max (support P x) (support Q x)) ∧
    (P ⊆ Q ↔ ∀ x, support P x ≤ support Q x) ∧
    (support P = support Q → P = Q) ∧
    (∀ (v : A → I → ℝ) x, support (convexHull ℝ (Set.range v)) x = finiteMax (fun a => v a ⬝ᵥ x) ∧
      ∃ p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ,
        p ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x) := @Thesis.SourceGeometry.support_properties
#check @Thesis.SourceGeometry.support_properties
#print axioms Thesis.SourceGeometry.support_properties

-- FOUNDATION-NEWTON
example : ∀ {I : Type} [Fintype I] (p q : Tropical.Polynomial I),
    (p.add q).newton = p.newton+q.newton ∧
    (p.max q).newton = convexHull ℝ (p.newton∪q.newton) ∧
    (∀ x, (p.add q).eval x=p.eval x+q.eval x) ∧
    (∀ x, (p.max q).eval x=max (p.eval x) (q.eval x)) ∧
    (∀ x, p.eval x=support p.lift.newton (Sum.elim x (fun _ => 1))) ∧
    ((∀ a, p.intercept a=0) → ∀ x, p.eval x=support p.newton x) := @Thesis.SourceGeometry.newton_calculus
#check @Thesis.SourceGeometry.newton_calculus
#print axioms Thesis.SourceGeometry.newton_calculus

-- FOUNDATION-NONNEGATIVE
example : ∀ {n m : ℕ} (net : Network n m) (hn : net.Nonnegative)
    (i : Fin m),
    let polynomials := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
    (∀ v ∈ (polynomials.1 i).newton, ∀ j, 0 ≤ v j) ∧
    (∀ v ∈ (polynomials.2 i).newton, ∀ j, 0 ≤ v j) := @Thesis.SourceGeometry.network_polytopes_nonnegative
#check @Thesis.SourceGeometry.network_polytopes_nonnegative
#print axioms Thesis.SourceGeometry.network_polytopes_nonnegative

-- FOUND-03-MINKOWSKI
example : ∀ {n m k : ℕ} (net : Network n m)
    (wp wn : Matrix (Fin k) (Fin m) ℝ) (bp bn : Fin k → ℝ),
    let hidden := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
    let sets := polytopeSplit net (fun j => {Pi.single (Sum.inl j : Fin n ⊕ Fin n) (1 : ℝ)})
      (fun j => {Pi.single (Sum.inr j : Fin n ⊕ Fin n) (1 : ℝ)})
    (∀ i, (hidden.1 i).newton=sets.1 i ∧ (hidden.2 i).newton=sets.2 i) ∧
    ∀ i, (polynomialAffine wp wn bp hidden.1 hidden.2 i).newton=
        (∑ j, wp i j • sets.1 j)+(∑ j, wn i j • sets.2 j) ∧
      (polynomialAffine wn wp bn hidden.1 hidden.2 i).newton=
        (∑ j, wn i j • sets.1 j)+(∑ j, wp i j • sets.2 j) := @Thesis.SourceGeometry.minkowski_propagation_affine_network
#check @Thesis.SourceGeometry.minkowski_propagation_affine_network
#print axioms Thesis.SourceGeometry.minkowski_propagation_affine_network

-- FOUND-04-FORWARD-network_cpwl
example : ∀ {n m : ℕ} (net : Network n m),
    CPWL net.eval := @Thesis.PiecewiseLinear.network_cpwl
#check @Thesis.PiecewiseLinear.network_cpwl
#print axioms Thesis.PiecewiseLinear.network_cpwl

-- FOUND-04-FORWARD-affine_network_cpwl
example : ∀ {n m k : ℕ} (net : Network n m)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ),
    CPWL (fun x => W.mulVec (net.eval x)+b) := @Thesis.PiecewiseLinear.affine_network_cpwl
#check @Thesis.PiecewiseLinear.affine_network_cpwl
#print axioms Thesis.PiecewiseLinear.affine_network_cpwl

-- FOUND-05-convex_cpwl_iff_max_affine
example : ∀ {I : Type} [Fintype I] (u : (I → ℝ) → ℝ),
    (CPWL (fun x (_ : Unit) => u x) ∧ ConvexOn ℝ Set.univ u) ↔
      ∃ p : Polynomial I, u=p.eval := @Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine
#check @Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine
#print axioms Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine

-- FOUND-05-homogeneous_convex_cpwl_unique_polytope
example : ∀ {I : Type} [Fintype I] (u : (I → ℝ) → ℝ)
    (hp : CPWL (fun x (_ : Unit) => u x)) (hc : ConvexOn ℝ Set.univ u)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ x, u (c • x)=c*u x),
    ∃! P : Set (I → ℝ), IsPolytope P ∧ u=support P := @Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope
#check @Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope
#print axioms Thesis.PiecewiseLinear.homogeneous_convex_cpwl_unique_polytope

-- FOUND-05-homogeneous_convex_cpwl_vertices
example : ∀ {I : Type} [Fintype I] (u : (I → ℝ) → ℝ)
    (hp : CPWL (fun x (_ : Unit) => u x)) (hc : ConvexOn ℝ Set.univ u)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ x, u (c • x)=c*u x),
    ∃ P : Set (I → ℝ), IsPolytope P ∧ u=support P ∧
      (∀ Q, IsPolytope Q → u=support Q → Q=P) ∧
      ∀ s, s ∈ P.extremePoints ℝ ↔ ∃ x, HasFDerivAt u (gradientRow s) x := @Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices
#check @Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices
#print axioms Thesis.PiecewiseLinear.homogeneous_convex_cpwl_vertices

-- FOUND-08-subgamePerfect_iff_gateOptimal
example : ∀ {n m : ℕ} (net : Network n m)
    (hr : NonzeroRows net) (x : Fin n → ℝ) (plus minus : Strategy net),
    SubgamePerfect net plus minus x (-x) ↔
      GateOptimalStrategy net x plus ∧ GateOptimalStrategy net x minus := @Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal
#check @Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal
#print axioms Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal

-- FOUND-08-optimalStrategy_subgamePerfect
example : ∀ {n m : ℕ} (net : Network n m)
    (hr : NonzeroRows net) (x : Fin n → ℝ),
    SubgamePerfect net (optimalStrategy net x) (optimalStrategy net x) x (-x) := @Thesis.ReLUNetGame.optimalStrategy_subgamePerfect
#check @Thesis.ReLUNetGame.optimalStrategy_subgamePerfect
#print axioms Thesis.ReLUNetGame.optimalStrategy_subgamePerfect

-- FOUND-08-subgamePerfect_value
example : ∀ {n m : ℕ} (net : Network n m) (hr : NonzeroRows net)
    (x : Fin n → ℝ) (plus minus : Strategy net)
    (h : SubgamePerfect net plus minus x (-x)),
    policyValue net plus minus x (-x)=(net.eval x,-net.eval x) := @Thesis.ReLUNetGame.subgamePerfect_value
#check @Thesis.ReLUNetGame.subgamePerfect_value
#print axioms Thesis.ReLUNetGame.subgamePerfect_value

-- FOUND-10-SLICE
example : ∀ {I A : Type} [Fintype I] [Fintype A] [Nonempty A] (v : A → I ⊕ Unit → ℝ) (s : I → ℝ),
    (∃ x, HasFDerivAt (fun y => support (convexHull ℝ (Set.range v)) (affineSlice y))
      (gradientRow s) x) ↔
    ∃ p, SliceVisible v p ∧ p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ ∧
      inputProjection p=s := @Thesis.Tropical.slice_attainable_gradients
#check @Thesis.Tropical.slice_attainable_gradients
#print axioms Thesis.Tropical.slice_attainable_gradients
