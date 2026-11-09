import Thesis.Foundations
import Thesis.BellmanReturn
import Thesis.LayeredGames
import Thesis.ReLUNetEquilibrium
import Thesis.PiecewiseLinear
import Thesis.SourceGeometryStatements
import Thesis.AffineSliceGeometry
import Thesis.ConvexCPWL

/-! Bundled statements matching complete source claims, rather than one component
identity standing in for a multi-part theorem. -/
noncomputable section
namespace Thesis.SourceFoundations
open Finset Matrix HiddenMonotonicity Thesis.Tropical
open scoped NNReal Pointwise

/-- prop:monotone_represents, including the actual affine final layer. -/
theorem monotone_represents {n m k} (net : Network n m) (σ : ℝ → ℝ)
    (hw : Foundations.PositiveWeights net) (hm : Monotone σ)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ) (hW : ∀ i j, 0 ≤ W i j) :
    Monotone (fun x => W.mulVec (net.forwardWith σ x)+b) :=
  Foundations.monotone_affine_output net σ hw hm W b hW

/-- prop:icnn_convex at the exact first-layer-unrestricted architecture, with an
ungated affine readout and standard ConvexOn conclusions for every output. -/
theorem icnn_represents_convex {n m k} (net : Network n m) (σ : ℝ → ℝ)
    (hw : Foundations.InputConvexWeights net) (hm : Monotone σ) (hc : Foundations.ScalarConvex σ)
    (W : Matrix (Fin k) (Fin m) ℝ) (b : Fin k → ℝ) (hW : ∀ i j, 0 ≤ W i j) :
    ∀ i, ConvexOn ℝ Set.univ (fun x => (W.mulVec (net.forwardWith σ x)+b) i) :=
  (Foundations.jensen_iff_convexOn _).mp (Foundations.icnn_affine_output net σ hw hm hc W b hW)

def poolingPolynomial {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] : Tropical.Polynomial I where
  Terms := I
  finite := inferInstance
  inhabited := inferInstance
  slope := fun i => Pi.single i 1
  intercept := fun _ => 0

/-- obs:relu_maxout_special_case, including both exact special cases, convexity,
and monotonicity in the preactivation arguments. -/
theorem maxout_special_cases {I A : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype A] [Nonempty A] (w : I → ℝ) (b : ℝ) (p : Tropical.Polynomial I) :
    (∀ x, relu (w ⬝ᵥ x+b) =
      ((Tropical.Polynomial.monomial w b).max (Tropical.Polynomial.monomial 0 0)).eval x) ∧
    (∀ x, (poolingPolynomial (I := I)).eval x = finiteMax x) ∧
    ConvexOn ℝ Set.univ p.eval ∧ Monotone (finiteMax (A := A)) := by
  refine ⟨?_,?_,p.convex,?_⟩
  · intro x
    rw [Tropical.Polynomial.eval_max,Tropical.Polynomial.eval_monomial,
      Tropical.Polynomial.eval_monomial,zero_dotProduct,zero_add]
    rfl
  · intro x
    simp only [Tropical.Polynomial.eval,poolingPolynomial,single_one_dotProduct,add_zero]
  · intro x y hxy
    apply finiteMax_le
    intro a
    exact (hxy a).trans (le_finiteMax y a)

/-- prop:bellman: expected return, evaluation uniqueness, optimality uniqueness,
existence of a pure optimum, and greedy optimality including ties. -/
theorem bellman_equations {S A : Type} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (M : Bellman.MDP S A) (π : Bellman.Policy S A) :
    ((∑' n, (M.discount : ℝ)^n • (M.markovOperator π)^[n] (M.policyReward π)) = M.policyValue π) ∧
    (M.policyBellman π (M.policyValue π) = M.policyValue π) ∧
    (∀ v, M.policyBellman π v=v → v=M.policyValue π) ∧
    (M.bellman M.optimalValue=M.optimalValue) ∧
    (∀ v, M.bellman v=v → v=M.optimalValue) ∧
    (M.policyValue (Bellman.pure M.greedy)=M.optimalValue) ∧
    (∀ ρ : Bellman.Policy S A, M.policyValue ρ ≤ M.optimalValue) ∧
    (∀ choice : S → A, (∀ s, M.action M.optimalValue s (choice s)=M.optimalValue s) →
      M.policyValue (Bellman.pure choice)=M.optimalValue) :=
  ⟨M.expected_return_eq_value π,M.policy_fixed π,M.policy_unique π,
    M.optimal_fixed,M.optimal_unique,M.greedy_policy_optimal M.greedy M.greedy_value,
    M.policy_le_optimal,M.greedy_policy_optimal⟩

/-- thm:shapley_bellman: unique layered Bellman solution and constructed pure
stationary saddle versus all randomized policies, at every subgame state. -/
theorem shapley_bellman {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    (G : LayeredGames.Game S A) :
    (∀ v : ℕ → S → ℝ, v 0=G.terminal →
      (∀ n s, v (n+1) s=LayeredGames.best (G.maximize n s) (fun a => G.action n s a (v n))) →
      v=G.value) ∧
    ∀ plus minus : LayeredGames.Policy S A, ∀ n s,
      G.payoff plus G.optimalPolicy n s ≤ G.value n s ∧
      G.payoff G.optimalPolicy G.optimalPolicy n s=G.value n s ∧
      G.value n s ≤ G.payoff G.optimalPolicy minus n s :=
  ⟨G.bellman_unique,G.saddle⟩

/-- prop:subdifferential_face, with its differentiability equivalence and the
membership conclusion for every attained genuine gradient. -/
theorem subdifferential_face {I A : Type} [Fintype I] [Fintype A] [Nonempty A]
    (v : A → I → ℝ) (x : I → ℝ) :
    (∀ s, Subgradient (support (convexHull ℝ (Set.range v))) x s ↔
      s ∈ convexHull ℝ (Set.range v) ∧ s ⬝ᵥ x=support (convexHull ℝ (Set.range v)) x) ∧
    (DifferentiableAt ℝ (support (convexHull ℝ (Set.range v))) x ↔
      ∃ p, p ∈ convexHull ℝ (Set.range v) ∧
        p ⬝ᵥ x=support (convexHull ℝ (Set.range v)) x ∧
        ∀ q ∈ convexHull ℝ (Set.range v), q ⬝ᵥ x=support (convexHull ℝ (Set.range v)) x → q=p) ∧
    (∀ p, HasFDerivAt (support (convexHull ℝ (Set.range v))) (gradientRow p) x →
      p ∈ convexHull ℝ (Set.range v)) := by
  refine ⟨subgradient_iff_maximizing_face v x,support_differentiable_iff_singleton_face v x,?_⟩
  intro p hp
  exact ((vertices_eq_attainable_gradients v p).mpr ⟨x,hp⟩).1

/-- thm:split_tropical_rational, all properties for the explicitly constructed
network split polynomials: convexity, monotonicity, positive homogeneity, and exactness. -/
theorem split_tropical_rational {n m} (net : Network n m) (hn : net.Nonnegative) (hb : BiasFree net) :
    let polys := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
    (∀ i, (polys.1 i).ZeroIntercepts ∧ (polys.2 i).ZeroIntercepts ∧
      (polys.1 i).NonnegativeSlopes ∧ (polys.2 i).NonnegativeSlopes ∧
      Monotone (polys.1 i).eval ∧ Monotone (polys.2 i).eval ∧
      ConvexOn ℝ Set.univ (polys.1 i).eval ∧ ConvexOn ℝ Set.univ (polys.2 i).eval ∧
      (∀ c : ℝ, 0 ≤ c → ∀ x, (polys.1 i).eval (c • x)=c*(polys.1 i).eval x ∧
        (polys.2 i).eval (c • x)=c*(polys.2 i).eval x)) ∧
    (∀ p q, ((fun i => (polys.1 i).eval (Sum.elim p q)),
        (fun i => (polys.2 i).eval (Sum.elim p q)))=net.split p q) ∧
    ∀ p q i, (polys.1 i).eval (Sum.elim p q)-(polys.2 i).eval (Sum.elim p q)=net.eval (p-q) i := by
  let p := (inputPolynomials n).1
  let q := (inputPolynomials n).2
  let polys := tropicalSplit net p q
  have hpos := tropicalSplit_nonnegative net hn p q
    (fun i => coordinate_nonnegative (Sum.inl i)) (fun i => coordinate_nonnegative (Sum.inr i))
  have hzero := tropicalSplit_zero net hb p q (fun _ _ => rfl) (fun _ _ => rfl)
  have he : ∀ x y, ((fun i => (polys.1 i).eval (Sum.elim x y)),
      (fun i => (polys.2 i).eval (Sum.elim x y)))=net.split x y := by
    intro x y
    have h := tropicalSplit_eval net hn p q (Sum.elim x y)
    simpa only [polys,p,q,inputPolynomials,coordinate_eval,Sum.elim_inl,Sum.elim_inr] using h
  refine ⟨?_,he,?_⟩
  · intro i
    exact ⟨hzero.1 i,hzero.2 i,hpos.1 i,hpos.2 i,
      Tropical.Polynomial.monotone _ (hpos.1 i),Tropical.Polynomial.monotone _ (hpos.2 i),
      Tropical.Polynomial.convex _,Tropical.Polynomial.convex _,
      fun c hc x => ⟨Tropical.Polynomial.homogeneous _ (hzero.1 i) c hc x,
        Tropical.Polynomial.homogeneous _ (hzero.2 i) c hc x⟩⟩
  · intro x y i
    have hg := congrFun (congrArg Prod.fst (he x y)) i
    have hh := congrFun (congrArg Prod.snd (he x y)) i
    change (polys.1 i).eval (Sum.elim x y)-(polys.2 i).eval (Sum.elim x y)=_
    change (polys.1 i).eval (Sum.elim x y)=(net.split x y).1 i at hg
    change (polys.2 i).eval (Sum.elim x y)=(net.split x y).2 i at hh
    rw [hg,hh]
    exact congrFun (net.correct x y) i

/-- The complete bias-free tropical theorem with the source's ungated affine
readout. The displayed head evaluations are the actual split affine heads, and
zero intercepts, monotonicity, convexity and homogeneity apply to both of them. -/
theorem split_tropical_rational_affine {n m k} (net : Network n m)
    (hn : net.Nonnegative) (hb : BiasFree net)
    (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) :
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
        (∑ j, wp i j • (hidden.2 j).newton)) := by
  let hidden := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
  let g := polynomialAffine wp wn 0 hidden.1 hidden.2
  let h := polynomialAffine wn wp 0 hidden.1 hidden.2
  have hs := split_tropical_rational net hn hb
  have hgpos : ∀ i, (g i).NonnegativeSlopes := polynomialAffine_nonnegative _ _ _ _ _
    hwp hwn (fun j => (hs.1 j).2.2.1) (fun j => (hs.1 j).2.2.2.1)
  have hhpos : ∀ i, (h i).NonnegativeSlopes := polynomialAffine_nonnegative _ _ _ _ _
    hwn hwp (fun j => (hs.1 j).2.2.1) (fun j => (hs.1 j).2.2.2.1)
  have hgzero : ∀ i, (g i).ZeroIntercepts := polynomialAffine_zero _ _ _ _
    (fun j => (hs.1 j).1) (fun j => (hs.1 j).2.1)
  have hhzero : ∀ i, (h i).ZeroIntercepts := polynomialAffine_zero _ _ _ _
    (fun j => (hs.1 j).1) (fun j => (hs.1 j).2.1)
  have he : ∀ p q,
      (fun i => (g i).eval (Sum.elim p q))=wp.mulVec (net.split p q).1+wn.mulVec (net.split p q).2 ∧
      (fun i => (h i).eval (Sum.elim p q))=wn.mulVec (net.split p q).1+wp.mulVec (net.split p q).2 := by
    intro p q
    have h1 := congrArg Prod.fst (hs.2.1 p q)
    have h2 := congrArg Prod.snd (hs.2.1 p q)
    change (fun i => (hidden.1 i).eval (Sum.elim p q))=(net.split p q).1 at h1
    change (fun i => (hidden.2 i).eval (Sum.elim p q))=(net.split p q).2 at h2
    constructor
    · funext i
      change (polynomialAffine wp wn 0 hidden.1 hidden.2 i).eval _=_
      rw [polynomialAffine_eval _ _ _ _ _ hwp hwn,h1,h2]
      simp
    · funext i
      change (polynomialAffine wn wp 0 hidden.1 hidden.2 i).eval _=_
      rw [polynomialAffine_eval _ _ _ _ _ hwn hwp,h1,h2]
      simp
  refine ⟨?_,he,?_,?_⟩
  · intro i
    exact ⟨hgzero i,hhzero i,hgpos i,hhpos i,
      Tropical.Polynomial.monotone _ (hgpos i),Tropical.Polynomial.monotone _ (hhpos i),
      Tropical.Polynomial.convex _,Tropical.Polynomial.convex _,
      fun c hc x => ⟨Tropical.Polynomial.homogeneous _ (hgzero i) c hc x,
        Tropical.Polynomial.homogeneous _ (hhzero i) c hc x⟩⟩
  · intro p q i
    have heg := congrFun (he p q).1 i
    have heh := congrFun (he p q).2 i
    change (g i).eval _-(h i).eval _=_
    rw [heg,heh,← net.correct p q,sub_mulVec,mulVec_sub,mulVec_sub]
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  · intro i
    exact ⟨Thesis.SourceGeometry.affine_newton wp wn 0 hidden.1 hidden.2 i,
      Thesis.SourceGeometry.affine_newton wn wp 0 hidden.1 hidden.2 i⟩

/-- Source-facing correction of the homogenized vertex claim for biased networks:
only vertices exposed by admissible slice directions yield input gradients. -/
theorem biased_vertices_gradients {I : Type} [Fintype I] (p : Tropical.Polynomial I)
    (s : I → ℝ) :
    (∃ x, HasFDerivAt p.eval (gradientRow s) x) ↔
    ∃ q, SliceVisible p.lift.slope q ∧ q ∈ p.lift.newton.extremePoints ℝ ∧
      inputProjection q=s := p.attainable_gradients s

/-- Full ReLU game statement: selected saddle, actual payoff, and exact all-subgame
characterization of every randomized equilibrium up to zero-preactivation ties. -/
theorem relu_net_game_value {n m} (net : Network n m) (hn : net.Nonnegative)
    (hr : ReLUNetGame.NonzeroRows net) (x : Fin n → ℝ)
    (plus minus : ReLUNetGame.Strategy net) :
    (ReLUNetGame.policyValue net plus (ReLUNetGame.optimalStrategy net x) x (-x)).1 ≤ net.eval x ∧
    (ReLUNetGame.policyValue net plus (ReLUNetGame.optimalStrategy net x) x (-x)).2 ≤ -net.eval x ∧
    ReLUNetGame.policyValue net (ReLUNetGame.optimalStrategy net x)
        (ReLUNetGame.optimalStrategy net x) x (-x)=(net.eval x,-net.eval x) ∧
    net.eval x ≤ (ReLUNetGame.policyValue net (ReLUNetGame.optimalStrategy net x) minus x (-x)).1 ∧
    -net.eval x ≤ (ReLUNetGame.policyValue net (ReLUNetGame.optimalStrategy net x) minus x (-x)).2 ∧
    (ReLUNetGame.SubgamePerfect net plus minus x (-x) ↔
      ReLUNetGame.GateOptimalStrategy net x plus ∧ ReLUNetGame.GateOptimalStrategy net x minus) ∧
    (ReLUNetGame.SubgamePerfect net plus minus x (-x) →
      ReLUNetGame.policyValue net plus minus x (-x)=(net.eval x,-net.eval x)) := by
  have hs := ReLUNetGame.relu_net_game_equilibrium net hn hr x plus minus
  exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2,
    ReLUNetGame.subgamePerfect_iff_gateOptimal net hr x plus minus,
    ReLUNetGame.subgamePerfect_value net hr x plus minus⟩

/-- The same all-subgame uniqueness statement together with the actual source
architecture's forced, ungated affine logit and its randomized saddle bounds. -/
theorem relu_net_game_value_affine {n m k} (net : Network n m) (hn : net.Nonnegative)
    (hr : ReLUNetGame.NonzeroRows net) (x : Fin n → ℝ)
    (plus minus : ReLUNetGame.Strategy net) (wp wn : Matrix (Fin k) (Fin m) ℝ)
    (b : Fin k → ℝ) (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j)
    (hrow : ∀ i, ReLUNetGame.rowDiscount wp wn i≠0) (i : Fin k) :
    let read := fun v : (Fin m → ℝ) × (Fin m → ℝ) => ReLUNetGame.continuation wp wn b v.1 v.2 i
    let logit := ((wp-wn).mulVec (net.eval x)+b) i
    read (ReLUNetGame.policyValue net plus (ReLUNetGame.optimalStrategy net x) x (-x)) ≤ logit ∧
    read (ReLUNetGame.policyValue net (ReLUNetGame.optimalStrategy net x)
      (ReLUNetGame.optimalStrategy net x) x (-x))=logit ∧
    logit ≤ read (ReLUNetGame.policyValue net (ReLUNetGame.optimalStrategy net x) minus x (-x)) ∧
    (ReLUNetGame.SubgamePerfect net plus minus x (-x) ↔
      ReLUNetGame.GateOptimalStrategy net x plus ∧ ReLUNetGame.GateOptimalStrategy net x minus) ∧
    (ReLUNetGame.SubgamePerfect net plus minus x (-x) →
      read (ReLUNetGame.policyValue net plus minus x (-x))=logit) := by
  have hs := ReLUNetGame.relu_net_game_affine_equilibrium net hn hr x plus minus wp wn b hwp hwn hrow i
  refine ⟨hs.1,hs.2.1,hs.2.2,ReLUNetGame.subgamePerfect_iff_gateOptimal net hr x plus minus,?_⟩
  intro he
  dsimp only
  rw [ReLUNetGame.subgamePerfect_value net hr x plus minus he,
    ReLUNetGame.continuation_recovery _ _ _ _ _ _ (hrow i),sub_mulVec,mulVec_neg]
  rfl

end Thesis.SourceFoundations
