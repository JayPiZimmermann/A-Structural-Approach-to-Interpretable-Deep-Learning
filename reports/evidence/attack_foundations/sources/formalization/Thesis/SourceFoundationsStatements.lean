import Thesis.Foundations
import Thesis.BellmanReturn
import Thesis.LayeredGames
import Thesis.ReLUNetEquilibrium
import Thesis.PiecewiseLinear
import Thesis.SourceGeometryStatements

/-! Bundled statements matching complete source claims, rather than one component
identity standing in for a multi-part theorem. -/
noncomputable section
namespace Thesis.SourceFoundations
open Finset Matrix HiddenMonotonicity Thesis.Tropical
open scoped NNReal

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

end Thesis.SourceFoundations
