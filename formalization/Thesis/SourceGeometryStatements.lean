import Thesis.TropicalNetwork
import Thesis.CompactSupport
import Thesis.SupportDerivatives
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-! Source-facing bundled geometry theorems. Every set below is an actual convex
hull or Minkowski operation, and support is the supremum over that set. -/
noncomputable section
namespace Thesis.SourceGeometry
open Finset Matrix HiddenMonotonicity Thesis.Tropical
open scoped Pointwise
variable {I A : Type} [Fintype I] [Fintype A] [Nonempty A]

/-- The finite-hull vertex representation required in lem:support_properties.1. -/
theorem polytope_vertex_support (v : A → I → ℝ) (x : I → ℝ) :
    ∃ p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ,
      p ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x := by
  let P := convexHull ℝ (Set.range v)
  have hP : IsCompact P := (Set.finite_range v).isCompact_convexHull ℝ
  have hne : P.Nonempty := (Set.range_nonempty v).convexHull
  have hf : (P.extremePoints ℝ).Finite :=
    (Set.finite_range v).subset extremePoints_convexHull_subset
  have hcl : IsClosed (convexHull ℝ (P.extremePoints ℝ)) := hf.isClosed_convexHull ℝ
  have hHull : convexHull ℝ (P.extremePoints ℝ) = P := by
    have h := closure_convexHull_extremePoints hP (convex_convexHull ℝ _)
    rwa [hcl.closure_eq] at h
  obtain ⟨p,hp,he⟩ := support_attained hf.isCompact (hP.extremePoints_nonempty hne) x
  refine ⟨p,hp,?_⟩
  change p ⬝ᵥ x = support P x
  rw [← hHull,support_convexHull_compact hf.isCompact (hP.extremePoints_nonempty hne)]
  exact he

/-- lem:support_properties, all three numbered parts, at the original compact-convex scope.
The separate finite-polytope clause gives vertex attainment and the finite generator formula. -/
theorem support_properties (P Q : Set (I → ℝ)) (hP : IsCompact P) (hneP : P.Nonempty)
    (hcP : Convex ℝ P) (hQ : IsCompact Q) (hneQ : Q.Nonempty) (hcQ : Convex ℝ Q) :
    ConvexOn ℝ Set.univ (support P) ∧
    (∀ c : ℝ, 0 ≤ c → ∀ x, support P (c • x) = c*support P x) ∧
    (∀ x, support (P+Q) x = support P x+support Q x) ∧
    (∀ x, support (convexHull ℝ (P∪Q)) x = max (support P x) (support Q x)) ∧
    (P ⊆ Q ↔ ∀ x, support P x ≤ support Q x) ∧
    (support P = support Q → P = Q) ∧
    (∀ (v : A → I → ℝ) x, support (convexHull ℝ (Set.range v)) x = finiteMax (fun a => v a ⬝ᵥ x) ∧
      ∃ p ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ,
        p ⬝ᵥ x = support (convexHull ℝ (Set.range v)) x) := by
  exact ⟨support_convex hP hneP,support_homogeneous hP hneP,
    support_minkowski hP hneP hQ hneQ,support_hull_union hP hneP hQ hneQ,
    compact_subset_iff_support hP hneP hQ hneQ hcQ,
    compact_eq_of_support_eq hP hneP hcP hQ hneQ hcQ,
    fun v x => ⟨support_convexHull v x,polytope_vertex_support v x⟩⟩

/-- prop:newton_calculus, combining the actual set identities with their tropical
function identities and the lifted support representation. -/
theorem newton_calculus (p q : Tropical.Polynomial I) :
    (p.add q).newton = p.newton+q.newton ∧
    (p.max q).newton = convexHull ℝ (p.newton∪q.newton) ∧
    (∀ x, (p.add q).eval x=p.eval x+q.eval x) ∧
    (∀ x, (p.max q).eval x=max (p.eval x) (q.eval x)) ∧
    (∀ x, p.eval x=support p.lift.newton (Sum.elim x (fun _ => 1))) ∧
    ((∀ a, p.intercept a=0) → ∀ x, p.eval x=support p.newton x) :=
  ⟨p.newton_add q,p.newton_max q,p.eval_add q,p.eval_max q,p.lifted_support,p.eval_eq_support⟩

/-- Finite sums of independent monomial choices have exactly the weighted Minkowski Newton sum. -/
theorem weightedSum_newton {B : Type} [Fintype B] (w : B → ℝ)
    (p : B → Tropical.Polynomial I) :
    (Tropical.Polynomial.weightedSum w p).newton = ∑ b, w b • (p b).newton := by
  classical
  have hr : Set.range (Tropical.Polynomial.weightedSum w p).slope =
      ∑ b, w b • Set.range (p b).slope := by
    ext v
    constructor
    · rintro ⟨terms,rfl⟩
      apply (Set.mem_fintype_sum _ _).mpr
      refine ⟨fun b => w b • (p b).slope (terms b),?_,rfl⟩
      intro b
      exact ⟨(p b).slope (terms b),⟨terms b,rfl⟩,rfl⟩
    · intro hv
      obtain ⟨g,hg,he⟩ := (Set.mem_fintype_sum _ _).mp hv
      have hex : ∀ b, ∃ term : (p b).Terms, w b • (p b).slope term = g b := by
        intro b
        obtain ⟨u,⟨term,rfl⟩,hu⟩ := hg b
        exact ⟨term,hu⟩
      choose terms hterms using hex
      refine ⟨terms,?_⟩
      change (∑ b, w b • (p b).slope (terms b)) = v
      simpa only [hterms] using he
  rw [Tropical.Polynomial.newton,hr,convexHull_sum]
  simp only [convexHull_smul,Tropical.Polynomial.newton]

/-- The preactivation Newton polytope is the actual weighted Minkowski sum.
Bias coefficients do not affect the unlifted Newton polytope. -/
theorem affine_newton {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (b : Fin k → ℝ)
    (p q : Fin n → Tropical.Polynomial I) (i : Fin k) :
    (polynomialAffine wp wn b p q i).newton =
      (∑ j, wp i j • (p j).newton)+(∑ j, wn i j • (q j).newton) := by
  rw [polynomialAffine,Tropical.Polynomial.newton_add,Tropical.Polynomial.newton_add,
    weightedSum_newton,weightedSum_newton]
  have hz : (Tropical.Polynomial.monomial (0 : I → ℝ) (b i)).newton = {0} := by
    simp [Tropical.Polynomial.newton,Tropical.Polynomial.monomial,Set.range_const,convexHull_singleton]
  rw [hz]
  simp

/-- cor:minkowski_propagation, the exact local induction step for every neuron.
Applying this along tropicalSplit gives the full arbitrary-depth propagation. -/
theorem minkowski_propagation {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Fin k → ℝ) (p q : Fin n → Tropical.Polynomial I) (i : Fin k) :
    let Qp := (∑ j, wp i j • (p j).newton)+(∑ j, wn i j • (q j).newton)
    let Qn := (∑ j, wn i j • (p j).newton)+(∑ j, wp i j • (q j).newton)
    ((polynomialAffine wp wn bp p q i).max (polynomialAffine wn wp bn p q i)).newton =
      convexHull ℝ (Qp∪Qn) ∧ (polynomialAffine wn wp bn p q i).newton = Qn := by
  dsimp only
  rw [Tropical.Polynomial.newton_max,affine_newton,affine_newton]
  exact ⟨rfl,rfl⟩

/-- cor:polytopes_nonneg for the actual network-constructed imaginary polytopes. -/
theorem network_polytopes_nonnegative {n m} (net : Network n m) (hn : net.Nonnegative)
    (i : Fin m) :
    let polynomials := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
    (∀ v ∈ (polynomials.1 i).newton, ∀ j, 0 ≤ v j) ∧
    (∀ v ∈ (polynomials.2 i).newton, ∀ j, 0 ≤ v j) := by
  have h := tropicalSplit_nonnegative net hn (inputPolynomials n).1 (inputPolynomials n).2
    (fun j => coordinate_nonnegative (Sum.inl j)) (fun j => coordinate_nonnegative (Sum.inr j))
  exact ⟨Tropical.Polynomial.newton_nonnegative _ (h.1 i),
    Tropical.Polynomial.newton_nonnegative _ (h.2 i)⟩

/-- Actual weighted Minkowski/hull propagation on sets, independently of polynomial syntax. -/
def polytopeSplit {n m} : Network n m → (Fin n → Set (I → ℝ)) → (Fin n → Set (I → ℝ)) →
    (Fin m → Set (I → ℝ)) × (Fin m → Set (I → ℝ))
  | .output _, P, Q => (P,Q)
  | .layer wp wn _ _ tail, P, Q =>
      let Zp := fun i => (∑ j, wp i j • P j)+(∑ j, wn i j • Q j)
      let Zn := fun i => (∑ j, wn i j • P j)+(∑ j, wp i j • Q j)
      polytopeSplit tail (fun i => convexHull ℝ (Zp i∪Zn i)) Zn

/-- Complete arbitrary-depth weighted-polytope propagation agrees with the Newton
polytopes of the actual constructed split polynomials. -/
theorem tropicalSplit_newton {n m} (net : Network n m)
    (p q : Fin n → Tropical.Polynomial I) :
    ((fun i => ((tropicalSplit net p q).1 i).newton),
      (fun i => ((tropicalSplit net p q).2 i).newton)) =
      polytopeSplit net (fun j => (p j).newton) (fun j => (q j).newton) := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      simp only [tropicalSplit]
      rw [ih]
      simp only [Tropical.Polynomial.newton_max,affine_newton,polytopeSplit]

theorem coordinate_newton [DecidableEq I] (i : I) :
    (coordinate i).newton = {Pi.single i (1 : ℝ)} := by
  simp [coordinate,Tropical.Polynomial.monomial,Tropical.Polynomial.newton,
    Set.range_const,convexHull_singleton]

/-- cor:minkowski_propagation in one source-facing statement: basis-singleton
initial polytopes and every weighted Minkowski/hull layer, for the entire shared MLP. -/
theorem minkowski_propagation_network {n m} (net : Network n m) :
    let polynomials := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
    ((fun i => (polynomials.1 i).newton),(fun i => (polynomials.2 i).newton)) =
      polytopeSplit net (fun j => {Pi.single (Sum.inl j : Fin n ⊕ Fin n) (1 : ℝ)})
        (fun j => {Pi.single (Sum.inr j : Fin n ⊕ Fin n) (1 : ℝ)}) := by
  have h := tropicalSplit_newton net (inputPolynomials n).1 (inputPolynomials n).2
  simpa only [inputPolynomials,coordinate_newton] using h

/-- Basis-singleton initialization, all hidden weighted Minkowski/hull steps,
and the ungated signed affine output heads, including the zero-hidden-layer case. -/
theorem minkowski_propagation_affine_network {n m k} (net : Network n m)
    (wp wn : Matrix (Fin k) (Fin m) ℝ) (bp bn : Fin k → ℝ) :
    let hidden := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
    let sets := polytopeSplit net (fun j => {Pi.single (Sum.inl j : Fin n ⊕ Fin n) (1 : ℝ)})
      (fun j => {Pi.single (Sum.inr j : Fin n ⊕ Fin n) (1 : ℝ)})
    (∀ i, (hidden.1 i).newton=sets.1 i ∧ (hidden.2 i).newton=sets.2 i) ∧
    ∀ i, (polynomialAffine wp wn bp hidden.1 hidden.2 i).newton=
        (∑ j, wp i j • sets.1 j)+(∑ j, wn i j • sets.2 j) ∧
      (polynomialAffine wn wp bn hidden.1 hidden.2 i).newton=
        (∑ j, wn i j • sets.1 j)+(∑ j, wp i j • sets.2 j) := by
  have hs := minkowski_propagation_network net
  let hidden := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
  let sets := polytopeSplit net (fun j => {Pi.single (Sum.inl j : Fin n ⊕ Fin n) (1 : ℝ)})
    (fun j => {Pi.single (Sum.inr j : Fin n ⊕ Fin n) (1 : ℝ)})
  have hp : (fun i => (hidden.1 i).newton)=sets.1 := congrArg Prod.fst hs
  have hn : (fun i => (hidden.2 i).newton)=sets.2 := congrArg Prod.snd hs
  refine ⟨fun i => ⟨congrFun hp i,congrFun hn i⟩,?_⟩
  intro i
  change (polynomialAffine wp wn bp hidden.1 hidden.2 i).newton=
      (∑ j, wp i j • sets.1 j)+(∑ j, wn i j • sets.2 j) ∧
    (polynomialAffine wn wp bn hidden.1 hidden.2 i).newton=
      (∑ j, wn i j • sets.1 j)+(∑ j, wp i j • sets.2 j)
  rw [← hp,← hn]
  exact ⟨affine_newton wp wn bp hidden.1 hidden.2 i,
    affine_newton wn wp bn hidden.1 hidden.2 i⟩

end Thesis.SourceGeometry
