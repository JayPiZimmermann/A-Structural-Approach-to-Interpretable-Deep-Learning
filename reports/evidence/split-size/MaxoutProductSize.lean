import HiddenMonotonicity.SplitDAGSize
import Thesis.Tropical

/-! Fixed-rank and bounded-total-degree size bounds for actual topological
Maxout multiplication graphs, with neurons and incoming arcs counted. -/
namespace HiddenMonotonicity
open Finset Matrix Thesis.Tropical

noncomputable def weightedInputs {ι} (terms : List (ℝ × ι)) : SignedExpr ι :=
  SignedExpr.sum (terms.map (fun t => .scale t.1 (.input t.2)))

theorem weightedInputs_eval {ι} (terms : List (ℝ × ι)) (x : ι → ℝ) :
    (weightedInputs terms).eval x=(terms.map (fun t => t.1*x t.2)).sum := by
  simp [weightedInputs,SignedExpr.sum_eval,List.map_map,SignedExpr.eval,Function.comp_def]

theorem weightedInputs_size {ι} (terms : List (ℝ × ι)) :
    (weightedInputs terms).syntaxSize=3*terms.length+1 := by
  induction terms with
  | nil => rfl
  | cons a as ih => simp only [weightedInputs,List.map_cons,SignedExpr.sum,SignedExpr.syntaxSize] at *; simp only [List.length_cons]; omega

theorem weightedInputs_depth {ι} (terms : List (ℝ × ι)) :
    (weightedInputs terms).duplicationDepth≤1 := by
  induction terms with
  | nil => simp [weightedInputs,SignedExpr.sum,SignedExpr.duplicationDepth]
  | cons a as ih => simpa [weightedInputs,SignedExpr.sum,SignedExpr.duplicationDepth] using ih

noncomputable def affineInputs {ι} (terms : List (ℝ × ι)) (bias : ℝ) : SignedExpr ι :=
  .add (.constant bias) (weightedInputs terms)

theorem affineInputs_eval {ι} (terms : List (ℝ × ι)) (bias : ℝ) (x : ι → ℝ) :
    (affineInputs terms bias).eval x=bias+(terms.map (fun t => t.1*x t.2)).sum := by
  simp [affineInputs,SignedExpr.eval,weightedInputs_eval]

theorem affineInputs_size {ι} (terms : List (ℝ × ι)) (bias : ℝ) :
    (affineInputs terms bias).syntaxSize=3*terms.length+3 := by
  simp [affineInputs,SignedExpr.syntaxSize,weightedInputs_size]; omega

theorem affineInputs_depth {ι} (terms : List (ℝ × ι)) (bias : ℝ) :
    (affineInputs terms bias).duplicationDepth≤1 := by
  simpa [affineInputs,SignedExpr.duplicationDepth] using weightedInputs_depth terms

theorem SignedExpr.maxList_size {ι} (first : SignedExpr ι) (es : List (SignedExpr ι)) :
    (SignedExpr.maxList first es).syntaxSize=
      first.syntaxSize+(es.map SignedExpr.syntaxSize).sum+es.length := by
  induction es with
  | nil => simp [maxList]
  | cons e es ih => simp [maxList,syntaxSize,ih]; omega

theorem SignedExpr.maxList_depth {ι} (first : SignedExpr ι) (es : List (SignedExpr ι))
    (hf : first.duplicationDepth≤1) (he : ∀ e∈es, e.duplicationDepth≤1) :
    (SignedExpr.maxList first es).duplicationDepth≤es.length+1 := by
  induction es with
  | nil => simpa [maxList] using hf
  | cons e es ih =>
      have h1 := he e (by simp)
      have h2 := ih (fun e he' => he e (by simp [he']))
      simp only [maxList,duplicationDepth,List.length_cons]
      omega

noncomputable def productInputs {ι} : List ι → SignedExpr ι
  | [] => .constant 1
  | i::is => .mul (.input i) (productInputs is)

theorem productInputs_eval {ι} (is : List ι) (x : ι → ℝ) :
    (productInputs is).eval x=(is.map x).prod := by
  induction is <;> simp_all [productInputs,SignedExpr.eval]

theorem productInputs_size {ι} (is : List ι) : (productInputs is).syntaxSize=2*is.length+1 := by
  induction is <;> simp_all [productInputs,SignedExpr.syntaxSize] <;> omega

theorem productInputs_depth {ι} (is : List ι) : (productInputs is).duplicationDepth=is.length := by
  induction is <;> simp_all [productInputs,SignedExpr.duplicationDepth]

/-- A Maxout neuron has a common list of incoming arcs and a vector of weights
on each arc. A multiplication neuron has natural exponents on its incoming arcs.
Biases are allowed directly and cost only a constant local overhead. -/
inductive MaxoutProductGate (n : ℕ)
  | maxout (fanIn rankPred : ℕ) (parent : Fin fanIn → Fin n)
      (weight : Matrix (Fin (rankPred+1)) (Fin fanIn) ℝ) (bias : Fin (rankPred+1) → ℝ)
  | monomial (fanIn : ℕ) (parent : Fin fanIn → Fin n) (power : Fin fanIn → ℕ)

def MaxoutProductGate.fanIn {n} : MaxoutProductGate n → ℕ
  | .maxout f _ _ _ _ | .monomial f _ _ => f

def MaxoutProductGate.rank {n} : MaxoutProductGate n → ℕ
  | .maxout _ r _ _ _ => r+1
  | .monomial _ _ _ => 1

def MaxoutProductGate.totalDegree {n} : MaxoutProductGate n → ℕ
  | .maxout _ _ _ _ _ => 0
  | .monomial _ _ w => ∑ i, w i

noncomputable def MaxoutProductGate.eval {n} : MaxoutProductGate n → Vec n → ℝ
  | .maxout _ _ p w b, x => finiteMax (fun j => b j+∑ i, w j i*x (p i))
  | .monomial _ parent power, x => ∏ i, x (parent i)^power i

noncomputable def repeatedParents {n f} (parent : Fin f → Fin n) (power : Fin f → ℕ) : List (Fin n) :=
  (List.ofFn (fun i => List.replicate (power i) (parent i))).flatten

theorem repeatedParents_length {n f} (parent : Fin f → Fin n) (power : Fin f → ℕ) :
    (repeatedParents parent power).length=∑ i, power i := by
  simp [repeatedParents,List.length_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]

theorem repeatedParents_product {n f} (parent : Fin f → Fin n) (power : Fin f → ℕ) (x : Vec n) :
    ((repeatedParents parent power).map x).prod=∏ i, x (parent i)^power i := by
  simp [repeatedParents,List.map_flatten,List.prod_flatten,List.map_ofFn,List.prod_ofFn,Function.comp_def]

noncomputable def MaxoutProductGate.toExpr {n} : MaxoutProductGate n → SignedExpr (Fin n)
  | .maxout _ r p w b =>
      let branch := fun j => affineInputs (List.ofFn (fun i => (w j i,p i))) (b j)
      SignedExpr.maxList (branch 0) (List.ofFn (fun j : Fin r => branch j.succ))
  | .monomial _ p w => productInputs (repeatedParents p w)

private theorem foldMax_first (a : ℝ) (xs : List ℝ) : a≤xs.foldr max a := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact ih.trans (le_max_right _ _)

private theorem foldMax_bound (a c : ℝ) (xs : List ℝ) (ha : a≤c) (hx : ∀ x∈xs, x≤c) :
    xs.foldr max a≤c := by
  induction xs with
  | nil => exact ha
  | cons x xs ih => exact max_le (hx x (by simp)) (ih (fun y hy => hx y (by simp [hy])))

private theorem maxList_fin_eval {ι k} (e : Fin (k+1) → SignedExpr ι) (x : ι → ℝ) :
    (SignedExpr.maxList (e 0) (List.ofFn (fun j : Fin k => e j.succ))).eval x=
      finiteMax (fun j => (e j).eval x) := by
  rw [SignedExpr.maxList_eval]
  have hfold : (List.ofFn (fun j : Fin k => e j.succ)).foldr
      (fun a v => max (a.eval x) v) ((e 0).eval x)=
      (List.ofFn (fun j : Fin k => (e j.succ).eval x)).foldr max ((e 0).eval x) := by
    rw [← List.foldr_map]
    simp [List.map_ofFn,Function.comp_def]
  rw [hfold]
  apply le_antisymm
  · apply foldMax_bound
    · exact le_finiteMax (fun j => (e j).eval x) 0
    · intro y hy
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hy
      exact le_finiteMax (fun j => (e j).eval x) j.succ
  · apply finiteMax_le
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact foldMax_first _ _
    · exact List.le_max_of_le' _ (List.mem_ofFn.mpr ⟨i,rfl⟩) le_rfl

theorem MaxoutProductGate.toExpr_eval {n} (g : MaxoutProductGate n) (x : Vec n) :
    g.toExpr.eval x=g.eval x := by
  cases g with
  | maxout f r p w b =>
      simp only [toExpr,eval]
      rw [maxList_fin_eval (fun j : Fin (r+1) => affineInputs (List.ofFn (fun i => (w j i,p i))) (b j)) x]
      congr 1
      funext j
      simp [affineInputs_eval,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  | monomial f p w => simp only [toExpr,eval,productInputs_eval,repeatedParents_product]

theorem MaxoutProductGate.toExpr_depth {n} (g : MaxoutProductGate n) :
    g.toExpr.duplicationDepth≤max g.rank g.totalDegree := by
  cases g with
  | maxout f r p w b =>
      have hh := SignedExpr.maxList_depth
        (affineInputs (List.ofFn (fun i => (w 0 i,p i))) (b 0))
        (List.ofFn (fun j : Fin r => affineInputs (List.ofFn (fun i => (w j.succ i,p i))) (b j.succ)))
        (affineInputs_depth _ _) (by
          intro e he
          obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
          exact affineInputs_depth _ _)
      simpa [toExpr,rank,totalDegree] using hh
  | monomial f p w => simp [toExpr,rank,totalDegree,productInputs_depth,repeatedParents_length]

theorem MaxoutProductGate.toExpr_size {n} (g : MaxoutProductGate n) (K D : ℕ)
    (hK : g.rank≤K) (hD : g.totalDegree≤D) :
    g.toExpr.syntaxSize≤(4*K+2*D+1)*(g.fanIn+1) := by
  cases g with
  | maxout f r p w b =>
      simp only [rank,totalDegree,fanIn] at *
      simp [toExpr,SignedExpr.maxList_size,affineInputs_size,List.map_ofFn,List.sum_ofFn]
      nlinarith
  | monomial f p w =>
      simp only [rank,totalDegree,fanIn] at *
      simp only [toExpr,productInputs_size,repeatedParents_length]
      nlinarith



/-- Maximum arity of a max gate in the positive local syntax. Addition and
scaling are rank-one affine gates; multiplication is a monomial gate. -/
def PositiveExpr.maxoutRank {ι} : PositiveExpr ι → ℕ
  | .input _ | .constant _ _ => 1
  | .scale _ _ a => max 1 a.maxoutRank
  | .add a b | .mul a b => max 1 (max a.maxoutRank b.maxoutRank)
  | .maximum a b => max 2 (max a.maxoutRank b.maxoutRank)

theorem PositiveExpr.maxoutRank_le_two {ι} (e : PositiveExpr ι) : e.maxoutRank≤2 := by
  induction e <;> simp_all [maxoutRank]

def SplitDAG.maxoutRank {d n} : SplitDAG d n → ℕ
  | .inputs => 1
  | .node prior p q => max prior.maxoutRank (max p.maxoutRank q.maxoutRank)

theorem SplitDAG.maxoutRank_le_two {d n} (g : SplitDAG d n) : g.maxoutRank≤2 := by
  induction g with
  | inputs => change 1≤2; omega
  | node prior p q ih => exact max_le ih (max_le p.maxoutRank_le_two q.maxoutRank_le_two)

/-- Actual finite topologically ordered source graphs. Parents in a gate may be
any earlier node, so sharing and residual arcs are retained. -/
inductive MaxoutProductDAG (d : ℕ) : ℕ → Type
  | inputs : MaxoutProductDAG d d
  | node {n} (prior : MaxoutProductDAG d n) (gate : MaxoutProductGate n) : MaxoutProductDAG d (n+1)

noncomputable def MaxoutProductDAG.eval {d n} : MaxoutProductDAG d n → Vec d → Vec n
  | .inputs, x => x
  | .node prior gate, x => Fin.snoc (prior.eval x) (gate.eval (prior.eval x))

/-- Source size counts input and internal neurons, plus every original incoming
arc once; a Maxout arc carries its whole rank-vector of scalar weights. -/
def MaxoutProductDAG.graphSize {d n} : MaxoutProductDAG d n → ℕ
  | .inputs => d
  | .node prior gate => prior.graphSize+1+gate.fanIn

def MaxoutProductDAG.BoundedRankDegree {d n} : MaxoutProductDAG d n → ℕ → ℕ → Prop
  | .inputs, _, _ => True
  | .node prior gate, K, D => prior.BoundedRankDegree K D ∧ gate.rank≤K ∧ gate.totalDegree≤D

noncomputable def MaxoutProductDAG.toCircuit {d n} : MaxoutProductDAG d n → Circuit d n
  | .inputs => .inputs
  | .node prior gate => .node prior.toCircuit gate.toExpr

theorem MaxoutProductDAG.toCircuit_eval {d n} (c : MaxoutProductDAG d n) (x : Vec d) :
    c.toCircuit.eval x=c.eval x := by
  induction c with
  | inputs => rfl
  | node prior gate ih => simp [toCircuit,Circuit.eval,eval,ih,MaxoutProductGate.toExpr_eval]

theorem MaxoutProductDAG.toCircuit_depth_bound {d n} (c : MaxoutProductDAG d n) (K D : ℕ)
    (hc : c.BoundedRankDegree K D) : c.toCircuit.BoundedDuplication (max K D) := by
  induction c with
  | inputs => trivial
  | node prior gate ih =>
      exact ⟨ih hc.1,gate.toExpr_depth.trans (max_le_max hc.2.1 hc.2.2)⟩

theorem MaxoutProductDAG.toCircuit_size {d n} (c : MaxoutProductDAG d n) (K D : ℕ)
    (hc : c.BoundedRankDegree K D) :
    c.toCircuit.syntaxSize≤(4*K+2*D+1)*c.graphSize := by
  induction c with
  | inputs => simp [toCircuit,Circuit.syntaxSize,graphSize]; nlinarith
  | node prior gate ih =>
      have h1 := ih hc.1
      have h2 := gate.toExpr_size K D hc.2.1 hc.2.2
      simp only [toCircuit,Circuit.syntaxSize,graphSize]
      nlinarith

noncomputable def MaxoutProductDAG.compile {d n} (c : MaxoutProductDAG d n) : SplitDAG d n :=
  c.toCircuit.compileSplitDAG

theorem MaxoutProductDAG.compile_size {d n} (c : MaxoutProductDAG d n) (K D : ℕ)
    (hc : c.BoundedRankDegree K D) :
    c.compile.graphSize≤(24*2^(max K D)*(4*K+2*D+1))*c.graphSize := by
  calc
    c.compile.graphSize≤24*2^(max K D)*c.toCircuit.syntaxSize :=
      c.toCircuit.compileSplitDAG_size _ (c.toCircuit_depth_bound K D hc)
    _ ≤ 24*2^(max K D)*((4*K+2*D+1)*c.graphSize) :=
      Nat.mul_le_mul_left _ (c.toCircuit_size K D hc)
    _ = _ := by ring

theorem MaxoutProductDAG.compile_recovery {d n} (c : MaxoutProductDAG d n)
    (x : Fin d × Bool → ℝ) :
    (c.compile.eval x).1-(c.compile.eval x).2=c.eval (fun i => x (i,false)-x (i,true)) := by
  rw [compile,Circuit.compileSplitDAG_eval,Circuit.split_correct,toCircuit_eval]

/-- Literal recovery on the source's canonical nonnegative input split. -/
theorem MaxoutProductDAG.compile_canonical_recovery {d n} (c : MaxoutProductDAG d n)
    (x : Vec d) : c.eval x=(c.compile.eval (canonicalSplitInput x)).1-
      (c.compile.eval (canonicalSplitInput x)).2 := by
  rw [c.compile_recovery]
  congr 1
  funext i
  exact (canonicalSplitInput_difference x i).symm

theorem MaxoutProductDAG.compile_polynomials {d n} (c : MaxoutProductDAG d n) (i : Fin n) :
    ∃ P Q : MaxPolynomial (Fin d × Bool), ∀ x : Fin d × Bool → ℝ, 0≤x →
      (c.compile.eval x).1 i=P.eval x ∧ (c.compile.eval x).2 i=Q.eval x := by
  refine ⟨(c.toCircuit.positiveExpressions.1 i).polynomialMaximum,
    (c.toCircuit.positiveExpressions.2 i).polynomialMaximum,?_⟩
  intro x hx
  rw [compile,Circuit.compileSplitDAG_eval]
  exact c.toCircuit.max_polynomial_streams x hx i

/-- The fixed-rank/bounded-total-degree source theorem, including an actual
rank-two positive shared DAG, exact all-node recovery, positivity, monotonicity,
finite max-polynomial representations, and an explicit linear node-plus-arc bound. -/
theorem MaxoutProductDAG.split_linear_size {d n} (c : MaxoutProductDAG d n) (K D : ℕ)
    (hc : c.BoundedRankDegree K D) :
    ∃ g : SplitDAG d n,
      g.maxoutRank≤2 ∧ g.graphSize≤(24*2^(max K D)*(4*K+2*D+1))*c.graphSize ∧
      (∀ x : Fin d × Bool → ℝ, (g.eval x).1-(g.eval x).2=
        c.eval (fun i => x (i,false)-x (i,true))) ∧
      (∀ x : Fin d × Bool → ℝ, 0≤x → 0≤g.eval x) ∧
      (∀ x y : Fin d × Bool → ℝ, 0≤x → 0≤y → x≤y → g.eval x≤g.eval y) ∧
      (∀ i : Fin n, ∃ P Q : MaxPolynomial (Fin d × Bool),
        ∀ x : Fin d × Bool → ℝ, 0≤x → (g.eval x).1 i=P.eval x ∧ (g.eval x).2 i=Q.eval x) :=
  ⟨c.compile,c.compile.maxoutRank_le_two,c.compile_size K D hc,c.compile_recovery,
    c.compile.nonnegative,c.compile.monotone_nonnegative,c.compile_polynomials⟩

/-- The actual number of binomial monomials before collecting equal terms. -/
def MaxoutProductGate.expandedTerms {n} : MaxoutProductGate n → ℕ
  | .maxout _ _ _ _ _ => 0
  | .monomial _ _ power => ∏ i, (power i+1)

private theorem sum_add_one_le_prod_succ {A : Type} [DecidableEq A]
    (s : Finset A) (w : A → ℕ) : (∑ i∈s,w i)+1≤∏ i∈s,(w i+1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hm := Nat.mul_le_mul_left (w a+1) ih
      have hn : 0≤w a*(∑ i∈s,w i) := Nat.zero_le _
      simp [ha]
      nlinarith

theorem MaxoutProductGate.degree_le_expandedTerms {n} (g : MaxoutProductGate n) :
    g.totalDegree≤g.expandedTerms := by
  cases g with
  | maxout => exact le_rfl
  | monomial f parent power =>
      have hh := sum_add_one_le_prod_succ univ power
      change (∑ i,power i)≤∏ i,(power i+1)
      omega

def MaxoutProductDAG.BoundedRankExpansion {d n} : MaxoutProductDAG d n → ℕ → ℕ → Prop
  | .inputs, _, _ => True
  | .node prior gate, K, B => prior.BoundedRankExpansion K B ∧ gate.rank≤K ∧ gate.expandedTerms≤B

theorem MaxoutProductDAG.degree_bound_of_expansion {d n} (c : MaxoutProductDAG d n) (K B : ℕ)
    (hc : c.BoundedRankExpansion K B) : c.BoundedRankDegree K B := by
  induction c with
  | inputs => trivial
  | node prior gate ih => exact ⟨ih hc.1,hc.2.1,gate.degree_le_expandedTerms.trans hc.2.2⟩

/-- The main thesis's expanded-monomial-count hypothesis implies the actual
linear node-plus-arc bound for the same explicit monotone split DAG. -/
theorem MaxoutProductDAG.split_linear_size_expansion {d n} (c : MaxoutProductDAG d n) (K B : ℕ)
    (hc : c.BoundedRankExpansion K B) :
    ∃ g : SplitDAG d n,
      g.maxoutRank≤2 ∧ g.graphSize≤(24*2^(max K B)*(4*K+2*B+1))*c.graphSize ∧
      (∀ x : Fin d × Bool → ℝ, (g.eval x).1-(g.eval x).2=
        c.eval (fun i => x (i,false)-x (i,true))) ∧
      (∀ x : Fin d × Bool → ℝ, 0≤x → 0≤g.eval x) ∧
      (∀ x y : Fin d × Bool → ℝ, 0≤x → 0≤y → x≤y → g.eval x≤g.eval y) ∧
      (∀ i : Fin n, ∃ P Q : MaxPolynomial (Fin d × Bool),
        ∀ x : Fin d × Bool → ℝ, 0≤x → (g.eval x).1 i=P.eval x ∧ (g.eval x).2 i=Q.eval x) :=
  c.split_linear_size K B (c.degree_bound_of_expansion K B hc)

end HiddenMonotonicity
