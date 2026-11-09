import HiddenMonotonicity.CircuitStatements

/-! Explicit shared positive pair-DAGs and their structural node/arc size.
Local expressions are finite trees attached to the preceding shared-state table;
an input leaf is a one-edge identity copy of the referenced previous state. -/
namespace HiddenMonotonicity

def PositiveExpr.vertices {ι} : PositiveExpr ι → ℕ
  | .input _ | .constant _ _ => 1
  | .scale _ _ a => a.vertices+1
  | .add a b | .mul a b | .maximum a b => a.vertices+b.vertices+1

def PositiveExpr.arcs {ι} : PositiveExpr ι → ℕ
  | .input _ => 1
  | .constant _ _ => 0
  | .scale _ _ a => a.arcs+1
  | .add a b | .mul a b | .maximum a b => a.arcs+b.arcs+2

def PositiveExpr.graphSize {ι} (e : PositiveExpr ι) : ℕ := e.vertices+e.arcs

theorem PositiveExpr.graphSize_le {ι} (e : PositiveExpr ι) : e.graphSize≤3*e.vertices := by
  induction e <;> simp_all [graphSize,vertices,arcs] <;> omega

/-- Each original node contributes two positive local trees. Both may refer to
any earlier pair, so the graph preserves sharing and arbitrary residual edges. -/
inductive SplitDAG (d : ℕ) : ℕ → Type
  | inputs : SplitDAG d d
  | node {n} (prior : SplitDAG d n)
      (positive negative : PositiveExpr (Fin n × Bool)) : SplitDAG d (n+1)

noncomputable def SplitDAG.eval {d n} : SplitDAG d n → (Fin d × Bool → ℝ) → PairVec n
  | .inputs, x => (fun i => x (i,false),fun i => x (i,true))
  | .node prior p q, x =>
      let s := prior.eval x
      let z := fun i : Fin _ × Bool => if i.2 then s.2 i.1 else s.1 i.1
      (Fin.snoc s.1 (p.eval z),Fin.snoc s.2 (q.eval z))

def SplitDAG.vertices {d n} : SplitDAG d n → ℕ
  | .inputs => 2*d
  | .node prior p q => prior.vertices+p.vertices+q.vertices

def SplitDAG.arcs {d n} : SplitDAG d n → ℕ
  | .inputs => 0
  | .node prior p q => prior.arcs+p.arcs+q.arcs

def SplitDAG.graphSize {d n} (g : SplitDAG d n) := g.vertices+g.arcs

noncomputable def Circuit.compileSplitDAG {d n} : Circuit d n → SplitDAG d n
  | .inputs => .inputs
  | .node prior op => .node prior.compileSplitDAG op.split.1 op.split.2

theorem Circuit.compileSplitDAG_eval {d n} (c : Circuit d n) (x : Fin d × Bool → ℝ) :
    c.compileSplitDAG.eval x=c.split false x := by
  induction c with
  | inputs => rfl
  | node prior op ih => simp [compileSplitDAG,SplitDAG.eval,Circuit.split,ih,recenterPair]

theorem SplitDAG.nonnegative {d n} (g : SplitDAG d n)
    (x : Fin d × Bool → ℝ) (hx : 0≤x) : 0≤g.eval x := by
  induction g with
  | inputs => exact ⟨fun i => hx (i,false),fun i => hx (i,true)⟩
  | @node n prior p q ih =>
      have hz : 0≤(fun i : Fin n × Bool => if i.2 then (prior.eval x).2 i.1 else (prior.eval x).1 i.1) := by
        rintro ⟨i,b⟩; cases b
        · exact ih.1 i
        · exact ih.2 i
      constructor <;> intro i <;> refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [SplitDAG.eval] using p.nonnegative _ hz
      · simpa [SplitDAG.eval] using ih.1 j
      · simpa [SplitDAG.eval] using q.nonnegative _ hz
      · simpa [SplitDAG.eval] using ih.2 j

theorem SplitDAG.monotone_nonnegative {d n} (g : SplitDAG d n)
    (x y : Fin d × Bool → ℝ) (hx : 0≤x) (hy : 0≤y) (hxy : x≤y) : g.eval x≤g.eval y := by
  induction g with
  | inputs => exact ⟨fun i => hxy (i,false),fun i => hxy (i,true)⟩
  | @node n prior p q ih =>
      let zx := fun i : Fin n × Bool => if i.2 then (prior.eval x).2 i.1 else (prior.eval x).1 i.1
      let zy := fun i : Fin n × Bool => if i.2 then (prior.eval y).2 i.1 else (prior.eval y).1 i.1
      have hzx : 0≤zx := by
        rintro ⟨i,b⟩; cases b
        · exact (prior.nonnegative x hx).1 i
        · exact (prior.nonnegative x hx).2 i
      have hzy : 0≤zy := by
        rintro ⟨i,b⟩; cases b
        · exact (prior.nonnegative y hy).1 i
        · exact (prior.nonnegative y hy).2 i
      have hzz : zx≤zy := by
        rintro ⟨i,b⟩; cases b
        · exact ih.1 i
        · exact ih.2 i
      constructor <;> intro i <;> refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [SplitDAG.eval] using p.monotone_nonnegative zx zy hzx hzy hzz
      · simpa [SplitDAG.eval] using ih.1 j
      · simpa [SplitDAG.eval] using q.monotone_nonnegative zx zy hzx hzy hzz
      · simpa [SplitDAG.eval] using ih.2 j

def SignedExpr.syntaxSize {ι} : SignedExpr ι → ℕ
  | .input _ | .constant _ => 1
  | .scale _ a => a.syntaxSize+1
  | .add a b | .mul a b | .maximum a b => a.syntaxSize+b.syntaxSize+1

/-- Additions do not duplicate their descendants under the actual split.
Scaling, products and maxima can duplicate them, each by at most a factor two. -/
def SignedExpr.duplicationDepth {ι} : SignedExpr ι → ℕ
  | .input _ | .constant _ => 0
  | .add a b => max a.duplicationDepth b.duplicationDepth
  | .scale _ a => a.duplicationDepth+1
  | .mul a b | .maximum a b => max a.duplicationDepth b.duplicationDepth+1

theorem SignedExpr.split_vertices_bound {ι} (e : SignedExpr ι) (D : ℕ)
    (hD : e.duplicationDepth≤D) :
    e.split.1.vertices+e.split.2.vertices≤8*2^D*e.syntaxSize := by
  induction e generalizing D with
  | input i | constant c =>
      simp only [duplicationDepth,split,PositiveExpr.vertices,syntaxSize] at *
      have hp : 1≤2^D := Nat.one_le_pow D 2 (by omega)
      nlinarith
  | add a b ha hb =>
      have hDa : a.duplicationDepth≤D := (le_max_left _ _).trans hD
      have hDb : b.duplicationDepth≤D := (le_max_right _ _).trans hD
      have h1 := ha D hDa
      have h2 := hb D hDb
      have hp : 1≤2^D := Nat.one_le_pow D 2 (by omega)
      simp only [split,PositiveExpr.vertices,syntaxSize]
      nlinarith
  | scale c a ha =>
      cases D with
      | zero => simp [duplicationDepth] at hD
      | succ D =>
          have hd : a.duplicationDepth≤D := by simpa [duplicationDepth] using hD
          have h1 := ha D hd
          have hp : 1≤2^D := Nat.one_le_pow D 2 (by omega)
          simp only [split,PositiveExpr.vertices,syntaxSize,pow_succ]
          nlinarith
  | mul a b ha hb | maximum a b ha hb =>
      cases D with
      | zero => simp [duplicationDepth] at hD
      | succ D =>
          have hd : max a.duplicationDepth b.duplicationDepth≤D := by simpa [duplicationDepth] using hD
          have h1 := ha D ((le_max_left _ _).trans hd)
          have h2 := hb D ((le_max_right _ _).trans hd)
          have hp : 1≤2^D := Nat.one_le_pow D 2 (by omega)
          simp only [split,PositiveExpr.vertices,syntaxSize,pow_succ]
          nlinarith

def Circuit.syntaxSize {d n} : Circuit d n → ℕ
  | .inputs => d
  | .node prior op => prior.syntaxSize+op.syntaxSize

def Circuit.BoundedDuplication {d n} : Circuit d n → ℕ → Prop
  | .inputs, _ => True
  | .node prior op, D => prior.BoundedDuplication D ∧ op.duplicationDepth≤D

/-- Linear size of the actual positive pair-DAG with all local syntax vertices
and arcs counted, while references to previous original nodes remain shared. -/
theorem Circuit.compileSplitDAG_size {d n} (c : Circuit d n) (D : ℕ)
    (hc : c.BoundedDuplication D) :
    c.compileSplitDAG.graphSize≤24*2^D*c.syntaxSize := by
  induction c with
  | inputs =>
      simp only [compileSplitDAG,SplitDAG.graphSize,SplitDAG.vertices,SplitDAG.arcs,syntaxSize,add_zero]
      have hp : 1≤2^D := Nat.one_le_pow D 2 (by omega)
      nlinarith
  | node prior op ih =>
      have h1 := ih hc.1
      have h2 := op.split_vertices_bound D hc.2
      have hp := op.split.1.graphSize_le
      have hq := op.split.2.graphSize_le
      simp only [compileSplitDAG,SplitDAG.graphSize,SplitDAG.vertices,SplitDAG.arcs,
        syntaxSize,PositiveExpr.graphSize] at *
      nlinarith

/-- Functional correctness, positivity, monotonicity and the quantitative
shared-graph bound, all for the same explicitly constructed split DAG. -/
theorem Circuit.split_DAG_with_size {d n} (c : Circuit d n) (D : ℕ)
    (hc : c.BoundedDuplication D) :
    c.compileSplitDAG.graphSize≤24*2^D*c.syntaxSize ∧
    (∀ x : Fin d × Bool → ℝ,
      (c.compileSplitDAG.eval x).1-(c.compileSplitDAG.eval x).2=
        c.eval (fun i => x (i,false)-x (i,true))) ∧
    (∀ x : Fin d × Bool → ℝ, 0≤x → 0≤c.compileSplitDAG.eval x) ∧
    (∀ x y : Fin d × Bool → ℝ, 0≤x → 0≤y → x≤y →
      c.compileSplitDAG.eval x≤c.compileSplitDAG.eval y) := by
  refine ⟨c.compileSplitDAG_size D hc,?_,c.compileSplitDAG.nonnegative,c.compileSplitDAG.monotone_nonnegative⟩
  intro x
  rw [c.compileSplitDAG_eval]
  exact c.split_correct false x

end HiddenMonotonicity
