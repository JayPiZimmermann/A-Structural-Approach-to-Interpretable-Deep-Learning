import HiddenMonotonicity.ExpressionSubstitution

namespace HiddenMonotonicity

/-- A topologically ordered computation graph. Each new scalar node may use
any earlier node, so sharing, residual branches, pooling and flattened convolutions
are represented without assuming a chain of layers. -/
inductive Circuit (d : ℕ) : ℕ → Type
  | inputs : Circuit d d
  | node {n} (prior : Circuit d n) (operation : SignedExpr (Fin n)) : Circuit d (n+1)

noncomputable def Circuit.eval {d n} : Circuit d n → Vec d → Vec n
  | .inputs, x => x
  | .node prior op, x => Fin.snoc (prior.eval x) (op.eval (prior.eval x))

noncomputable def recenterPair (center : Bool) (p q : ℝ) : ℝ × ℝ :=
  if center then (p-min p q,q-min p q) else (p,q)

theorem recenterPair_difference (center : Bool) (p q : ℝ) :
    (recenterPair center p q).1-(recenterPair center p q).2=p-q := by
  cases center <;> simp [recenterPair] <;> ring

theorem recenterPair_nonnegative (center : Bool) (p q : ℝ) (hp : 0≤p) (hq : 0≤q) :
    0≤(recenterPair center p q).1 ∧ 0≤(recenterPair center p q).2 := by
  cases center
  · exact ⟨hp,hq⟩
  · exact ⟨sub_nonneg.mpr (min_le_left _ _),sub_nonneg.mpr (min_le_right _ _)⟩

/-- The actual split pass, optionally re-centering each newly evaluated node.
The same recorded earlier-node values are reused by all outgoing branches. -/
noncomputable def Circuit.split {d n} : Circuit d n → Bool → (Fin d × Bool → ℝ) → PairVec n
  | .inputs, _, x => (fun i => x (i,false), fun i => x (i,true))
  | .node prior op, center, x =>
      let s := prior.split center x
      let z := fun i : Fin _ × Bool => if i.2 then s.2 i.1 else s.1 i.1
      let out := recenterPair center (op.split.1.eval z) (op.split.2.eval z)
      (Fin.snoc s.1 out.1,Fin.snoc s.2 out.2)

/-- All-node difference invariance for arbitrary DAGs of affine, max and product
operations; in particular every supported CNN chunk obeys this theorem. -/
theorem Circuit.split_correct {d n} (c : Circuit d n) (center : Bool)
    (x : Fin d × Bool → ℝ) :
    (c.split center x).1-(c.split center x).2=c.eval (fun i => x (i,false)-x (i,true)) := by
  induction c with
  | inputs => rfl
  | @node n prior op ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Circuit.split, Circuit.eval, Fin.snoc_last, Pi.sub_apply]
        rw [recenterPair_difference,op.split_correct]
        congr 1
      · simpa only [Circuit.split, Circuit.eval, Fin.snoc_castSucc, Pi.sub_apply] using congrFun ih j

/-- Every node keeps a nonnegative pair, including optional re-centering. -/
theorem Circuit.split_nonnegative {d n} (c : Circuit d n) (center : Bool)
    (x : Fin d × Bool → ℝ) (hx : 0≤x) :
    0≤(c.split center x).1 ∧ 0≤(c.split center x).2 := by
  induction c with
  | inputs => exact ⟨fun i => hx (i,false),fun i => hx (i,true)⟩
  | @node n prior op ih =>
      have hz : 0 ≤ (fun i : Fin n × Bool =>
          if i.2 then (prior.split center x).2 i.1 else (prior.split center x).1 i.1) := by
        rintro ⟨i,b⟩
        cases b
        · exact ih.1 i
        · exact ih.2 i
      have hout := recenterPair_nonnegative center _ _
        (op.split.1.nonnegative _ hz) (op.split.2.nonnegative _ hz)
      constructor <;> intro i <;> refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Circuit.split, Fin.snoc_last, Pi.zero_apply] using hout.1
      · simpa only [Circuit.split, Fin.snoc_castSucc, Pi.zero_apply] using ih.1 j
      · simpa only [Circuit.split, Fin.snoc_last, Pi.zero_apply] using hout.2
      · simpa only [Circuit.split, Fin.snoc_castSucc, Pi.zero_apply] using ih.2 j

/-- A symbolic certificate for each split node, using the same shared-node
calculation. This is used only for proofs; the split algorithm remains a DAG pass. -/
noncomputable def Circuit.positiveExpressions {d n} : Circuit d n →
    (Fin n → PositiveExpr (Fin d × Bool)) × (Fin n → PositiveExpr (Fin d × Bool))
  | .inputs => (fun i => .input (i,false),fun i => .input (i,true))
  | .node prior op =>
      let s := prior.positiveExpressions
      let z := fun i : Fin _ × Bool => if i.2 then s.2 i.1 else s.1 i.1
      (Fin.snoc s.1 (op.split.1.substitute z),Fin.snoc s.2 (op.split.2.substitute z))

theorem Circuit.positiveExpressions_eval {d n} (c : Circuit d n) (x : Fin d × Bool → ℝ) :
    (fun i => (c.positiveExpressions.1 i).eval x)=(c.split false x).1 ∧
    (fun i => (c.positiveExpressions.2 i).eval x)=(c.split false x).2 := by
  induction c with
  | inputs => exact ⟨rfl,rfl⟩
  | @node n prior op ih =>
      constructor <;> funext i <;> refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Circuit.positiveExpressions, Fin.snoc_last, PositiveExpr.substitute_eval,
          Circuit.split, recenterPair, Bool.false_eq_true, ite_false]
        congr 1
        funext a
        cases a.2
        · exact congrFun ih.1 a.1
        · exact congrFun ih.2 a.1
      · simpa only [Circuit.positiveExpressions, Circuit.split, Fin.snoc_castSucc] using congrFun ih.1 j
      · simp only [Circuit.positiveExpressions, Fin.snoc_last, PositiveExpr.substitute_eval,
          Circuit.split, recenterPair, Bool.false_eq_true, ite_false]
        congr 1
        funext a
        cases a.2
        · exact congrFun ih.1 a.1
        · exact congrFun ih.2 a.1
      · simpa only [Circuit.positiveExpressions, Circuit.split, Fin.snoc_castSucc] using congrFun ih.2 j

def Circuit.Additive {d n} : Circuit d n → Prop
  | .inputs => True
  | .node prior op => prior.Additive ∧ op.Additive

theorem Circuit.positiveExpressions_additive {d n} (c : Circuit d n) (hc : c.Additive) :
    (∀ i, (c.positiveExpressions.1 i).Additive) ∧
    (∀ i, (c.positiveExpressions.2 i).Additive) := by
  induction c with
  | inputs => exact ⟨fun _ => trivial,fun _ => trivial⟩
  | @node n prior op ih =>
      have hi := ih hc.1
      have hz : ∀ i : Fin n × Bool,
          (if i.2 then prior.positiveExpressions.2 i.1 else prior.positiveExpressions.1 i.1).Additive := by
        intro i
        cases i.2
        · exact hi.1 i.1
        · exact hi.2 i.1
      constructor <;> intro i <;> refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Circuit.positiveExpressions, Fin.snoc_last] using
          op.split.1.substitute_additive _ hz (op.split_additive hc.2).1
      · simpa only [Circuit.positiveExpressions, Fin.snoc_castSucc] using hi.1 j
      · simpa only [Circuit.positiveExpressions, Fin.snoc_last] using
          op.split.2.substitute_additive _ hz (op.split_additive hc.2).2
      · simpa only [Circuit.positiveExpressions, Fin.snoc_castSucc] using hi.2 j

/-- CNN split convexity, with the essential restrictions explicit: no products
and no input-dependent re-centering in the convexity calculation. -/
theorem Circuit.cnn_split_convex {d n} (c : Circuit d n) (hc : c.Additive)
    (x y : Fin d × Bool → ℝ) (t : ℝ) (ht : 0≤t) (ht' : t≤1) (i : Fin n) :
    (c.split false (fun a => t*x a+(1-t)*y a)).1 i ≤
      t*(c.split false x).1 i+(1-t)*(c.split false y).1 i ∧
    (c.split false (fun a => t*x a+(1-t)*y a)).2 i ≤
      t*(c.split false x).2 i+(1-t)*(c.split false y).2 i := by
  have ha := c.positiveExpressions_additive hc
  have hg := (c.positiveExpressions.1 i).convex_additive (ha.1 i) x y t ht ht'
  have hh := (c.positiveExpressions.2 i).convex_additive (ha.2 i) x y t ht ht'
  simp only [congrFun (c.positiveExpressions_eval _).1 i,
    congrFun (c.positiveExpressions_eval _).2 i] at hg hh
  exact ⟨hg,hh⟩

/-- CNN split monotonicity of every recorded node in the shared graph. -/
theorem Circuit.cnn_split_monotone {d n} (c : Circuit d n) (hc : c.Additive)
    (x y : Fin d × Bool → ℝ) (hxy : x≤y) (i : Fin n) :
    (c.split false x).1 i≤(c.split false y).1 i ∧
    (c.split false x).2 i≤(c.split false y).2 i := by
  have ha := c.positiveExpressions_additive hc
  have hg := (c.positiveExpressions.1 i).monotone_additive (ha.1 i) x y hxy
  have hh := (c.positiveExpressions.2 i).monotone_additive (ha.2 i) x y hxy
  simp only [congrFun (c.positiveExpressions_eval _).1 i,
    congrFun (c.positiveExpressions_eval _).2 i] at hg hh
  exact ⟨hg,hh⟩

/-- Every split stream of a multiplicative DAG is a finite maximum of
nonnegative-coefficient polynomials on the nonnegative split-input orthant. -/
theorem Circuit.max_polynomial_streams {d n} (c : Circuit d n)
    (x : Fin d × Bool → ℝ) (hx : 0≤x) (i : Fin n) :
    (c.split false x).1 i=(c.positiveExpressions.1 i).polynomialMaximum.eval x ∧
    (c.split false x).2 i=(c.positiveExpressions.2 i).polynomialMaximum.eval x := by
  rw [PositiveExpr.max_polynomial_representation _ _ hx,
    PositiveExpr.max_polynomial_representation _ _ hx]
  exact ⟨(congrFun (c.positiveExpressions_eval x).1 i).symm,
    (congrFun (c.positiveExpressions_eval x).2 i).symm⟩

end HiddenMonotonicity
