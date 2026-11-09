import HiddenMonotonicity.Circuit
import HiddenMonotonicity.MaxPool

namespace HiddenMonotonicity

inductive PoolingRule
  | convex
  | winner
  deriving DecidableEq

/-- Forward both streams from the same actual maximizer, with left tie breaking. -/
noncomputable def winnerPair (a b : ℝ × ℝ) : ℝ × ℝ :=
  if b.1-b.2 ≤ a.1-a.2 then a else b

theorem winnerPair_recovery (a b : ℝ × ℝ) :
    (winnerPair a b).1-(winnerPair a b).2 = max (a.1-a.2) (b.1-b.2) := by
  unfold winnerPair
  split_ifs with h
  · exact (max_eq_left h).symm
  · exact (max_eq_right (le_of_lt (lt_of_not_ge h))).symm

theorem winnerPair_nonnegative (a b : ℝ × ℝ) (ha : 0≤a) (hb : 0≤b) :
    0≤winnerPair a b := by
  unfold winnerPair
  split_ifs <;> assumption

/-- Recursive WTA on a maximum tree forwards a single winning argument pair,
including finite pools represented by nested binary maxima in one graph node. -/
noncomputable def SignedExpr.poolTreeSplit {ι} : SignedExpr ι → (ι × Bool → ℝ) → ℝ × ℝ
  | .maximum a b, x => winnerPair (a.poolTreeSplit x) (b.poolTreeSplit x)
  | e, x => (e.split.1.eval x,e.split.2.eval x)

theorem SignedExpr.poolTreeSplit_correct {ι} (e : SignedExpr ι) (x : ι × Bool → ℝ) :
    (e.poolTreeSplit x).1-(e.poolTreeSplit x).2 = e.eval (fun i => x (i,false)-x (i,true)) := by
  induction e with
  | maximum a b ha hb => simp only [poolTreeSplit, winnerPair_recovery, ha, hb, eval]
  | _ => exact SignedExpr.split_correct _ x

theorem SignedExpr.poolTreeSplit_nonnegative {ι} (e : SignedExpr ι)
    (x : ι × Bool → ℝ) (hx : 0≤x) : 0≤e.poolTreeSplit x := by
  induction e with
  | maximum a b ha hb => exact winnerPair_nonnegative _ _ ha hb
  | _ => exact ⟨PositiveExpr.nonnegative _ x hx,PositiveExpr.nonnegative _ x hx⟩

/-- A node may either use the convex maximum split or forward both streams
from its actual maximizing pool argument. Other arithmetic uses the old split. -/
noncomputable def SignedExpr.splitAtNode {ι} (e : SignedExpr ι) (rule : PoolingRule)
    (x : ι × Bool → ℝ) : ℝ × ℝ :=
  match rule with
  | .winner => e.poolTreeSplit x
  | .convex => (e.split.1.eval x,e.split.2.eval x)

theorem SignedExpr.splitAtNode_correct {ι} (e : SignedExpr ι) (rule : PoolingRule)
    (x : ι × Bool → ℝ) :
    (e.splitAtNode rule x).1-(e.splitAtNode rule x).2 =
      e.eval (fun i => x (i,false)-x (i,true)) := by
  cases rule
  · exact e.split_correct x
  · exact e.poolTreeSplit_correct x

theorem SignedExpr.splitAtNode_nonnegative {ι} (e : SignedExpr ι) (rule : PoolingRule)
    (x : ι × Bool → ℝ) (hx : 0≤x) : 0≤e.splitAtNode rule x := by
  cases rule
  · exact ⟨e.split.1.nonnegative x hx,e.split.2.nonnegative x hx⟩
  · exact e.poolTreeSplit_nonnegative x hx

/-- The same Circuit graph with independent pooling and recentering policies at
its nodes. Node n appends its output after the n previously recorded values. -/
noncomputable def Circuit.splitWithPolicy {d n} : Circuit d n →
    (ℕ → PoolingRule) → (ℕ → Bool) → (Fin d × Bool → ℝ) → PairVec n
  | .inputs, _, _, x => (fun i => x (i,false),fun i => x (i,true))
  | .node (n := n) prior op, pooling, center, x =>
      let s := prior.splitWithPolicy pooling center x
      let z := fun i : Fin n × Bool => if i.2 then s.2 i.1 else s.1 i.1
      let v := op.splitAtNode (pooling n) z
      let out := recenterPair (center n) v.1 v.2
      (Fin.snoc s.1 out.1,Fin.snoc s.2 out.2)

/-- All-node recovery including actual WTA choice and independent per-node
recentering. No convexity assertion is made for these optional policies. -/
theorem Circuit.split_policy_correct {d n} (c : Circuit d n)
    (pooling : ℕ → PoolingRule) (center : ℕ → Bool) (x : Fin d × Bool → ℝ) :
    (c.splitWithPolicy pooling center x).1-(c.splitWithPolicy pooling center x).2 =
      c.eval (fun i => x (i,false)-x (i,true)) := by
  induction c with
  | inputs => rfl
  | @node n prior op ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Circuit.splitWithPolicy, Circuit.eval, Fin.snoc_last, Pi.sub_apply]
        rw [recenterPair_difference,op.splitAtNode_correct]
        congr 1
      · simpa only [Circuit.splitWithPolicy, Circuit.eval, Fin.snoc_castSucc, Pi.sub_apply]
          using congrFun ih j

theorem Circuit.split_policy_nonnegative {d n} (c : Circuit d n)
    (pooling : ℕ → PoolingRule) (center : ℕ → Bool) (x : Fin d × Bool → ℝ) (hx : 0≤x) :
    0≤c.splitWithPolicy pooling center x := by
  induction c with
  | inputs => exact ⟨fun i => hx (i,false),fun i => hx (i,true)⟩
  | @node n prior op ih =>
      have hz : 0 ≤ (fun i : Fin n × Bool =>
          if i.2 then (prior.splitWithPolicy pooling center x).2 i.1
          else (prior.splitWithPolicy pooling center x).1 i.1) := by
        rintro ⟨i,b⟩
        cases b
        · exact ih.1 i
        · exact ih.2 i
      have hv := op.splitAtNode_nonnegative (pooling n) _ hz
      have hout := recenterPair_nonnegative (center n) _ _ hv.1 hv.2
      constructor <;> intro i <;> refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Circuit.splitWithPolicy, Fin.snoc_last, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] using hout.1
      · simpa only [Circuit.splitWithPolicy, Fin.snoc_castSucc, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] using ih.1 j
      · simpa only [Circuit.splitWithPolicy, Fin.snoc_last, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] using hout.2
      · simpa only [Circuit.splitWithPolicy, Fin.snoc_castSucc, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] using ih.2 j

/-- Compatibility with the original graph pass when every pool is convex and
all nodes use its original common recentering choice. -/
theorem Circuit.split_policy_convex_eq {d n} (c : Circuit d n) (center : Bool)
    (x : Fin d × Bool → ℝ) :
    c.splitWithPolicy (fun _ => .convex) (fun _ => center) x = c.split center x := by
  induction c with
  | inputs => rfl
  | node prior op ih => simp only [Circuit.splitWithPolicy, Circuit.split,
      SignedExpr.splitAtNode, ih]

end HiddenMonotonicity
