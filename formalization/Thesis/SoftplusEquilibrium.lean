import Thesis.SoftplusPolicies

noncomputable section
namespace Thesis.SoftplusGame
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward
open Thesis.ReLUNetGame Thesis.RoutingBackward Matrix
open scoped BigOperators

theorem optimal_lower_pair {n m} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x p q : Vec n) (hp : x≤p) (hq : -x≤q) (minus : Strategy net) :
    softEval θ net x≤(policyValue θ net (gibbsStrategy θ net x) minus p q).1 ∧
    -softEval θ net x≤(policyValue θ net (gibbsStrategy θ net x) minus p q).2 := by
  induction net with
  | output n => exact ⟨hp,hq⟩
  | layer wp wn bp bn tail ih =>
      have hweights : ∀ j i,0≤wp j i ∧ 0≤wn j i := fun j i => ⟨hw.1 j i,hw.2.1 j i⟩
      apply ih hw.2.2 _ _ _ _ _ minus.2
      · intro j
        have hm := continuation_mono_total wp wn hweights (bp-bn) hp hq j
        rw [(continuation_signed_total wp wn hweights bp bn x j).1] at hm
        change softplus θ (preactivation wp wn bp bn x j)≤
          gate θ (preactivation wp wn bp bn x j)*continuation wp wn (bp-bn) p q j+
            θ*Real.binEntropy (gate θ (preactivation wp wn bp bn x j))
        rw [← entropy_gate_value θ _ hθ]
        exact add_le_add (mul_le_mul_of_nonneg_left hm (gate_pos θ _).le) le_rfl
      · intro j
        have hm := continuation_mono_total wn wp (fun j i => ⟨(hweights j i).2,(hweights j i).1⟩)
          (bn-bp) hp hq j
        rw [(continuation_signed_total wp wn hweights bp bn x j).2] at hm
        change -softplus θ (preactivation wp wn bp bn x j)≤
          (minus.1 j).val*continuation wn wp (bn-bp) p q j-θ*Real.binEntropy (minus.1 j).val
        exact (entropy_min_bound θ _ hθ (minus.1 j)).trans
          (sub_le_sub_right (mul_le_mul_of_nonneg_left hm (minus.1 j).property.1) _)

theorem optimal_upper_pair {n m} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x p q : Vec n) (hp : p≤x) (hq : q≤ -x) (plus : Strategy net) :
    (policyValue θ net plus (gibbsStrategy θ net x) p q).1≤softEval θ net x ∧
    (policyValue θ net plus (gibbsStrategy θ net x) p q).2≤ -softEval θ net x := by
  induction net with
  | output n => exact ⟨hp,hq⟩
  | layer wp wn bp bn tail ih =>
      have hweights : ∀ j i,0≤wp j i ∧ 0≤wn j i := fun j i => ⟨hw.1 j i,hw.2.1 j i⟩
      apply ih hw.2.2 _ _ _ _ _ plus.2
      · intro j
        have hm := continuation_mono_total wp wn hweights (bp-bn) hp hq j
        rw [(continuation_signed_total wp wn hweights bp bn x j).1] at hm
        change (plus.1 j).val*continuation wp wn (bp-bn) p q j+
          θ*Real.binEntropy (plus.1 j).val≤softplus θ (preactivation wp wn bp bn x j)
        exact (add_le_add (mul_le_mul_of_nonneg_left hm (plus.1 j).property.1) le_rfl).trans
          (entropy_policy_le_softplus θ _ (plus.1 j).val hθ
            (plus.1 j).property.1 (plus.1 j).property.2)
      · intro j
        have hm := continuation_mono_total wn wp (fun j i => ⟨(hweights j i).2,(hweights j i).1⟩)
          (bn-bp) hp hq j
        rw [(continuation_signed_total wp wn hweights bp bn x j).2] at hm
        change gate θ (preactivation wp wn bp bn x j)*continuation wn wp (bn-bp) p q j-
          θ*Real.binEntropy (gate θ (preactivation wp wn bp bn x j))≤
          -softplus θ (preactivation wp wn bp bn x j)
        rw [← entropy_min_value θ _ hθ]
        exact sub_le_sub_right (mul_le_mul_of_nonneg_left hm (gate_pos θ _).le) _

/-- Actual saddle bounds against arbitrary full randomized policy profiles.
Zero-fan-in states are included, and discounts need not be at most one. -/
theorem softplus_saddle {n m} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net) :
    (policyValue θ net plus (gibbsStrategy θ net x) x (-x)).1≤softEval θ net x ∧
    (policyValue θ net plus (gibbsStrategy θ net x) x (-x)).2≤ -softEval θ net x ∧
    policyValue θ net (gibbsStrategy θ net x) (gibbsStrategy θ net x) x (-x)=
      (softEval θ net x,-softEval θ net x) ∧
    softEval θ net x≤(policyValue θ net (gibbsStrategy θ net x) minus x (-x)).1 ∧
    -softEval θ net x≤(policyValue θ net (gibbsStrategy θ net x) minus x (-x)).2 := by
  have hu := optimal_upper_pair net θ hθ hw x x (-x) le_rfl le_rfl plus
  have hl := optimal_lower_pair net θ hθ hw x x (-x) le_rfl le_rfl minus
  have hue := optimal_upper_pair net θ hθ hw x x (-x) le_rfl le_rfl (gibbsStrategy θ net x)
  have hle := optimal_lower_pair net θ hθ hw x x (-x) le_rfl le_rfl (gibbsStrategy θ net x)
  exact ⟨hu.1,hu.2,Prod.ext (le_antisymm hue.1 hle.1) (le_antisymm hue.2 hle.2),hl.1,hl.2⟩

/-- At every actual signed state the active player is a best response to the
evaluated predecessor subgames, quantified over every mixed stop/continue action.
The recursive boundary is the profile's own realized entropy-regularized payoff. -/
def SubgamePerfect {n m} (θ : ℝ) : (net : Network n m) → Strategy net → Strategy net →
    Vec n → Vec n → Prop
  | .output _, _, _, _, _ => True
  | .layer wp wn bp bn tail, plus, minus, p, q =>
      (∀ j,MaximizesEntropy θ (continuation wp wn (bp-bn) p q j) (plus.1 j)) ∧
      (∀ j,∀ a : Set.Icc (0 : ℝ) 1,
        (minus.1 j).val*continuation wn wp (bn-bp) p q j-θ*Real.binEntropy (minus.1 j).val≤
          a.val*continuation wn wp (bn-bp) p q j-θ*Real.binEntropy a.val) ∧
      SubgamePerfect θ tail plus.2 minus.2
        (fun j => (plus.1 j).val*continuation wp wn (bp-bn) p q j+θ*Real.binEntropy (plus.1 j).val)
        (fun j => (minus.1 j).val*continuation wn wp (bn-bp) p q j-θ*Real.binEntropy (minus.1 j).val)

/-- Positive-temperature strict concavity determines both players' complete
policies uniquely, even at zero preactivation and zero fan-in. -/
theorem subgamePerfect_iff {n m} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net) :
    SubgamePerfect θ net plus minus x (-x) ↔
      plus=gibbsStrategy θ net x ∧ minus=gibbsStrategy θ net x := by
  induction net with
  | output n => cases plus; cases minus; simp [SubgamePerfect,gibbsStrategy]; rfl
  | layer wp wn bp bn tail ih =>
      have hweights : ∀ j i,0≤wp j i ∧ 0≤wn j i := fun j i => ⟨hw.1 j i,hw.2.1 j i⟩
      have hp : ∀ j,continuation wp wn (bp-bn) x (-x) j=preactivation wp wn bp bn x j :=
        fun j => (continuation_signed_total wp wn hweights bp bn x j).1
      have hn : ∀ j,continuation wn wp (bn-bp) x (-x) j= -preactivation wp wn bp bn x j :=
        fun j => (continuation_signed_total wp wn hweights bp bn x j).2
      constructor
      · rintro ⟨hplus,hminus,ht⟩
        have heplus : plus.1=(fun j => gibbsProbability θ (preactivation wp wn bp bn x j)) := by
          funext j
          apply (maximizesEntropy_iff θ _ hθ _).mp
          simpa only [hp] using hplus j
        have heminus : minus.1=(fun j => gibbsProbability θ (preactivation wp wn bp bn x j)) := by
          funext j
          apply (minimizesEntropy_neg_iff θ _ hθ _).mp
          simpa only [hn] using hminus j
        simp only [hp,hn,heplus,heminus,gibbsProbability,entropy_gate_value θ _ hθ,
          entropy_min_value θ _ hθ] at ht
        have hrest := (ih hw.2.2 (softLayer θ wp wn bp bn x) plus.2 minus.2).mp ht
        exact ⟨Prod.ext heplus hrest.1,Prod.ext heminus hrest.2⟩
      · rintro ⟨rfl,rfl⟩
        refine ⟨?_,?_,?_⟩
        · intro j
          rw [hp]
          exact (maximizesEntropy_iff θ _ hθ _).mpr rfl
        · intro j
          rw [hn]
          exact (minimizesEntropy_neg_iff θ _ hθ _).mpr rfl
        · simp only [gibbsStrategy,hp,hn,gibbsProbability,entropy_gate_value θ _ hθ,
            entropy_min_value θ _ hθ]
          exact (ih hw.2.2 (softLayer θ wp wn bp bn x) _ _).mpr ⟨rfl,rfl⟩

theorem gibbs_subgamePerfect {n m} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x : Vec n) :
    SubgamePerfect θ net (gibbsStrategy θ net x) (gibbsStrategy θ net x) x (-x) :=
  (subgamePerfect_iff net θ hθ hw x _ _).mpr ⟨rfl,rfl⟩

end Thesis.SoftplusGame
