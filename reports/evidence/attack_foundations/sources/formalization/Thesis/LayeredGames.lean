import Thesis.Games
import Mathlib.Data.Finset.Lattice.Fold

/-! Finite layered, turn-based stochastic games. A state is `(remaining depth,s)`.
Transitions strictly decrease remaining depth, so discounts need not be less than one.
All randomized Markov policies are included; backward induction constructs pure
stationary policies on the layered state graph and proves their saddle inequalities. -/
noncomputable section
namespace Thesis.LayeredGames
open Finset
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- Data of the game, with ordinary normalized probabilities and structural discounts. -/
structure Game (S A : Type*) [Fintype S] where
  maximize : ℕ → S → Bool
  reward : ℕ → S → A → ℝ
  discount : ℕ → S → ℝ
  transition : ℕ → S → A → S → ℝ
  terminal : S → ℝ
  discount_nonneg : ∀ n s, 0 ≤ discount n s
  transition_nonneg : ∀ n s a t, 0 ≤ transition n s a t
  transition_sum : ∀ n s a, ∑ t, transition n s a t = 1

/-- Randomized policies at every nonterminal layered state. -/
structure Policy (S A : Type*) [Fintype A] where
  prob : ℕ → S → A → ℝ
  nonneg : ∀ n s a, 0 ≤ prob n s a
  sum_one : ∀ n s, ∑ a, prob n s a = 1

noncomputable def purePolicy (choose : ℕ → S → A) : Policy S A := by
  classical
  exact ⟨fun n s a => if a = choose n s then 1 else 0,
    fun _ _ _ => by split_ifs <;> norm_num,
    fun _ _ => by simp⟩

def best (maximize : Bool) (f : A → ℝ) : ℝ :=
  if maximize then univ.sup' univ_nonempty f else -univ.sup' univ_nonempty (fun a => -f a)

theorem best_attained (maximize : Bool) (f : A → ℝ) : ∃ a, best maximize f = f a := by
  cases maximize with
  | true =>
      obtain ⟨a,_,ha⟩ := univ.exists_mem_eq_sup' univ_nonempty f
      exact ⟨a,ha⟩
  | false =>
      obtain ⟨a,_,ha⟩ := univ.exists_mem_eq_sup' univ_nonempty (fun a => -f a)
      exact ⟨a,by simp [best,ha]⟩

noncomputable def selector (maximize : Bool) (f : A → ℝ) : A :=
  Classical.choose (best_attained maximize f)

theorem selector_value (maximize : Bool) (f : A → ℝ) :
    f (selector maximize f) = best maximize f :=
  (Classical.choose_spec (best_attained maximize f)).symm

theorem le_best_max (f : A → ℝ) (a : A) : f a ≤ best true f :=
  univ.le_sup' f (mem_univ a)

theorem best_min_le (f : A → ℝ) (a : A) : best false f ≤ f a := by
  have h := univ.le_sup' (fun a => -f a) (mem_univ a)
  change -univ.sup' univ_nonempty (fun a => -f a) ≤ f a
  linarith

/-- Continuation payoff, including the immediate reward and discount. -/
def Game.action (G : Game S A) (n : ℕ) (s : S) (a : A) (v : S → ℝ) : ℝ :=
  G.reward n s a + G.discount n s * ∑ t, G.transition n s a t * v t

def Game.value (G : Game S A) : ℕ → S → ℝ
  | 0, s => G.terminal s
  | n+1, s => best (G.maximize n s) (fun a => G.action n s a (G.value n))

def Game.optimalAction (G : Game S A) (n : ℕ) (s : S) : A :=
  selector (G.maximize n s) (fun a => G.action n s a (G.value n))

def Game.optimalPolicy (G : Game S A) : Policy S A := purePolicy G.optimalAction

/-- Expected discounted total payoff under a policy pair, recursively conditioning
on the first action and transition. Terminal reward is paid exactly once. -/
def Game.payoff (G : Game S A) (plus minus : Policy S A) : ℕ → S → ℝ
  | 0, s => G.terminal s
  | n+1, s => ∑ a, (if G.maximize n s then plus.prob n s a else minus.prob n s a) *
      G.action n s a (G.payoff plus minus n)

theorem Game.action_mono (G : Game S A) (n : ℕ) (s : S) (a : A)
    {v w : S → ℝ} (h : v ≤ w) : G.action n s a v ≤ G.action n s a w := by
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (G.discount_nonneg n s)
  exact sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h t) (G.transition_nonneg n s a t)

theorem average_le (π : Policy S A) (n : ℕ) (s : S) (f : A → ℝ) (b : ℝ)
    (h : ∀ a, f a ≤ b) : (∑ a, π.prob n s a * f a) ≤ b := by
  calc
    _ ≤ ∑ a, π.prob n s a * b := sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (h a) (π.nonneg n s a)
    _ = b := by rw [← sum_mul, π.sum_one, one_mul]

theorem le_average (π : Policy S A) (n : ℕ) (s : S) (f : A → ℝ) (b : ℝ)
    (h : ∀ a, b ≤ f a) : b ≤ ∑ a, π.prob n s a * f a := by
  calc
    b = ∑ a, π.prob n s a * b := by rw [← sum_mul, π.sum_one, one_mul]
    _ ≤ _ := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (π.nonneg n s a)

theorem pure_average (choose : ℕ → S → A) (n : ℕ) (s : S) (f : A → ℝ) :
    (∑ a, (purePolicy choose).prob n s a * f a) = f (choose n s) := by
  classical
  simp [purePolicy]

/-- The maximizing player's pure selector guarantees the Bellman value against
 every randomized opponent at every subgame. -/
theorem Game.optimal_lower (G : Game S A) (minus : Policy S A) (n : ℕ) :
    G.value n ≤ G.payoff G.optimalPolicy minus n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      intro s
      cases howner : G.maximize n s with
      | true =>
          simp only [Game.payoff, howner, ite_true]
          rw [show G.optimalPolicy = purePolicy G.optimalAction from rfl, pure_average]
          have he : G.action n s (G.optimalAction n s) (G.value n) = G.value (n+1) s :=
            selector_value (G.maximize n s) (fun a => G.action n s a (G.value n))
          rw [← he]
          exact G.action_mono n s _ ih
      | false =>
          simp only [Game.payoff, howner, Bool.false_eq_true, ite_false]
          apply le_average
          intro a
          calc
            G.value (n+1) s = best false (fun a => G.action n s a (G.value n)) := by
              simp only [Game.value, howner]
            _ ≤ G.action n s a (G.value n) := best_min_le _ a
            _ ≤ _ := G.action_mono n s a ih

/-- The minimizing player's pure selector guarantees the opposite saddle bound. -/
theorem Game.optimal_upper (G : Game S A) (plus : Policy S A) (n : ℕ) :
    G.payoff plus G.optimalPolicy n ≤ G.value n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      intro s
      cases howner : G.maximize n s with
      | false =>
          simp only [Game.payoff, howner, Bool.false_eq_true, ite_false]
          rw [show G.optimalPolicy = purePolicy G.optimalAction from rfl, pure_average]
          have he : G.action n s (G.optimalAction n s) (G.value n) = G.value (n+1) s :=
            selector_value (G.maximize n s) (fun a => G.action n s a (G.value n))
          rw [← he]
          exact G.action_mono n s _ ih
      | true =>
          simp only [Game.payoff, howner, ite_true]
          apply average_le
          intro a
          calc
            G.action n s a (G.payoff plus G.optimalPolicy n) ≤
                G.action n s a (G.value n) := G.action_mono n s a ih
            _ ≤ best true (fun a => G.action n s a (G.value n)) := le_best_max (fun a => G.action n s a (G.value n)) a
            _ = G.value (n+1) s := by simp only [Game.value, howner]

/-- thm:shapley_bellman / eq:saddle_point. One pure policy specifies the action at
each state; each player uses its restriction to the states that player controls. -/
theorem Game.saddle (G : Game S A) (plus minus : Policy S A) (n : ℕ) (s : S) :
    G.payoff plus G.optimalPolicy n s ≤ G.value n s ∧
    G.payoff G.optimalPolicy G.optimalPolicy n s = G.value n s ∧
    G.value n s ≤ G.payoff G.optimalPolicy minus n s := by
  exact ⟨G.optimal_upper plus n s,
    le_antisymm (G.optimal_upper G.optimalPolicy n s)
      (G.optimal_lower G.optimalPolicy n s), G.optimal_lower minus n s⟩

/-- No second solution of the layered Shapley--Bellman equations exists. -/
theorem Game.bellman_unique (G : Game S A) (v : ℕ → S → ℝ)
    (hzero : v 0 = G.terminal)
    (hstep : ∀ n s, v (n+1) s = best (G.maximize n s) (fun a => G.action n s a (v n))) :
    v = G.value := by
  funext n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      funext s
      rw [hstep, ih]
      rfl

end Thesis.LayeredGames
