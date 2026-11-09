import Thesis.RoutingNetwork
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma

noncomputable section
namespace Thesis.RoutingHistory
open HiddenMonotonicity Thesis.RoutingProfiles Thesis.RoutingExtended
open scoped BigOperators

/-- Full histories of the existing source tree. Activation stopping, the fair
oracle's two sign outcomes, and every routing action remain distinct. -/
@[reducible] def Histories : Tree → Type
  | .terminal _ => Unit
  | .activation _ p n => Unit ⊕ (Histories p ⊕ Histories n)
  | .routing k _ _ _ _ child => (i : Fin k) × Histories (child i)

instance historiesFintype : (t : Tree) → Fintype (Histories t)
  | .terminal _ => inferInstanceAs (Fintype Unit)
  | .activation _ p n => by
      letI := historiesFintype p
      letI := historiesFintype n
      exact inferInstanceAs (Fintype (Unit ⊕ (Histories p ⊕ Histories n)))
  | .routing k _ _ _ _ child => by
      letI (i : Fin k) := historiesFintype (child i)
      exact inferInstanceAs (Fintype ((i : Fin k) × Histories (child i)))

/-- Actual behavioral path probability for arbitrary profiles: the active
player's pure gate, fair sign oracle, and normalized routing policy. -/
def probability : (t : Tree) → Strategy t → Strategy t → Histories t → ℝ
  | .terminal _, _, _, _ => 1
  | .activation q p n, plus, minus, history =>
      if (if q then plus.1 else minus.1) then
        match history with
        | .inl _ => 0
        | .inr (.inl h) => (1/2)*probability p plus.2.1 minus.2.1 h
        | .inr (.inr h) => (1/2)*probability n plus.2.2 minus.2.2 h
      else match history with | .inl _ => 1 | _ => 0
  | .routing _ q _ _ _ child, plus, minus, history =>
      (if q then plus.1 else minus.1).prob history.1 *
        probability (child history.1) (plus.2 history.1) (minus.2 history.1) history.2

theorem probability_nonnegative (t : Tree) (plus minus : Strategy t) (h : Histories t) :
    0≤probability t plus minus h := by
  induction t with
  | terminal z => exact zero_le_one
  | activation q p n hp hn =>
      simp only [probability]
      by_cases hg : (if q then plus.1 else minus.1)=true
      · rw [if_pos hg]
        cases h with
        | inl _ => exact le_rfl
        | inr h => cases h with
          | inl h => exact mul_nonneg (by norm_num) (hp _ _ h)
          | inr h => exact mul_nonneg (by norm_num) (hn _ _ h)
      · rw [if_neg hg]
        cases h <;> norm_num
  | routing k q outside w hw child ih =>
      exact mul_nonneg ((if q then plus.1 else minus.1).nonnegative h.1) (ih _ _ _ h.2)

theorem probability_normalized (t : Tree) (plus minus : Strategy t) :
    (∑ h : Histories t,probability t plus minus h)=1 := by
  induction t with
  | terminal z => change (∑ _ : Unit,(1 : ℝ))=1; simp
  | activation q p n hp hn =>
      change (∑ h : Unit ⊕ (Histories p ⊕ Histories n),probability (.activation q p n) plus minus h)=1
      rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
      simp only [probability]
      split_ifs <;> simp [← Finset.mul_sum,hp,hn]
      all_goals norm_num
  | routing k q outside w hw child ih =>
      change (∑ h : (i : Fin k) × Histories (child i),probability (.routing k q outside w hw child) plus minus h)=1
      rw [Fintype.sum_sigma]
      simp only [probability,← Finset.mul_sum,ih,mul_one]
      exact (if q then plus.1 else minus.1).normalized

/-- A scalar observable attached to actual source-tree states. All copies of a
shared neuron may carry the same label; the tree only unfolds possible histories. -/
def Observation : Tree → Type
  | .terminal _ => ℝ
  | .activation _ p n => ℝ × Observation p × Observation n
  | .routing _ _ _ _ _ child => ℝ × ((i : _) → Observation (child i))

/-- Sum of rewards along the realized history with the source's cumulative
entered-state discounts. Entering positive/negative routing applies 2α/2β;
activation, terminal and ordinary routing moves add no further multiplier. -/
def pathReturn (α β : ℝ) : (t : Tree) → Observation t → Histories t → ℝ
  | .terminal _, obs, _ => obs
  | .activation _ p n, obs, h => obs.1 +
      match h with
      | .inl _ => 0
      | .inr (.inl rest) => (2*α)*pathReturn α β p obs.2.1 rest
      | .inr (.inr rest) => (2*β)*pathReturn α β n obs.2.2 rest
  | .routing _ _ _ _ _ child, obs, h => obs.1+pathReturn α β (child h.1) (obs.2 h.1) h.2

def integral (α β : ℝ) (t : Tree) (plus minus : Strategy t) (obs : Observation t) : ℝ :=
  ∑ h : Histories t, probability t plus minus h*pathReturn α β t obs h

theorem integral_terminal (α β z r : ℝ) (plus minus : Strategy (.terminal z)) :
    integral α β (.terminal z) plus minus r=r := by
  change (∑ _ : Unit,1*r)=r
  simp

theorem integral_activation (α β : ℝ) (q : Bool) (p n : Tree)
    (plus minus : Strategy (.activation q p n)) (obs : Observation (.activation q p n)) :
    integral α β (.activation q p n) plus minus obs = obs.1+
      if (if q then plus.1 else minus.1) then
        α*integral α β p plus.2.1 minus.2.1 obs.2.1+
          β*integral α β n plus.2.2 minus.2.2 obs.2.2 else 0 := by
  unfold integral
  change (∑ h : Unit ⊕ (Histories p ⊕ Histories n),probability (.activation q p n) plus minus h*pathReturn α β (.activation q p n) obs h)=_
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [probability,pathReturn]
  by_cases hg : (if q then plus.1 else minus.1)=true
  · simp only [hg,ite_true]
    simp_rw [show ∀ a b c d : ℝ,(1/2*a)*(b+2*c*d)=a*b/2+c*(a*d) by intros;ring]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_div,
      ← Finset.sum_mul,probability_normalized]
    simp
    ring
  · simp [hg,probability_normalized]

theorem integral_routing (α β : ℝ) (k : ℕ) (q : Bool) (outside : Fin k)
    (w : Fin k → ℝ) (hw : ∀ i,0≤w i) (child : Fin k → Tree)
    (plus minus : Strategy (.routing k q outside w hw child))
    (obs : Observation (.routing k q outside w hw child)) :
    integral α β (.routing k q outside w hw child) plus minus obs = obs.1+
      ∑ i,(if q then plus.1 else minus.1).prob i *
        integral α β (child i) (plus.2 i) (minus.2 i) (obs.2 i) := by
  unfold integral
  change (∑ h : (i : Fin k) × Histories (child i),probability (.routing k q outside w hw child) plus minus h*pathReturn α β (.routing k q outside w hw child) obs h)=_
  rw [Fintype.sum_sigma]
  simp only [probability,pathReturn]
  simp_rw [show ∀ a b c d : ℝ,(a*b)*(c+d)=a*c*b+a*(b*d) by intros;ring]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,probability_normalized,mul_one]
  rw [← Finset.sum_mul,(if q then plus.1 else minus.1).normalized,one_mul]

def canonicalIntegral (θ α β : ℝ) (t : Tree) (obs : Observation t) : ℝ :=
  integral α β t (canonical θ t) (canonical θ t) obs

def zeroObservation : (t : Tree) → Observation t
  | .terminal _ => (0 : ℝ)
  | .activation _ p n => (0,zeroObservation p,zeroObservation n)
  | .routing _ _ _ _ _ child => (0,fun i => zeroObservation (child i))

theorem zero_return (α β : ℝ) (t : Tree) (h : Histories t) :
    pathReturn α β t (zeroObservation t) h=0 := by
  induction t with
  | terminal _ => rfl
  | activation q p n hp hn => cases h with
    | inl _ => simp [pathReturn,zeroObservation]
    | inr h => cases h <;> simp [pathReturn,zeroObservation,hp,hn]
  | routing k q outside w hw child ih => simp [pathReturn,zeroObservation,ih]

def rootObservation (t : Tree) (r : ℝ) : Observation t :=
  match t with
  | .terminal _ => r
  | .activation _ p n => (r,zeroObservation p,zeroObservation n)
  | .routing _ _ _ _ _ child => (r,fun i => zeroObservation (child i))

theorem root_return (α β : ℝ) (t : Tree) (r : ℝ) (h : Histories t) :
    pathReturn α β t (rootObservation t r) h=r := by
  cases t with
  | terminal _ => rfl
  | activation q p n => cases h with
    | inl _ => simp [pathReturn,rootObservation]
    | inr h => cases h <;> simp [pathReturn,rootObservation,zero_return]
  | routing k q outside w hw child => simp [pathReturn,rootObservation,zero_return]

theorem integral_root (α β : ℝ) (t : Tree) (plus minus : Strategy t) (r : ℝ) :
    integral α β t plus minus (rootObservation t r)=r := by
  simp only [integral,root_return,← Finset.sum_mul,probability_normalized,one_mul]

end Thesis.RoutingHistory
