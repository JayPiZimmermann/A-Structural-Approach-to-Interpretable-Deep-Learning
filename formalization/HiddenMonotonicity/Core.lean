import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Tactic

/-! Algebra and actual derivatives for the split-stream construction.
All derivatives below require explicit differentiability; no claim is made at ReLU kinks.
The algebraic backward recurrences also apply to a consistently chosen activation mask.
-/
namespace HiddenMonotonicity

def relu (x : ℝ) : ℝ := max x 0

theorem max_sub (p n : ℝ) : max p n - n = relu (p - n) := by
  unfold relu
  rcases le_total p n with h | h
  · rw [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]; ring
  · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]

def posPre (wp wn p n : ℝ) := wp * p + wn * n
def negPre (wp wn p n : ℝ) := wn * p + wp * n

theorem pre_difference (wp wn p n : ℝ) :
    posPre wp wn p n - negPre wp wn p n = (wp - wn) * (p - n) := by
  unfold posPre negPre; ring

theorem split_correct (wp wn p n : ℝ) :
    max (posPre wp wn p n) (negPre wp wn p n) - negPre wp wn p n =
      relu ((wp - wn) * (p - n)) := by
  rw [max_sub, pre_difference]

theorem max_common_shift (p n c : ℝ) : max (p + c) (n + c) = max p n + c := by
  exact max_add_add_right p n c

theorem pre_common_shift (wp wn p n c : ℝ) :
    posPre wp wn (p+c) (n+c) = posPre wp wn p n + (wp+wn)*c ∧
    negPre wp wn (p+c) (n+c) = negPre wp wn p n + (wp+wn)*c := by
  unfold posPre negPre; constructor <;> ring

/-- Actual multivariate chain rule for a head under the symmetric lift. -/
theorem lift_chain_rule (g : (ℝ × ℝ) → ℝ) (x : ℝ)
    (D : (ℝ × ℝ) →L[ℝ] ℝ) (hg : HasFDerivAt g D (x/2,-x/2)) :
    HasDerivAt (fun t => g (t/2,-t/2)) (D (1/2,-1/2)) x := by
  have hp : HasDerivAt (fun t : ℝ => t / 2) (1/2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have hn : HasDerivAt (fun t : ℝ => -t / 2) (-1/2) x := by
    convert (hasDerivAt_id x).const_mul (-1/2) using 1 <;> (first | rfl | (funext t; simp only [id_eq]; ring) | ring)
  exact hg.comp_hasDerivAt x (hp.prodMk hn)

/-- The differential on the symmetric direction is half the partial difference. -/
theorem lift_differential (D : (ℝ × ℝ) →L[ℝ] ℝ) :
    D (1/2,-1/2) = (D (1,0)-D (0,1))/2 := by
  have he : ((1/2,-1/2) : ℝ × ℝ) = (1/2 : ℝ) • (1,0) - (1/2 : ℝ) • (0,1) := by
    ext <;> norm_num
  rw [he, map_sub, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- ReLU has the expected derivative on its positive open region. -/
theorem relu_derivative_positive (x : ℝ) (hx : 0 < x) : HasDerivAt relu 1 x := by
  apply (hasDerivAt_id x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact max_eq_left (le_of_lt hy)

/-- ReLU has the expected derivative on its negative open region. -/
theorem relu_derivative_negative (x : ℝ) (hx : x < 0) : HasDerivAt relu 0 x := by
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
  exact max_eq_right (le_of_lt hy)

/-- Correct reconstruction from the four split partials includes a factor 1/2. -/
theorem backward_invariant (pg ng ph nh δ : ℝ)
    (h : (pg-ng)/2 - (ph-nh)/2 = δ) : pg-ng-ph+nh = 2*δ := by linarith

/-- A one-layer active ReLU, weight 1: partials are (1,0,0,1). -/
theorem paper_backward_invariant_counterexample :
    (1 : ℝ) - 0 - 0 + 1 ≠ 1 := by norm_num

/-- Pull back a head's two partials through one split layer with mask m. -/
def backPos (p n m wp wn : ℝ) := p*(m*wp+(1-m)*wn)+n*wn
def backNeg (p n m wp wn : ℝ) := p*(m*wn+(1-m)*wp)+n*wp

theorem backward_sum (p n m wp wn : ℝ) :
    backPos p n m wp wn + backNeg p n m wp wn = (p+n)*(wp+wn) := by
  unfold backPos backNeg; ring

theorem backward_difference (p n m wp wn : ℝ) :
    backPos p n m wp wn - backNeg p n m wp wn =
      (p-n)*m*(wp-wn) - (p+n)*(1-m)*(wp-wn) := by
  unfold backPos backNeg; ring

/-- Equal subtraction does not affect the signed difference. -/
theorem shift_difference (p n α : ℝ) :
    (p-α*(p+n)) - (n-α*(p+n)) = p-n := by ring

theorem shift_sum (p n α : ℝ) :
    (p-α*(p+n)) + (n-α*(p+n)) = (1-2*α)*(p+n) := by ring

/-- The local shift α cancels completely from the current layer's difference. -/
theorem shifted_backward_difference (p n m wp wn α : ℝ) :
    let bp := backPos p n m wp wn
    let bn := backNeg p n m wp wn
    (bp-α*(bp+bn))-(bn-α*(bp+bn)) =
      (p-n)*m*(wp-wn)-(p+n)*(1-m)*(wp-wn) := by
  dsimp; rw [shift_difference, backward_difference]

/-- Inactive one-layer ReLU, w=1, terminal α=0, local α=1/4.
The actual g lift derivative is -1/2; the printed j..L product gives -1/4. -/
theorem shifted_formula_counterexample :
    let bp := backPos 1 0 0 1 0
    let bn := backNeg 1 0 0 1 0
    ((bp-(1/4)*(bp+bn))-(bn-(1/4)*(bp+bn)))/2 = (-1/2 : ℝ) ∧
    (-1/2 : ℝ) ≠ -(1/2)*(1-2*(1/4)) := by norm_num [backPos, backNeg]

/-- The signed derivatives of both heads must reconstruct the original derivative. -/
theorem two_head_reconstruction (dG dH S D B : ℝ) :
    ((dG*D-S*B/2) - (dH*D-S*B/2)) = (dG-dH)*D := by ring

/-- xy fails the midpoint convexity inequality even on the positive quadrant. -/
theorem multiplicative_convexity_counterexample :
    let f : ℝ × ℝ → ℝ := fun p => p.1*p.2
    f ((1+3)/2,(3+1)/2) > (f (1,3)+f (3,1))/2 := by norm_num

end HiddenMonotonicity
