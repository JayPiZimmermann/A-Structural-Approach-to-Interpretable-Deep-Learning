import HiddenMonotonicity.Decomposition
import Thesis.BackwardGames

/-! The actual gated stopping decomposition on the shared MLP. At a strict
activation cell both streams have genuine derivatives; ties are not called
classically differentiable. -/
noncomputable section
namespace Thesis.StoppingDecomposition
open HiddenMonotonicity Matrix Finset Filter
open Thesis.BackwardGames
open scoped Topology

def stopPair (z : ℝ × ℝ) : ℝ × ℝ :=
  (if z.2 < z.1 then z.1 else 0, if z.2 < z.1 then z.2 else 0)

theorem stopPair_valid : ValidPairActivation relu stopPair := by
  intro p q
  by_cases h : q < p
  · simp [stopPair, h, relu, max_eq_left (sub_nonneg.mpr h.le)]
  · simp [stopPair, h, relu, max_eq_right (sub_nonpos.mpr (le_of_not_gt h))]

theorem stopPair_nonnegative : NonnegativePairActivation stopPair := by
  intro p q hp hq
  by_cases h : q < p
  · simpa [stopPair, h] using And.intro hp hq
  · simp [stopPair, h]

/-- Source thm:stopping_validity and ptnb:thm:decomp-recovery on the full network. -/
theorem thesis_stopping_validity {n m} (net : Network n m) (x : PairVec n) :
    (net.decomposeWith stopPair x).1 - (net.decomposeWith stopPair x).2 = net.eval (x.1-x.2) := by
  rw [← net.forwardWith_relu]
  exact net.valid_decomposition_recovery relu stopPair stopPair_valid x

theorem stopping_nonnegative {n m} (net : Network n m) (hp : net.NonnegativeParameters)
    (x : PairVec n) (hx : 0 ≤ x.1 ∧ 0 ≤ x.2) :
    0 ≤ (net.decomposeWith stopPair x).1 ∧ 0 ≤ (net.decomposeWith stopPair x).2 :=
  net.decomposition_nonnegative hp stopPair stopPair_nonnegative x hx

def stopLayer {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (x : PairVec n) : PairVec k :=
  ((fun j => (stopPair ((preP wp wn x+bp) j,(preN wp wn x+bn) j)).1),
   (fun j => (stopPair ((preP wp wn x+bp) j,(preN wp wn x+bn) j)).2))

def stopLayerJac {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (g : Fin k → Bool) :
    PairVec n →L[ℝ] PairVec k :=
  ((MaskedTrace.activeMap g).comp (preP wp wn)).prod ((MaskedTrace.activeMap g).comp (preN wp wn))

def stoppingJac {n m} : MaskedTrace n m → (PairVec n →L[ℝ] PairVec m)
  | .output _ => ContinuousLinearMap.id ℝ _
  | .layer wp wn g tail => (stoppingJac tail).comp (stopLayerJac wp wn g)

theorem stopLayer_difference {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) :
    (stopLayer wp wn bp bn x).1 - (stopLayer wp wn bp bn x).2 = reluLayer wp wn bp bn (x.1-x.2) := by
  funext j
  change (stopPair ((preP wp wn x+bp) j,(preN wp wn x+bn) j)).1 -
    (stopPair ((preP wp wn x+bp) j,(preN wp wn x+bn) j)).2 = _
  rw [stopPair_valid]
  change relu ((preP wp wn x+bp-(preN wp wn x+bn)) j) = _
  rw [preactivation_difference]
  rfl

theorem layerGate_original {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) :
    (fun j => decide ((preN wp wn x+bn) j < (preP wp wn x+bp) j)) =
      originalGate wp wn bp bn (x.1-x.2) := by
  funext j
  have h := congrFun (preactivation_difference wp wn bp bn x) j
  simp only [Pi.sub_apply] at h
  simp only [originalGate]
  simp only [← h, sub_pos]

theorem gated_projection {n k} (g : Fin k → Bool) (D : PairVec n →L[ℝ] Vec k) (j : Fin k) :
    (ContinuousLinearMap.proj j).comp ((MaskedTrace.activeMap g).comp D) =
      if g j then (ContinuousLinearMap.proj j).comp D else 0 := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, MaskedTrace.activeMap_apply,
    ContinuousLinearMap.proj_apply]
  cases g j <;> rfl

/-- Actual derivative of a strictly selected open/closed stopping gate. -/
theorem gated_scalar_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g h : E → ℝ) (D : E →L[ℝ] ℝ) (x : E)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hh : HasFDerivAt h D x)
    (hne : f x ≠ g x) :
    HasFDerivAt (fun y => if g y < f y then h y else 0)
      (if g x < f x then D else 0) x := by
  by_cases hs : g x < f x
  · simp only [hs, ite_true]
    apply hh.congr_of_eventuallyEq
    filter_upwards [hg.eventually_lt hf hs] with y hy
    simp [hy]
  · simp only [hs, ite_false]
    have hn : f x < g x := lt_of_le_of_ne (le_of_not_gt hs) hne
    apply (hasFDerivAt_const (0:ℝ) x).congr_of_eventuallyEq
    filter_upwards [hf.eventually_lt hg hn] with y hy
    simp [not_lt_of_ge hy.le]

theorem stopLayer_hasFDerivAt {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n)
    (hx : ∀ j, (preP wp wn x+bp) j ≠ (preN wp wn x+bn) j) :
    HasFDerivAt (stopLayer wp wn bp bn)
      (stopLayerJac wp wn (originalGate wp wn bp bn (x.1-x.2))) x := by
  rw [← layerGate_original]
  have hp : HasFDerivAt (fun y => preP wp wn y+bp) (preP wp wn) x :=
    (preP wp wn).hasFDerivAt.add_const bp
  have hn : HasFDerivAt (fun y => preN wp wn y+bn) (preN wp wn) x :=
    (preN wp wn).hasFDerivAt.add_const bn
  have hpc (j : Fin k) : HasFDerivAt (fun y => (preP wp wn y+bp) j)
      ((ContinuousLinearMap.proj j).comp (preP wp wn)) x := by
    convert (ContinuousLinearMap.proj j).hasFDerivAt.comp x hp using 1
    rfl
  have hnc (j : Fin k) : HasFDerivAt (fun y => (preN wp wn y+bn) j)
      ((ContinuousLinearMap.proj j).comp (preN wp wn)) x := by
    convert (ContinuousLinearMap.proj j).hasFDerivAt.comp x hn using 1
    rfl
  have hcoord (j : Fin k) (H : PairVec n → ℝ) (D : PairVec n →L[ℝ] ℝ)
      (hH : HasFDerivAt H D x) :=
    gated_scalar_derivative (fun y => (preP wp wn y+bp) j) (fun y => (preN wp wn y+bn) j)
      H D x (hpc j).continuousAt (hnc j).continuousAt hH (hx j)
  have hp' : HasFDerivAt (fun y j => if (preN wp wn y+bn) j < (preP wp wn y+bp) j
      then (preP wp wn y+bp) j else 0)
      ((MaskedTrace.activeMap (fun j => decide ((preN wp wn x+bn) j < (preP wp wn x+bp) j))).comp
        (preP wp wn)) x := by
    apply hasFDerivAt_pi'.mpr
    intro j
    rw [gated_projection]
    convert hcoord j _ _ (hpc j) using 1; simp only [decide_eq_true_eq]
  have hn' : HasFDerivAt (fun y j => if (preN wp wn y+bn) j < (preP wp wn y+bp) j
      then (preN wp wn y+bn) j else 0)
      ((MaskedTrace.activeMap (fun j => decide ((preN wp wn x+bn) j < (preP wp wn x+bp) j))).comp
        (preN wp wn)) x := by
    apply hasFDerivAt_pi'.mpr
    intro j
    rw [gated_projection]
    convert hcoord j _ _ (hnc j) using 1; simp only [decide_eq_true_eq]
  exact hp'.prodMk hn'

/-- Source stopping-decomposition derivative, through the actual full MLP. -/
theorem stopping_hasFDerivAt {n m} (net : Network n m) (x : PairVec n)
    (hx : net.Strict (x.1-x.2)) :
    HasFDerivAt (net.decomposeWith stopPair) (stoppingJac (net.originalTrace (x.1-x.2))) x := by
  induction net with
  | output n => exact (ContinuousLinearMap.id ℝ _).hasFDerivAt
  | layer wp wn bp bn tail ih =>
      have hlneq : ∀ j, (preP wp wn x+bp) j ≠ (preN wp wn x+bn) j := by
        intro j he
        apply hx.1 j
        have h := congrFun (preactivation_difference wp wn bp bn x) j
        simp only [Pi.sub_apply] at h
        linarith
      have htstrict : tail.Strict ((stopLayer wp wn bp bn x).1-(stopLayer wp wn bp bn x).2) := by
        rw [stopLayer_difference]
        exact hx.2
      have ht := ih (stopLayer wp wn bp bn x) htstrict
      rw [stopLayer_difference] at ht
      exact ht.comp x (stopLayer_hasFDerivAt wp wn bp bn x hlneq)

/-- The signed two-channel linear map associated with a pair of weight matrices. -/
def pairMap {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) : PairVec n →L[ℝ] PairVec k :=
  (preP wp wn).prod (preN wp wn)

theorem stopLayerJac_pairMap {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (g : Fin k → Bool) :
    stopLayerJac wp wn g = pairMap (gated g wp) (gated g wn) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext <;> funext j
  all_goals
    simp only [stopLayerJac, pairMap, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, MaskedTrace.activeMap_apply, preN, preP_apply]
    cases hg : g j <;> simp [gated, Matrix.mulVec, dotProduct, hg]

theorem pairMap_comp {n k m} (up un : Matrix (Fin m) (Fin k) ℝ)
    (lp ln : Matrix (Fin k) (Fin n) ℝ) :
    (pairMap up un).comp (pairMap lp ln) = pairMap (up*lp+un*ln) (up*ln+un*lp) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext
  · change up.mulVec (lp.mulVec x.1 + ln.mulVec x.2) +
        un.mulVec (ln.mulVec x.1 + lp.mulVec x.2) =
      (up*lp+un*ln).mulVec x.1 + (up*ln+un*lp).mulVec x.2
    simp only [Matrix.mulVec_add, Matrix.add_mulVec, Matrix.mulVec_mulVec]
    abel
  · change un.mulVec (lp.mulVec x.1 + ln.mulVec x.2) +
        up.mulVec (ln.mulVec x.1 + lp.mulVec x.2) =
      (up*ln+un*lp).mulVec x.1 + (up*lp+un*ln).mulVec x.2
    simp only [Matrix.mulVec_add, Matrix.add_mulVec, Matrix.mulVec_mulVec]
    abel

/-- The full stopping-decomposition Jacobian has exactly the occupation parity blocks. -/
theorem stoppingJac_occupation {n m} (tr : MaskedTrace n m) :
    stoppingJac tr = pairMap (occupations tr).1 (occupations tr).2 := by
  induction tr with
  | output n =>
      apply ContinuousLinearMap.ext
      intro x
      apply Prod.ext <;> simp [stoppingJac, occupations, pairMap, preN, preP_apply]
  | layer wp wn g tail ih =>
      simp only [stoppingJac, occupations, ih, stopLayerJac_pairMap, pairMap_comp]

/-- Part 1 of source `ptnb:thm:deriv-occ`: actual positive-head partials
of the stopping decomposition are the signed-state occupation measures. -/
theorem thesis_stopping_decomposition_gradient {n m} (net : Network n m)
    (x : PairVec n) (hx : net.Strict (x.1-x.2))
    (hγ : Thesis.BackwardGames.PositiveFanIn (net.originalTrace (x.1-x.2)))
    (j : Fin m) (i : Fin n) :
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).1 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i false ∧
    (fderiv ℝ (net.decomposeWith stopPair) x (Pi.single i 1,0)).2 j =
      sgOccupation (net.originalTrace (x.1-x.2)) j i true := by
  rw [(stopping_hasFDerivAt net x hx).fderiv, stoppingJac_occupation]
  constructor
  · change ((occupations (net.originalTrace (x.1-x.2))).1 *ᵥ (Pi.single i 1) +
      (occupations (net.originalTrace (x.1-x.2))).2 *ᵥ 0) j = _
    simp only [Matrix.mulVec_zero, add_zero]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, (sg_occupation_kernels _ hγ j i).1]
  · change ((occupations (net.originalTrace (x.1-x.2))).2 *ᵥ (Pi.single i 1) +
      (occupations (net.originalTrace (x.1-x.2))).1 *ᵥ 0) j = _
    simp only [Matrix.mulVec_zero, add_zero]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, (sg_occupation_kernels _ hγ j i).2]

end Thesis.StoppingDecomposition
