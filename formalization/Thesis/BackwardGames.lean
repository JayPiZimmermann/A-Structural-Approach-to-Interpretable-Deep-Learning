import HiddenMonotonicity.MaskedTrace
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Network-linked stopping-game occupations. The objects below use exactly the
varying-width `Network` and its forward-extracted `MaskedTrace`; no Jacobian or
backward-rule equality is assumed as a hypothesis. -/
noncomputable section
namespace Thesis.BackwardGames
open HiddenMonotonicity Matrix Finset

/-- Apply the realized gate to each successor row. -/
def gated {n k : ℕ} (g : Fin k → Bool) (w : Matrix (Fin k) (Fin n) ℝ) :
    Matrix (Fin k) (Fin n) ℝ := fun j i => if g j then w j i else 0

/-- The nonnegative parity kernels of the fixed-gate stopping decomposition. -/
def occupations {n m : ℕ} : MaskedTrace n m →
    Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ
  | .output _ => (1, 0)
  | .layer wp wn g tail =>
      let o := occupations tail
      (o.1 * gated g wp + o.2 * gated g wn,
       o.1 * gated g wn + o.2 * gated g wp)

def signedProduct {n m : ℕ} : MaskedTrace n m → Matrix (Fin m) (Fin n) ℝ
  | .output _ => 1
  | .layer wp wn g tail => signedProduct tail * gated g (wp - wn)

theorem gated_sub {n k} (g : Fin k → Bool) (wp wn : Matrix (Fin k) (Fin n) ℝ) :
    gated g (wp - wn) = gated g wp - gated g wn := by
  ext j i
  simp only [gated, Matrix.sub_apply]
  cases g j <;> simp

theorem occupation_difference {n m} (tr : MaskedTrace n m) :
    (occupations tr).1 - (occupations tr).2 = signedProduct tr := by
  induction tr with
  | output n => simp [occupations, signedProduct]
  | layer wp wn g tail ih =>
      simp only [occupations, signedProduct, gated_sub]
      rw [← ih]
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel

theorem signedMap_matrix {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (g : Fin k → Bool) :
    MaskedTrace.signedMap wp wn g = matrixCLM (gated g (wp-wn)) := by
  ext v j
  simp only [MaskedTrace.signedMap, ContinuousLinearMap.comp_apply, MaskedTrace.activeMap_apply]
  change (if g j then ((wp-wn).mulVec v) j else 0) =
    (gated g (wp-wn)).mulVec v j
  simp only [Matrix.mulVec, dotProduct, gated]
  cases g j <;> simp

/-- The actual trace Jacobian is the signed parity kernel, not a freely assumed matrix. -/
theorem originalJac_occupation {n m} (tr : MaskedTrace n m) :
    tr.originalJac = matrixCLM ((occupations tr).1 - (occupations tr).2) := by
  rw [occupation_difference]
  induction tr with
  | output n =>
      ext v j
      simp [MaskedTrace.originalJac, signedProduct, matrixCLM, Matrix.toLin'_apply']
  | layer wp wn g tail ih =>
      simp only [MaskedTrace.originalJac, signedProduct, signedMap_matrix, ih]
      ext v j
      change (signedProduct tail).mulVec ((gated g (wp-wn)).mulVec v) j =
        ((signedProduct tail) * gated g (wp-wn)).mulVec v j
      rw [Matrix.mulVec_mulVec]

/-- All intermediate neuron and sign choices of a complete ordinary trajectory.
Its input and output states are supplied separately to the path law. -/
def Paths {n m} : MaskedTrace n m → Type
  | .output _ => Unit
  | @MaskedTrace.layer _ k _ _ _ _ tail => Fin k × Bool × Paths tail

instance pathsFintype {n m} : (tr : MaskedTrace n m) → Fintype (Paths tr)
  | .output _ => inferInstanceAs (Fintype Unit)
  | .layer _ _ _ tail => @instFintypeProd _ _ _ (@instFintypeProd _ _ _ (pathsFintype tail))

/-- Product of gated edge weights, sorted by total negative-edge parity. -/
def rawWeight {n m} : (tr : MaskedTrace n m) → Fin m → Fin n → Bool → Paths tr → ℝ
  | .output _, j, i, p, _ => if j = i ∧ p = false then 1 else 0
  | .layer wp wn g tail, j, i, p, path =>
      (if g path.1 then (if path.2.1 then wn path.1 i else wp path.1 i) else 0) *
        rawWeight tail j path.1 (Bool.xor p path.2.1) path.2.2

/-- Explicit finite path integral equals the positive/negative occupation kernels. -/
theorem raw_path_integral {n m} (tr : MaskedTrace n m) (j : Fin m) (i : Fin n) :
    (∑ path : Paths tr, rawWeight tr j i false path) = (occupations tr).1 j i ∧
    (∑ path : Paths tr, rawWeight tr j i true path) = (occupations tr).2 j i := by
  induction tr with
  | output n =>
      constructor
      · change (∑ _ : Unit, if j = i ∧ false = false then (1 : ℝ) else 0) = _
        simp [occupations, Matrix.one_apply]
      · change (∑ _ : Unit, if j = i ∧ true = false then (1 : ℝ) else 0) = _
        simp [occupations]
  | @layer n k m wp wn g tail ih =>
      have ihp (h : Fin k) := (ih j h).1
      have ihn (h : Fin k) := (ih j h).2
      constructor
      all_goals
        change (∑ path : Fin k × Bool × Paths tail,
          (if g path.1 then (if path.2.1 then wn path.1 i else wp path.1 i) else 0) *
            rawWeight tail j path.1 (Bool.xor _ path.2.1) path.2.2) = _
        simp only [Fintype.sum_prod_type, Fintype.sum_bool,
          Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true]
        simp only [ite_true, Bool.false_eq_true, ite_false, ← Finset.mul_sum]
        simp_rw [ihp, ihn]
        simp only [occupations, Matrix.add_apply, Matrix.mul_apply]
        rw [Finset.sum_add_distrib]
        simp only [gated, mul_comm, add_comm]

/-- Total absolute fan-in at a stopping-game state. -/
def fanIn {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) : ℝ :=
  ∑ i, (wp j i + wn j i)

def PositiveFanIn {n m} : MaskedTrace n m → Prop
  | .output _ => True
  | .layer wp wn _ tail => (∀ j, 0 < fanIn wp wn j) ∧ PositiveFanIn tail

def NonnegativeWeights {n m} : MaskedTrace n m → Prop
  | .output _ => True
  | .layer wp wn _ tail => (∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i) ∧ NonnegativeWeights tail

/-- Probability of an ordinary complete trajectory under stop/continue equilibrium.
Stopped trajectories have no ordinary endpoint and consequently contribute zero here. -/
def sgProbability {n m} : (tr : MaskedTrace n m) → Fin m → Fin n → Bool → Paths tr → ℝ
  | .output _, j, i, p, _ => if j = i ∧ p = false then 1 else 0
  | .layer wp wn g tail, j, i, p, path =>
      (if g path.1 then (if path.2.1 then wn path.1 i else wp path.1 i) / fanIn wp wn path.1 else 0) *
        sgProbability tail j path.1 (Bool.xor p path.2.1) path.2.2

/-- The cumulative local fan-in discounts of the same trajectory. -/
def sgDiscount {n m} : (tr : MaskedTrace n m) → Paths tr → ℝ
  | .output _, _ => 1
  | .layer wp wn _ tail, path => fanIn wp wn path.1 * sgDiscount tail path.2.2

theorem sg_path_discount_recovery {n m} (tr : MaskedTrace n m)
    (hγ : PositiveFanIn tr) (j : Fin m) (i : Fin n) (p : Bool) (path : Paths tr) :
    sgDiscount tr path * sgProbability tr j i p path = rawWeight tr j i p path := by
  induction tr generalizing p with
  | output n => simp [sgDiscount, sgProbability, rawWeight]
  | layer wp wn g tail ih =>
      simp only [sgDiscount, sgProbability, rawWeight]
      have ht := ih hγ.2 j path.1 (Bool.xor p path.2.1) path.2.2
      cases hg : g path.1
      · simp
      · simp only [ite_true]
        have he : fanIn wp wn path.1 ≠ 0 := (hγ.1 path.1).ne'
        rw [show fanIn wp wn path.1 * sgDiscount tail path.2.2 *
            ((if path.2.1 then wn path.1 i else wp path.1 i) / fanIn wp wn path.1 *
             sgProbability tail j path.1 (Bool.xor p path.2.1) path.2.2) =
            (if path.2.1 then wn path.1 i else wp path.1 i) *
              (sgDiscount tail path.2.2 * sgProbability tail j path.1 (Bool.xor p path.2.1) path.2.2) by
                field_simp]
        rw [ht]

/-- Discounted occupation at a signed input state, as an explicit finite expectation. -/
def sgOccupation {n m} (tr : MaskedTrace n m) (j : Fin m) (i : Fin n) (p : Bool) : ℝ :=
  ∑ path : Paths tr, sgDiscount tr path * sgProbability tr j i p path

theorem sg_occupation_kernels {n m} (tr : MaskedTrace n m) (hγ : PositiveFanIn tr)
    (j : Fin m) (i : Fin n) :
    sgOccupation tr j i false = (occupations tr).1 j i ∧
    sgOccupation tr j i true = (occupations tr).2 j i := by
  simp only [sgOccupation, sg_path_discount_recovery tr hγ]
  exact raw_path_integral tr j i

/-- Gradient representation for the actual shared MLP: the differential is the
positive occupation minus the negative occupation, on every strict activation cell. -/
theorem stopping_game_gradient {n m} (net : Network n m) (x : Vec n)
    (hx : net.Regular (x,0)) (hγ : PositiveFanIn (net.trace (x,0))) :
    HasFDerivAt net.eval (matrixCLM (fun j i =>
      sgOccupation (net.trace (x,0)) j i false -
      sgOccupation (net.trace (x,0)) j i true)) x := by
  have h := net.hasFDerivAt_eval_trace x hx
  rw [originalJac_occupation] at h
  have he : ((occupations (net.trace (x,0))).1 - (occupations (net.trace (x,0))).2) =
      (fun j i => sgOccupation (net.trace (x,0)) j i false -
        sgOccupation (net.trace (x,0)) j i true) := by
    ext j i
    rw [(sg_occupation_kernels _ hγ j i).1, (sg_occupation_kernels _ hγ j i).2]
    rfl
  rwa [he] at h

theorem sgProbability_nonneg {n m} (tr : MaskedTrace n m)
    (hw : NonnegativeWeights tr) (hγ : PositiveFanIn tr)
    (j : Fin m) (i : Fin n) (p : Bool) (path : Paths tr) :
    0 ≤ sgProbability tr j i p path := by
  induction tr generalizing p with
  | output n => simp only [sgProbability]; split_ifs <;> norm_num
  | layer wp wn g tail ih =>
      simp only [sgProbability]
      apply mul_nonneg _ (ih hw.2 hγ.2 j path.1 (Bool.xor p path.2.1) path.2.2)
      split_ifs
      · exact div_nonneg (hw.1 _ _).2 (hγ.1 _).le
      · exact div_nonneg (hw.1 _ _).1 (hγ.1 _).le
      · exact le_rfl

theorem sgDiscount_pos {n m} (tr : MaskedTrace n m) (hγ : PositiveFanIn tr)
    (path : Paths tr) : 0 < sgDiscount tr path := by
  induction tr with
  | output n => exact zero_lt_one
  | layer wp wn g tail ih => exact mul_pos (hγ.1 path.1) (ih hγ.2 path.2.2)

theorem sgOccupation_nonneg {n m} (tr : MaskedTrace n m)
    (hw : NonnegativeWeights tr) (hγ : PositiveFanIn tr)
    (j : Fin m) (i : Fin n) (p : Bool) : 0 ≤ sgOccupation tr j i p :=
  Finset.sum_nonneg fun path _ => mul_nonneg (sgDiscount_pos tr hγ path).le
    (sgProbability_nonneg tr hw hγ j i p path)

/-- Full one-step equilibrium kernel, including the stopping cemetery. -/
def sgTransition {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (g : Fin k → Bool)
    (j : Fin k) (turn : Bool) : Option (Fin n × Bool) → ℝ
  | none => if g j then 0 else 1
  | some (i,p) => if g j then (if p = turn then wp j i else wn j i) / fanIn wp wn j else 0

theorem sgTransition_normalized {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (g : Fin k → Bool) (hγ : ∀ j, 0 < fanIn wp wn j) (j : Fin k) (turn : Bool) :
    (∑ t, sgTransition wp wn g j turn t) = 1 := by
  cases hg : g j
  · simp [sgTransition, hg, Fintype.sum_option]
  · cases turn <;>
      simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
        sgTransition, hg, ite_true, Bool.true_eq_false, Bool.false_eq_true,
        ite_false, zero_add]
    all_goals
      simp_rw [← add_div]
      rw [← Finset.sum_div]
      simpa [fanIn, add_comm] using div_self (hγ j).ne'

theorem sgTransition_nonneg {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (g : Fin k → Bool) (hw : ∀ j i, 0 ≤ wp j i ∧ 0 ≤ wn j i)
    (hγ : ∀ j, 0 < fanIn wp wn j) (j : Fin k) (turn : Bool)
    (target : Option (Fin n × Bool)) : 0 ≤ sgTransition wp wn g j turn target := by
  cases target with
  | none => simp only [sgTransition]; split_ifs <;> norm_num
  | some t =>
      rcases t with ⟨i,p⟩
      simp only [sgTransition]
      split_ifs
      · exact div_nonneg (hw j i).1 (hγ j).le
      · exact div_nonneg (hw j i).2 (hγ j).le
      · exact le_rfl

/-- Thesis Theorem `ptnb:thm:gradient` / Part 2 of `ptnb:thm:deriv-occ`,
for the shared finite MLP on a strict activation cell. The coordinate differential
is represented by a difference of genuinely nonnegative discounted occupations. -/
theorem thesis_gradient_representation {n m} (net : Network n m) (x : Vec n)
    (hx : net.Regular (x,0)) (hγ : PositiveFanIn (net.trace (x,0)))
    (_hw : NonnegativeWeights (net.trace (x,0)))
    (j : Fin m) (i : Fin n) :
    fderiv ℝ net.eval x (Pi.single i 1) j =
      sgOccupation (net.trace (x,0)) j i false - sgOccupation (net.trace (x,0)) j i true := by
  rw [(stopping_game_gradient net x hx hγ).fderiv]
  change ((fun j i => sgOccupation (net.trace (x,0)) j i false -
    sgOccupation (net.trace (x,0)) j i true) *ᵥ (Pi.single i 1)) j = _
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Coordinate formula exposing all complete signed active paths. -/
theorem originalJac_coordinate_paths {n m} (tr : MaskedTrace n m) (j : Fin m) (i : Fin n) :
    tr.originalJac (Pi.single i 1) j =
      (∑ path : Paths tr, rawWeight tr j i false path) -
      (∑ path : Paths tr, rawWeight tr j i true path) := by
  rw [originalJac_occupation, (raw_path_integral tr j i).1, (raw_path_integral tr j i).2]
  change ((fun j i => (occupations tr).1 j i - (occupations tr).2 j i) *ᵥ (Pi.single i 1)) j = _
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- No active signed path implies exactly zero coordinate differential. -/
theorem originalJac_no_path {n m} (tr : MaskedTrace n m) (j : Fin m) (i : Fin n)
    (hp : ∀ path : Paths tr, rawWeight tr j i false path = 0)
    (hn : ∀ path : Paths tr, rawWeight tr j i true path = 0) :
    tr.originalJac (Pi.single i 1) j = 0 := by
  rw [originalJac_coordinate_paths]
  simp [hp, hn]

end Thesis.BackwardGames
