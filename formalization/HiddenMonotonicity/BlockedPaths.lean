import HiddenMonotonicity.RegionalBlindness

namespace HiddenMonotonicity
open Thesis.BackwardGames

/-- A structural signed path connects the requested input/output through
nonzero edges. Gates are deliberately ignored by this predicate. -/
def PathConnected {n m} : (tr : MaskedTrace n m) → Fin m → Fin n → Paths tr → Prop
  | .output _, j, i, _ => j=i
  | .layer wp wn _ tail, j, i, path =>
      (if path.2.1 then wn path.1 i else wp path.1 i) ≠ 0 ∧
      PathConnected tail j path.1 path.2.2

/-- A path contains at least one inactive neuron. -/
def PathHasInactive {n m} : (tr : MaskedTrace n m) → Paths tr → Prop
  | .output _, _ => False
  | .layer _ _ gate tail, path => gate path.1=false ∨ PathHasInactive tail path.2.2

theorem rawWeight_zero_of_not_connected {n m} (tr : MaskedTrace n m) (j : Fin m)
    (i : Fin n) (p : Bool) (path : Paths tr) (h : ¬PathConnected tr j i path) :
    rawWeight tr j i p path=0 := by
  induction tr generalizing p with
  | output n => simp [PathConnected] at h; simp [rawWeight,h]
  | layer wp wn gate tail ih =>
      simp only [PathConnected, not_and_or] at h
      rcases h with hw | ht
      · simp only [not_not] at hw
        simp only [rawWeight]
        cases gate path.1 <;> simp [hw]
      · simp only [rawWeight, ih j path.1 (Bool.xor p path.2.1) path.2.2 ht, mul_zero]

theorem rawWeight_zero_of_inactive {n m} (tr : MaskedTrace n m) (j : Fin m)
    (i : Fin n) (p : Bool) (path : Paths tr) (h : PathHasInactive tr path) :
    rawWeight tr j i p path=0 := by
  induction tr generalizing p with
  | output n => exact False.elim h
  | layer wp wn gate tail ih =>
      rcases h with hg | ht
      · simp [rawWeight,hg]
      · simp [rawWeight,ih j path.1 (Bool.xor p path.2.1) path.2.2 ht]

/-- Exact structural form of prop:gradient_blindness: every nonzero-edge path
contains an inactive gate, so the coordinate derivative vanishes throughout
an open neighborhood of the original input. -/
theorem Network.gradient_blindness {n m} (net : Network n m) (x : Vec n)
    (hx : net.Strict x) (j : Fin m) (i : Fin n)
    (hblocked : ∀ path : Paths (net.originalTrace x),
      PathConnected (net.originalTrace x) j i path → PathHasInactive (net.originalTrace x) path) :
    ∃ U : Set (Vec n), IsOpen U ∧ x∈U ∧ ∀ y∈U,
      fderiv ℝ net.eval y (Pi.single i 1) j=0 := by
  apply net.regional_gradient_blindness x hx j i
  all_goals
    intro path
    by_cases hc : PathConnected (net.originalTrace x) j i path
    · exact rawWeight_zero_of_inactive _ _ _ _ _ (hblocked path hc)
    · exact rawWeight_zero_of_not_connected _ _ _ _ _ hc

/-- Input-dependent min re-centering preserves reconstruction but invalidates
an unconditional claim of coordinatewise monotonicity of the split streams. -/
theorem recenter_breaks_monotonicity :
    max (2 : ℝ) 0-min (max (2 : ℝ) 0) 0 >
      max (2 : ℝ) 1-min (max (2 : ℝ) 1) 1 := by norm_num

end HiddenMonotonicity
