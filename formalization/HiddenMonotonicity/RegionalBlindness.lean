import HiddenMonotonicity.OriginalTrace
import Thesis.BackwardGames

namespace HiddenMonotonicity
open Filter Set
open scoped Topology

/-- Affine preactivations and the complete ReLU layer are continuous. -/
theorem reluLayer_continuous {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) :
    Continuous (reluLayer wp wn bp bn) := by
  apply continuous_pi
  intro i
  exact (((continuous_apply i).comp ((matrixCLM (wp-wn)).continuous.add continuous_const)).max
    continuous_const)

/-- Strict activation cells are neighborhoods and the actual complete forward
trace is constant there. The conclusion includes strictness at every point. -/
theorem Network.eventually_strict_trace {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) :
    ∀ᶠ y in 𝓝 x, net.Strict y ∧ net.originalTrace y=net.originalTrace x := by
  induction net with
  | output n => exact Filter.Eventually.of_forall (fun _ => ⟨trivial,rfl⟩)
  | layer wp wn bp bn tail ih =>
      have hsign : ∀ i, ∀ᶠ y in 𝓝 x,
          (0 < affineLayer wp wn bp bn y i ↔ 0 < affineLayer wp wn bp bn x i) ∧
          affineLayer wp wn bp bn y i ≠ 0 := by
        intro i
        have hc : ContinuousAt (fun y => affineLayer wp wn bp bn y i) x :=
          ((continuous_apply i).comp ((matrixCLM (wp-wn)).continuous.add continuous_const)).continuousAt
        by_cases hp : 0 < affineLayer wp wn bp bn x i
        · have he := continuousAt_const.eventually_lt hc hp
          filter_upwards [he] with y hy
          exact ⟨iff_of_true hy hp, ne_of_gt hy⟩
        · have hn : affineLayer wp wn bp bn x i < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hx.1 i)
          have he := hc.eventually_lt continuousAt_const hn
          filter_upwards [he] with y hy
          exact ⟨iff_of_false (not_lt_of_ge (le_of_lt hy)) hp, ne_of_lt hy⟩
      have htail := (reluLayer_continuous wp wn bp bn).continuousAt.tendsto.eventually
        (ih (reluLayer wp wn bp bn x) hx.2)
      filter_upwards [Filter.eventually_all.mpr hsign, htail] with y hy hty
      constructor
      · exact ⟨fun i => (hy i).2,hty.1⟩
      · simp only [Network.originalTrace, hty.2]
        congr 1
        funext i
        by_cases hp : 0 < affineLayer wp wn bp bn x i
        · have hyp := (hy i).1.mpr hp
          simp [originalGate,hp,hyp]
        · have hyp : ¬0 < affineLayer wp wn bp bn y i := fun h => hp ((hy i).1.mp h)
          simp [originalGate,hp,hyp]

/-- A genuine open neighborhood on which the whole MLP Jacobian is fixed. -/
theorem Network.locally_constant_jacobian {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) :
    ∃ U : Set (Vec n), IsOpen U ∧ x∈U ∧ ∀ y∈U,
      HasFDerivAt net.eval (net.originalTrace x).originalJac y := by
  rcases mem_nhds_iff.mp (net.eventually_strict_trace x hx) with ⟨U,hU,hopen,hxU⟩
  refine ⟨U,hopen,hxU,?_⟩
  intro y hy
  have hs := hU hy
  have hd := net.hasFDerivAt_originalTrace y hs.1
  rw [hs.2] at hd
  exact hd

/-- Thesis prop:gradient_blindness, with the path obstruction stated exactly
as vanishing of every signed active path. It proves zero on an open region,
not just zero at the inspected input. -/
theorem Network.regional_gradient_blindness {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (j : Fin m) (i : Fin n)
    (hp : ∀ path : Thesis.BackwardGames.Paths (net.originalTrace x),
      Thesis.BackwardGames.rawWeight (net.originalTrace x) j i false path=0)
    (hn : ∀ path : Thesis.BackwardGames.Paths (net.originalTrace x),
      Thesis.BackwardGames.rawWeight (net.originalTrace x) j i true path=0) :
    ∃ U : Set (Vec n), IsOpen U ∧ x∈U ∧ ∀ y∈U,
      fderiv ℝ net.eval y (Pi.single i 1) j=0 := by
  rcases net.locally_constant_jacobian x hx with ⟨U,hopen,hxU,hU⟩
  refine ⟨U,hopen,hxU,?_⟩
  intro y hy
  rw [(hU y hy).fderiv]
  exact Thesis.BackwardGames.originalJac_no_path _ j i hp hn

end HiddenMonotonicity
