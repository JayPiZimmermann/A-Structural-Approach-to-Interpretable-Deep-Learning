import Thesis.GeneralRegularization
import Thesis.SoftplusDecomposition
import Mathlib.Topology.Algebra.Order.Field

/-! The entropy split approaches the strict stopping split away from gate ties.
The zero-score boundary is deliberately excluded: its limiting gate is 1/2. -/
noncomputable section
set_option autoImplicit false
namespace Thesis.SoftplusLimits
open HiddenMonotonicity Thesis.Regularization Filter
open scoped Topology

theorem gate_limit_positive (z : ℝ) (hz : 0 < z) :
    Tendsto (fun θ : ℝ => gate θ z) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun θ : ℝ => z / θ) (𝓝[>] 0) atTop := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_nhdsGT_zero : Tendsto (fun θ : ℝ => θ⁻¹) (𝓝[>] 0) atTop).const_mul_atTop hz
  exact Real.tendsto_sigmoid_atTop.comp h

theorem gate_limit_negative (z : ℝ) (hz : z < 0) :
    Tendsto (fun θ : ℝ => gate θ z) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun θ : ℝ => z / θ) (𝓝[>] 0) atBot := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_nhdsGT_zero : Tendsto (fun θ : ℝ => θ⁻¹) (𝓝[>] 0) atTop).const_mul_atTop_of_neg hz
  exact Real.tendsto_sigmoid_atBot.comp h

/-- Pointwise convergence of both streams, not only their difference. -/
theorem softSplit_tendsto_stopping (u v : ℝ) (hne : u ≠ v) :
    Tendsto (fun θ : ℝ => softSplit θ u v) (𝓝[>] 0)
      (𝓝 (Thesis.StoppingDecomposition.stopPair (u,v))) := by
  have ht : Tendsto (fun θ : ℝ => θ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  rcases lt_or_gt_of_ne hne with h | h
  · have hg := gate_limit_negative (u-v) (sub_neg.mpr h)
    have hH := Real.binEntropy_continuous.continuousAt.tendsto.comp hg
    have he := ht.mul hH
    have hp := (hg.mul_const u).add he
    have hn := hg.mul_const v
    simpa [softSplit, Thesis.StoppingDecomposition.stopPair, not_lt.mpr h.le] using hp.prodMk_nhds hn
  · have hg := gate_limit_positive (u-v) (sub_pos.mpr h)
    have hH := Real.binEntropy_continuous.continuousAt.tendsto.comp hg
    have he := ht.mul hH
    have hp := (hg.mul_const u).add he
    have hn := hg.mul_const v
    simpa [softSplit, Thesis.StoppingDecomposition.stopPair, h] using hp.prodMk_nhds hn

/-- At a tied score the smooth limiting pair is half of each input; the
strict stopping convention is not its limit unless the tied input is zero. -/
theorem softSplit_tendsto_tie (u : ℝ) :
    Tendsto (fun θ : ℝ => softSplit θ u u) (𝓝[>] 0) (𝓝 (u/2,u/2)) := by
  have ht : Tendsto (fun θ : ℝ => θ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have he := ht.mul_const (Real.binEntropy (1/2))
  have hp := (tendsto_const_nhds (x := u/2) (f := 𝓝[>] (0 : ℝ))).add he
  have hn : Tendsto (fun _ : ℝ => (u/2 : ℝ)) (𝓝[>] 0) (𝓝 (u/2)) := tendsto_const_nhds
  convert hp.prodMk_nhds hn using 1 <;>
    simp [softSplit, gate, Real.sigmoid_zero, div_eq_mul_inv, mul_comm]

end Thesis.SoftplusLimits
