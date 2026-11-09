import HiddenMonotonicity.SmoothCurvatureSplit
import HiddenMonotonicity.Decomposition

namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory

noncomputable def splitPair (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (tilt (C1 f) (commonTilt f) z,tilt (C2 f) (commonTilt f) z)

theorem smooth_pair_valid (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b,AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) : ValidPairActivation f (splitPair f) := by
  intro a b
  exact (smooth_dc_split f hf hAC hq).2.2.2.2.2.2 (a,b)

/-- The monotone convex smooth pair maps nonnegative split inputs to
nonnegative outputs whenever the activation's value at zero is nonnegative. -/
theorem smooth_pair_nonnegative (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b,AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) (hzero : 0≤f 0) :
    NonnegativePairActivation (splitPair f) := by
  intro a b ha hb
  have hs := smooth_dc_split f hf hAC hq
  have hg := hs.2.2.2.2.1 (show ((0,0) : ℝ × ℝ)≤(a,b) from ⟨ha,hb⟩)
  have hh := hs.2.2.2.2.2.1 (show ((0,0) : ℝ × ℝ)≤(a,b) from ⟨ha,hb⟩)
  have h0g : tilt (C1 f) (commonTilt f) (0,0)=f 0 := by simp [tilt,C1,primitive]
  have h0h : tilt (C2 f) (commonTilt f) (0,0)=0 := by simp [tilt,C2,primitive]
  change 0≤tilt (C1 f) (commonTilt f) (a,b) ∧ 0≤tilt (C2 f) (commonTilt f) (a,b)
  rw [h0g] at hg
  rw [h0h] at hh
  exact ⟨le_trans hzero hg,hh⟩

/-- The actual same-parameter finite MLP with this smooth activation is
recovered exactly by the curvature-based decomposition at every output. -/
theorem smooth_network_recovery {n m} (net : Network n m)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b,AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) (x : PairVec n) :
    (net.decomposeWith (splitPair f) x).1-(net.decomposeWith (splitPair f) x).2=
      net.forwardWith f (x.1-x.2) :=
  net.valid_decomposition_recovery f (splitPair f) (smooth_pair_valid f hf hAC hq) x

theorem smooth_network_nonnegative {n m} (net : Network n m)
    (hp : net.NonnegativeParameters) (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b,AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) (hzero : 0≤f 0) (x : PairVec n) (hx : 0≤x.1 ∧ 0≤x.2) :
    0≤(net.decomposeWith (splitPair f) x).1 ∧ 0≤(net.decomposeWith (splitPair f) x).2 :=
  net.decomposition_nonnegative hp (splitPair f) (smooth_pair_nonnegative f hf hAC hq hzero) x hx

end HiddenMonotonicity.SmoothDC
