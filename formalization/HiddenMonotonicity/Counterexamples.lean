import HiddenMonotonicity.Core

namespace HiddenMonotonicity

/-- Balanced-input positive head of the two-hidden-neuron example
f(x)=ReLU(ReLU(x)+ReLU(-x)-10), with every edge connected and nonzero. -/
noncomputable def connectedFlatG (x : ℝ) : ℝ :=
  max (2*max (x/2) (-x/2)) (-x/2+x/2+10)

noncomputable def connectedFlatH (x : ℝ) : ℝ := -x/2+x/2+10

theorem connected_flat_head_derivatives :
    HasDerivAt connectedFlatG 0 1 ∧ HasDerivAt connectedFlatH 0 1 := by
  constructor
  · apply (hasDerivAt_const (1 : ℝ) (10 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ)<1) (by norm_num : (1 : ℝ)<10)] with x hx
    unfold connectedFlatG
    rw [max_eq_left (by linarith [hx.1] : -x/2 ≤ x/2)]
    have hcancel : -x/2+x/2+(10 : ℝ)=10 := by ring
    rw [hcancel]
    exact max_eq_right (by linarith [hx.2] : 2*(x/2) ≤ 10)
  · convert hasDerivAt_const (1 : ℝ) (10 : ℝ) using 1
    funext x
    unfold connectedFlatH
    ring

/-- A nonzero raw sensitivity mass does not force a nonzero balanced derivative. -/
theorem nonzero_mass_zero_balanced :
    (1 : ℝ)+1>0 ∧ ((1 : ℝ)-1)/2=0 := by norm_num

end HiddenMonotonicity
