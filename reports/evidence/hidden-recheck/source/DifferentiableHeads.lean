import HiddenMonotonicity.AffineHeads
import HiddenMonotonicity.Convexity
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace HiddenMonotonicity

/-- At a differentiability point, every touching affine lower support has the
actual derivative. This handles tied max branches without strict-gate premises. -/
theorem hasFDerivAt_of_affine_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) (D : E →L[ℝ] ℝ) (hf : DifferentiableAt ℝ f x)
    (hs : ∀ y, f x+D (y-x)≤f y) : HasFDerivAt f D x := by
  have hmin : IsLocalMin (fun y => f y-D (y-x)) x := by
    apply Filter.Eventually.of_forall
    intro y
    have h := hs y
    simpa only [sub_self, map_zero, sub_zero] using (show f x-D (x-x) ≤ f y-D (y-x) by
      simp only [sub_self, map_zero, sub_zero]
      linarith)
  have hd := hf.hasFDerivAt.sub (D.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x))
  have he := hmin.hasFDerivAt_eq_zero hd
  have he' : fderiv ℝ f x = D := by simpa using sub_eq_zero.mp he
  simpa only [he'] using hf.hasFDerivAt

theorem preP_monotone {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (hw : ∀ i j, 0≤wp i j ∧ 0≤wn i j) : Monotone (preP wp wn) := by
  intro x y h
  exact add_le_add (positive_matrix_monotone wp (fun i j => (hw i j).1) h.1)
    (positive_matrix_monotone wn (fun i j => (hw i j).2) h.2)

theorem layerJac_monotone {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x : PairVec n) (hw : ∀ i j, 0≤wp i j ∧ 0≤wn i j) :
    Monotone (layerJac wp wn bp bn x) := by
  intro u v h
  have hp := preP_monotone wp wn hw h
  have hn := preP_monotone wn wp (fun i j => ⟨(hw i j).2,(hw i j).1⟩) h
  constructor
  · intro i
    simp only [layerJac, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    split_ifs <;> first | exact hp i | exact hn i
  · exact hn

/-- Selecting either winning branch at a tie gives a global affine lower support. -/
theorem layerFun_affine_support {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (bp bn : Vec k) (x y : PairVec n) :
    layerFun wp wn bp bn x + layerJac wp wn bp bn x (y-x) ≤ layerFun wp wn bp bn y := by
  constructor
  · intro i
    simp only [layerFun, layerJac, Prod.fst_add, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Pi.add_apply]
    split_ifs with h
    · rw [max_eq_left (le_of_lt h), map_sub]
      change preP wp wn x i+bp i+(preP wp wn y i-preP wp wn x i) ≤
        max (preP wp wn y i+bp i) (preN wp wn y i+bn i)
      linarith only [le_max_left (preP wp wn y i+bp i) (preN wp wn y i+bn i)]
    · rw [max_eq_right (le_of_not_gt h), map_sub]
      change preN wp wn x i+bn i+(preN wp wn y i-preN wp wn x i) ≤
        max (preP wp wn y i+bp i) (preN wp wn y i+bn i)
      linarith only [le_max_right (preP wp wn y i+bp i) (preN wp wn y i+bn i)]
  · intro i
    change (preN wp wn x+bn) i+preN wp wn (y-x) i ≤ (preN wp wn y+bn) i
    rw [map_sub]
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith

theorem Network.jacobian_monotone {n m} (net : Network n m) (hw : net.Nonnegative)
    (x : PairVec n) : Monotone (net.jacobian x) := by
  induction net with
  | output n => exact monotone_id
  | layer wp wn bp bn tail ih =>
      exact (ih hw.2.2 _).comp (layerJac_monotone wp wn bp bn x (fun i j => ⟨hw.1 i j,hw.2.1 i j⟩))

/-- Both split streams have the selected trace as a global supporting affine map,
including degenerate neurons whose preactivation vanishes identically. -/
theorem Network.split_affine_support {n m} (net : Network n m) (hw : net.Nonnegative)
    (x y : PairVec n) :
    net.split x.1 x.2 + net.jacobian x (y-x) ≤ net.split y.1 y.2 := by
  induction net with
  | output n => change x+(y-x)≤y; simp
  | layer wp wn bp bn tail ih =>
      let lx := layerFun wp wn bp bn x
      let ly := layerFun wp wn bp bn y
      have hl : layerJac wp wn bp bn x (y-x) ≤ ly-lx := by
        have hl := layerFun_affine_support wp wn bp bn x y
        constructor
        · intro i
          have h := hl.1 i
          change lx.1 i+(layerJac wp wn bp bn x (y-x)).1 i ≤ ly.1 i at h
          change _ ≤ ly.1 i-lx.1 i
          linarith
        · intro i
          have h := hl.2 i
          change lx.2 i+(layerJac wp wn bp bn x (y-x)).2 i ≤ ly.2 i at h
          change _ ≤ ly.2 i-lx.2 i
          linarith
      have hm := tail.jacobian_monotone hw.2.2 lx hl
      change tail.split lx.1 lx.2 + tail.jacobian lx (layerJac wp wn bp bn x (y-x)) ≤
        tail.split ly.1 ly.2
      have ht := ih hw.2.2 lx ly
      exact ⟨le_trans (add_le_add (le_refl _) hm.1) ht.1,
        le_trans (add_le_add (le_refl _) hm.2) ht.2⟩

/-- The exact supporting row computed by the ungated affine-head pass. -/
theorem Network.affine_head_support {n m} (net : Network n m)
    (hw : net.Nonnegative) (x y : PairVec n) (rp rn : Row m)
    (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ) (head : Bool) :
    (if head then (net.affineHeads rp rn bp bn x).1 else (net.affineHeads rp rn bp bn x).2) +
      assemble ((net.originalTrace (x.1-x.2)).run (fun _ => 0)
        (affineReadoutSeed rp rn 0 head)) (y-x) ≤
      (if head then (net.affineHeads rp rn bp bn y).1 else (net.affineHeads rp rn bp bn y).2) := by
  have hs := net.split_affine_support hw x y
  rw [MaskedTrace.run_zero_actual, ← net.trace_originalTrace, ← net.jacobian_trace]
  cases head
  · have h := add_le_add (hn hs.1) (hp hs.2)
    simpa [affineHeads, affineReadoutSeed, shiftPair, assemble, map_add, add_assoc,
      add_left_comm, add_comm] using add_le_add_right h bn
  · have h := add_le_add (hp hs.1) (hn hs.2)
    simpa [affineHeads, affineReadoutSeed, shiftPair, assemble, map_add, add_assoc,
      add_left_comm, add_comm] using add_le_add_right h bp


/-- An actual affine head derivative at every point where that head is
Fréchet differentiable; internal gates may tie, even on whole open sets. -/
theorem Network.affine_head_derivative_of_differentiable {n m} (net : Network n m)
    (hw : net.Nonnegative) (x : PairVec n) (rp rn : Row m)
    (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ) (head : Bool)
    (hd : DifferentiableAt ℝ (fun y => if head then (net.affineHeads rp rn bp bn y).1
      else (net.affineHeads rp rn bp bn y).2) x) :
    HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn y).1
      else (net.affineHeads rp rn bp bn y).2)
      (assemble ((net.originalTrace (x.1-x.2)).run (fun _ => 0)
        (affineReadoutSeed rp rn 0 head))) x :=
  hasFDerivAt_of_affine_support _ _ _ hd
    (fun y => net.affine_head_support hw x y rp rn hp hn bp bn head)

/-- The source's symmetric input gradient at every differentiability point of
that lifted head, even when the full pair-input function is not differentiable. -/
theorem Network.affine_symmetric_derivative_of_differentiable {n m} (net : Network n m)
    (hw : net.Nonnegative) (x : Vec n) (rp rn : Row m)
    (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ) (head : Bool)
    (hd : DifferentiableAt ℝ (fun y => if head then
      (net.affineHeads rp rn bp bn (balancedLift n y)).1
      else (net.affineHeads rp rn bp bn (balancedLift n y)).2) x) :
    HasFDerivAt (fun y => if head then (net.affineHeads rp rn bp bn (balancedLift n y)).1
      else (net.affineHeads rp rn bp bn (balancedLift n y)).2)
      (unified ((net.originalTrace x).run (fun _ => 0)
        (affineReadoutSeed rp rn 0 head))) x := by
  apply hasFDerivAt_of_affine_support _ _ _ hd
  intro y
  have hs := net.affine_head_support hw (balancedLift n x) (balancedLift n y)
    rp rn hp hn bp bn head
  rw [balancedLift_difference, ← map_sub] at hs
  change _ + ((assemble _).comp (balancedLift n)) (y-x) ≤ _ at hs
  rw [assemble_balancedLift] at hs
  exact hs

theorem coefficientRow_monotone {m} (w : Vec m) (hw : 0≤w) :
    Monotone (coefficientRow w) := by
  intro x y h
  simp only [coefficientRow_apply]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i))

theorem Network.canonical_nonnegative {n m} (net : Network n m) (hc : net.Canonical) :
    net.Nonnegative := by
  induction net with
  | output n => trivial
  | layer wp wn bp bn tail ih =>
      refine ⟨?_, ?_, ih hc.2⟩
      · intro i j
        rw [(hc.1 i j).1]
        exact le_max_right _ _
      · intro i j
        rw [(hc.1 i j).2]
        exact le_max_right _ _

theorem MaskedTrace.affine_unified_invariant {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (rp rn : Row m) (β : ℝ) :
    unified (tr.run α (affineReadoutSeed rp rn β true)) -
      unified (tr.run α (affineReadoutSeed rp rn β false)) = (rp-rn).comp tr.originalJac := by
  have hi := tr.affine_partial_invariants α rp rn β
  ext v
  have hp := congrArg (fun R : Row n => R v) hi.1
  have hn := congrArg (fun R : Row n => R v) hi.2
  simp only [unified, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, smul_eq_mul] at hp hn ⊢
  linarith

/-- Both differentiable affine heads reconstruct the actual logit derivative
and both shifted partial invariants at tied as well as strict internal gates. -/
theorem Network.affine_backward_invariants_of_differentiable {n m} (net : Network n m)
    (hw : net.Nonnegative) (x : Vec n) (rp rn : Row m)
    (hp : Monotone rp) (hn : Monotone rn) (bp bn : ℝ)
    (hg : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).1) x)
    (hh : DifferentiableAt ℝ (fun y => (net.affineHeads rp rn bp bn (balancedLift n y)).2) x)
    (α : ℕ → ℝ) (β : ℝ) :
    HasFDerivAt (net.affineLogit rp rn bp bn) ((rp-rn).comp (net.originalTrace x).originalJac) x ∧
    ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).1-
      ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).1 =
      (rp-rn).comp (net.originalTrace x).originalJac ∧
    ((net.originalTrace x).run α (affineReadoutSeed rp rn β true)).2-
      ((net.originalTrace x).run α (affineReadoutSeed rp rn β false)).2 =
      -((rp-rn).comp (net.originalTrace x).originalJac) := by
  refine ⟨?_, (net.originalTrace x).affine_partial_invariants α rp rn β⟩
  have dg := net.affine_symmetric_derivative_of_differentiable hw x rp rn hp hn bp bn true hg
  have dh := net.affine_symmetric_derivative_of_differentiable hw x rp rn hp hn bp bn false hh
  have hd := dg.fun_sub dh
  simp only [ite_true, Bool.false_eq_true, ite_false] at hd
  rw [MaskedTrace.affine_unified_invariant] at hd
  simpa only [Network.affine_heads_recovery, balancedLift_difference] using hd

end HiddenMonotonicity
