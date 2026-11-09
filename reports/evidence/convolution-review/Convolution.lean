import HiddenMonotonicity.AffineChunk
import Mathlib.Logic.Equiv.Fin.Basic

/-! Multi-channel finite cross-correlation with an explicit sampling stencil.
A stencil gives the input position used by each output position and kernel tap;
`none` means zero padding. Thus stride, dilation, and spatial shape affect the
index map, while shared kernel coefficients remain explicit. -/
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity.Convolution
open HiddenMonotonicity Matrix Finset

def flat {a b : ℕ} : Fin a × Fin b → Fin (a*b) := finProdFinEquiv
def unflat {a b : ℕ} : Fin (a*b) → Fin a × Fin b := finProdFinEquiv.symm

def sample {ci ip : ℕ} (x : Vec (ci*ip)) (c : Fin ci) : Option (Fin ip) → ℝ
  | none => 0
  | some i => x (flat (c,i))

/-- Direct tensor-indexed cross-correlation, before flattening to a matrix. -/
def applyKernel {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip))
    (x : Vec (ci*ip)) : Vec (co*op) :=
  fun u => ∑ c, ∑ t, K (unflat u).1 c t * sample x c (stencil (unflat u).2 t)

/-- The actual sparse, weight-shared matrix induced by the tensor indices. -/
def kernelMatrix {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip)) :
    Matrix (Fin (co*op)) (Fin (ci*ip)) ℝ :=
  fun u v => ∑ t, if stencil (unflat u).2 t = some (unflat v).2
    then K (unflat u).1 (unflat v).1 t else 0

theorem sampling_sum {ci ip : ℕ} (x : Vec (ci*ip)) (c : Fin ci)
    (s : Option (Fin ip)) (w : ℝ) :
    (∑ i, (if s = some i then w else 0) * x (flat (c,i))) = w * sample x c s := by
  cases s with
  | none => simp [sample]
  | some i => simp [sample]

/-- Exact flattening bridge; no injectivity assumption on the stencil is needed. -/
theorem applyKernel_eq_mulVec {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip)) (x : Vec (ci*ip)) :
    applyKernel K stencil x = (kernelMatrix K stencil).mulVec x := by
  funext u
  change (∑ c, ∑ t, K (unflat u).1 c t * sample x c (stencil (unflat u).2 t)) =
    ∑ v, kernelMatrix K stencil u v * x v
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin ci × Fin ip ≃ Fin (ci*ip))
    (fun v => kernelMatrix K stencil u v * x v), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  simp only [kernelMatrix, unflat, Equiv.symm_apply_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact (sampling_sum x c (stencil (unflat u).2 t) (K (unflat u).1 c t)).symm

theorem applyKernel_hasFDerivAt {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip)) (x : Vec (ci*ip)) :
    HasFDerivAt (applyKernel K stencil) (matrixCLM (kernelMatrix K stencil)) x := by
  have he : applyKernel K stencil = matrixCLM (kernelMatrix K stencil) := by
    funext y
    exact applyKernel_eq_mulVec K stencil y
  rw [he]
  exact (matrixCLM (kernelMatrix K stencil)).hasFDerivAt

theorem kernelMatrix_nonnegative {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip))
    (hK : ∀ o c t, 0 ≤ K o c t) : ∀ u v, 0 ≤ kernelMatrix K stencil u v := by
  intro u v
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · exact hK _ _ _
  · exact le_rfl

def positiveKernel {ci co taps : ℕ} (K : Fin co → Fin ci → Fin taps → ℝ) :=
  fun o c t => max (K o c t) 0

def negativeKernel {ci co taps : ℕ} (K : Fin co → Fin ci → Fin taps → ℝ) :=
  fun o c t => max (-K o c t) 0

theorem kernelMatrix_sign_difference {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip)) :
    kernelMatrix (positiveKernel K) stencil - kernelMatrix (negativeKernel K) stencil =
      kernelMatrix K stencil := by
  ext u v
  simp only [Matrix.sub_apply, kernelMatrix, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs
  · exact (canonical_weight_split _).1
  · ring

/-- The original kernel-level split, with a bias shared over output positions. -/
def splitKernel {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip)) (b : Fin co → ℝ)
    (x : PairVec (ci*ip)) : PairVec (co*op) :=
  (applyKernel (positiveKernel K) stencil x.1 + applyKernel (negativeKernel K) stencil x.2 +
      (fun u => max (b (unflat u).1) 0),
   applyKernel (negativeKernel K) stencil x.1 + applyKernel (positiveKernel K) stencil x.2 +
      (fun u => max (-b (unflat u).1) 0))

theorem splitKernel_eq_affineChunk {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip)) (b : Fin co → ℝ)
    (x : PairVec (ci*ip)) :
    splitKernel K stencil b x =
    affineChunk (kernelMatrix (positiveKernel K) stencil) (kernelMatrix (negativeKernel K) stencil)
      (fun u => max (b (unflat u).1) 0) (fun u => max (-b (unflat u).1) 0) x := by
  simp only [splitKernel, applyKernel_eq_mulVec]
  rfl

/-- All four split-convolution Jacobian blocks are the literal positive and
negative kernel matrices, in the same order as the MLP split. -/
theorem splitKernel_hasFDerivAt {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip)) (b : Fin co → ℝ)
    (x : PairVec (ci*ip)) :
    HasFDerivAt (splitKernel K stencil b)
      ((preP (kernelMatrix (positiveKernel K) stencil) (kernelMatrix (negativeKernel K) stencil)).prod
       (preN (kernelMatrix (positiveKernel K) stencil) (kernelMatrix (negativeKernel K) stencil))) x := by
  have he := funext (splitKernel_eq_affineChunk K stencil b)
  rw [he]
  exact ((preP _ _).hasFDerivAt.add_const _).prodMk ((preN _ _).hasFDerivAt.add_const _)

/-- prop:conv_correct with the actual multi-channel tensor sums and padding. -/
theorem splitKernel_recovery {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip)) (b : Fin co → ℝ)
    (x : PairVec (ci*ip)) :
    (splitKernel K stencil b x).1-(splitKernel K stencil b x).2 =
      applyKernel K stencil (x.1-x.2)+(fun u => b (unflat u).1) := by
  rw [splitKernel_eq_affineChunk, affineChunk_recovery, affineLayer,
    kernelMatrix_sign_difference, applyKernel_eq_mulVec]
  congr 1
  funext u
  exact (canonical_weight_split _).1

theorem splitKernel_properties {ci co ip op taps : ℕ}
    (K : Fin co → Fin ci → Fin taps → ℝ)
    (stencil : Fin op → Fin taps → Option (Fin ip)) (b : Fin co → ℝ) :
    (∀ x, 0 ≤ x → 0 ≤ splitKernel K stencil b x) ∧
    Monotone (splitKernel K stencil b) ∧
    (∀ i, ConvexOn ℝ Set.univ (fun x => (splitKernel K stencil b x).1 i) ∧
      ConvexOn ℝ Set.univ (fun x => (splitKernel K stencil b x).2 i)) ∧
    (∀ x, (splitKernel K stencil b x).1-(splitKernel K stencil b x).2 =
      applyKernel K stencil (x.1-x.2)+(fun u => b (unflat u).1)) := by
  have hw : ∀ u v, 0 ≤ kernelMatrix (positiveKernel K) stencil u v ∧
      0 ≤ kernelMatrix (negativeKernel K) stencil u v := fun u v =>
    ⟨kernelMatrix_nonnegative _ _ (fun _ _ _ => le_max_right _ _) u v,
     kernelMatrix_nonnegative _ _ (fun _ _ _ => le_max_right _ _) u v⟩
  have he := funext (splitKernel_eq_affineChunk K stencil b)
  refine ⟨?_, ?_, ?_, splitKernel_recovery K stencil b⟩
  · intro x hx
    rw [he]
    exact affineChunk_nonnegative _ _ _ _ hw
      ⟨fun _ => le_max_right _ _,fun _ => le_max_right _ _⟩ x hx
  · rw [he]
    exact affineChunk_monotone _ _ _ _ hw
  · intro i
    simp only [he]
    exact affineChunk_convex _ _ _ _ i

end HiddenMonotonicity.Convolution
