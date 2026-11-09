import HiddenMonotonicity.Core
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace HiddenMonotonicity

/-- Differentiating the common-shift law rigorously gives the sum-of-partials law.
E can be a finite-dimensional activation vector space, not only one scalar. -/
theorem common_shift_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E × E → ℝ) (p q : E) (D : (E × E) →L[ℝ] ℝ) (A : E →L[ℝ] ℝ)
    (hg : HasFDerivAt g D (p,q))
    (hshift : ∀ c, g (p+c,q+c)=g (p,q)+A c) (v : E) :
    D (v,0)+D (0,v) = A v := by
  have hp : HasDerivAt (fun t : ℝ => p+t • v) v 0 := by
    simpa only [Pi.add_apply, zero_add, one_smul, id_eq] using (hasDerivAt_const (0 : ℝ) p).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hq : HasDerivAt (fun t : ℝ => q+t • v) v 0 := by
    simpa only [Pi.add_apply, zero_add, one_smul, id_eq] using (hasDerivAt_const (0 : ℝ) q).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hg' : HasFDerivAt g D (p+(0 : ℝ) • v,q+(0 : ℝ) • v) := by simpa using hg
  have hc := hg'.comp_hasDerivAt 0 (hp.prodMk hq)
  have heq : (fun t : ℝ => g (p+t • v,q+t • v)) = (fun t : ℝ => g (p,q)+t*A v) := by
    funext t
    rw [hshift, map_smul]
    rfl
  change HasDerivAt (fun t : ℝ => g (p+t • v,q+t • v)) (D (v,v)) 0 at hc
  rw [heq] at hc
  have ht : HasDerivAt (fun t : ℝ => g (p,q)+t*A v) (A v) 0 := by
    simpa only [Pi.add_apply, zero_add, one_mul, id_eq] using (hasDerivAt_const (0 : ℝ) (g (p,q))).fun_add
      ((hasDerivAt_id (0 : ℝ)).mul_const (A v))
  have hd := hc.unique ht
  rw [← map_add]
  simpa using hd

/-- The actual symmetric-lift derivative in any activation dimension. -/
theorem vector_lift_chain_rule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E × E → ℝ) (v : E) (D : (E × E) →L[ℝ] ℝ)
    (hg : HasFDerivAt g D ((1/2 : ℝ) • v,(-1/2 : ℝ) • v)) :
    HasDerivAt (fun t : ℝ => g ((t/2) • v,(-t/2) • v))
      ((D (v,0)-D (0,v))/2) 1 := by
  have hp : HasDerivAt (fun t : ℝ => (t/2) • v) ((1/2 : ℝ) • v) 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).div_const 2).smul_const v
  have hn : HasDerivAt (fun t : ℝ => (-t/2) • v) ((-1/2 : ℝ) • v) 1 := by
    convert ((hasDerivAt_id (1 : ℝ)).const_mul (-1/2)).smul_const v using 1
    · funext t
      congr 1
      simp only [id_eq]
      ring
    · simp
  have hc := hg.comp_hasDerivAt 1 (hp.prodMk hn)
  have he : (((1/2 : ℝ) • v, (-1/2 : ℝ) • v) : E × E) =
      (1/2 : ℝ) • (v,0) - (1/2 : ℝ) • (0,v) := by
    apply Prod.ext <;> simp [neg_div, neg_smul]
  rw [he, map_sub, map_smul, map_smul] at hc
  have hd : (D (v,0)-D (0,v))/2 = (1/2 : ℝ) • D (v,0) - (1/2 : ℝ) • D (0,v) := by
    simp only [smul_eq_mul]
    ring
  rw [← hd] at hc
  exact hc

/-- Monotone differentiable functions have nonnegative directional derivatives
in every nonnegative direction, in particular every coordinate direction. -/
theorem monotone_directional_nonnegative {n : ℕ} (g : (Fin n → ℝ) → ℝ)
    (x v : Fin n → ℝ) (D : (Fin n → ℝ) →L[ℝ] ℝ)
    (hg : Monotone g) (hd : HasFDerivAt g D x) (hv : 0 ≤ v) : 0 ≤ D v := by
  have hline : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa only [Pi.add_apply, zero_add, one_smul, id_eq] using
      (hasDerivAt_const (0 : ℝ) x).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hd' : HasFDerivAt g D (x+(0 : ℝ) • v) := by simpa using hd
  have hc := hd'.comp_hasDerivAt 0 hline
  have hm : Monotone (fun t : ℝ => g (x+t • v)) := by
    intro a b hab
    apply hg
    intro i
    exact add_le_add (le_refl (x i)) (mul_le_mul_of_nonneg_right hab (hv i))
  rw [← hc.deriv]
  exact hm.deriv_nonneg

/-- Canonical sign parts recover both a weight and its absolute value. -/
theorem canonical_weight_split (w : ℝ) :
    max w 0 - max (-w) 0 = w ∧ max w 0 + max (-w) 0 = |w| := by
  rcases le_total 0 w with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
    constructor <;> ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]
    constructor <;> ring

end HiddenMonotonicity
