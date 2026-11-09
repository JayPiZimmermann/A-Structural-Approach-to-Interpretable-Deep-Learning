import HiddenMonotonicity.PolarizedProductDC

/-! Scalar arithmetic and convex monotone composition for nonnegative DC streams. -/
noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity.TransformerDC
open Set

def value (p : ℝ × ℝ) : ℝ := p.1 - p.2

def constPair (c : ℝ) : ℝ × ℝ := (max c 0, max (-c) 0)

def addPair (p q : ℝ × ℝ) : ℝ × ℝ := p + q

def scalePair (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if 0 ≤ c then (c * p.1, c * p.2) else ((-c) * p.2, (-c) * p.1)

def mulPair (p q : ℝ × ℝ) : ℝ × ℝ := productSplit (p, q)

@[simp] theorem value_constPair (c : ℝ) : value (constPair c) = c := by
  by_cases hc : 0 ≤ c
  · simp [value, constPair, max_eq_left hc, max_eq_right (neg_nonpos.mpr hc)]
  · have hc' : c ≤ 0 := le_of_not_ge hc
    simp [value, constPair, max_eq_right hc', max_eq_left (neg_nonneg.mpr hc')]

@[simp] theorem value_addPair (p q : ℝ × ℝ) :
    value (addPair p q) = value p + value q := by
  simp only [value, addPair, Prod.fst_add, Prod.snd_add]
  ring

@[simp] theorem value_scalePair (c : ℝ) (p : ℝ × ℝ) :
    value (scalePair c p) = c * value p := by
  unfold scalePair
  split <;> dsimp [value] <;> ring

@[simp] theorem value_mulPair (p q : ℝ × ℝ) :
    value (mulPair p q) = value p * value q := productSplit_exact (p, q)

@[simp] theorem value_zero : value (0 : ℝ × ℝ) = 0 := by simp [value]

@[simp] theorem value_add (p q : ℝ × ℝ) : value (p + q) = value p + value q :=
  value_addPair p q

theorem value_sum {ι : Type*} (t : Finset ι) (f : ι → ℝ × ℝ) :
    value (∑ i ∈ t, f i) = ∑ i ∈ t, value (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [hi, ih]

section Regular
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Preorder E]
variable {s : Set E}

/-- Each stream is convex and nonnegative on the stated domain; the pair is
coordinatewise nondecreasing there. No property of its signed difference is assumed. -/
structure Regular (s : Set E) (f : E → ℝ × ℝ) : Prop where
  convex_fst : ConvexOn ℝ s (fun x => (f x).1)
  convex_snd : ConvexOn ℝ s (fun x => (f x).2)
  monotone : MonotoneOn f s
  nonnegative : ∀ x ∈ s, 0 ≤ f x

theorem Regular.const (hs : Convex ℝ s) (c : ℝ) :
    Regular s (fun _ : E => constPair c) := by
  refine ⟨convexOn_const _ hs, convexOn_const _ hs, ?_, ?_⟩
  · intro x hx y hy hxy
    exact le_rfl
  · intro x hx
    exact ⟨le_max_right _ _, le_max_right _ _⟩

theorem Regular.zero (hs : Convex ℝ s) : Regular s (fun _ : E => (0 : ℝ × ℝ)) := by
  have hz : constPair 0 = (0 : ℝ × ℝ) := by ext <;> norm_num [constPair]
  simpa only [hz] using Regular.const hs 0

theorem Regular.add {f g : E → ℝ × ℝ} (hf : Regular s f) (hg : Regular s g) :
    Regular s (fun x => addPair (f x) (g x)) := by
  refine ⟨hf.convex_fst.add hg.convex_fst, hf.convex_snd.add hg.convex_snd, ?_, ?_⟩
  · intro x hx y hy hxy
    exact ⟨add_le_add (hf.monotone hx hy hxy).1 (hg.monotone hx hy hxy).1,
      add_le_add (hf.monotone hx hy hxy).2 (hg.monotone hx hy hxy).2⟩
  · intro x hx
    exact ⟨add_nonneg (hf.nonnegative x hx).1 (hg.nonnegative x hx).1,
      add_nonneg (hf.nonnegative x hx).2 (hg.nonnegative x hx).2⟩

theorem Regular.scale {f : E → ℝ × ℝ} (hf : Regular s f) (c : ℝ) :
    Regular s (fun x => scalePair c (f x)) := by
  by_cases hc : 0 ≤ c
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [scalePair, if_pos hc, smul_eq_mul] using hf.convex_fst.smul hc
    · simpa only [scalePair, if_pos hc, smul_eq_mul] using hf.convex_snd.smul hc
    · intro x hx y hy hxy
      simp only [scalePair, if_pos hc]
      exact ⟨mul_le_mul_of_nonneg_left (hf.monotone hx hy hxy).1 hc,
        mul_le_mul_of_nonneg_left (hf.monotone hx hy hxy).2 hc⟩
    · intro x hx
      simp only [scalePair, if_pos hc]
      exact ⟨mul_nonneg hc (hf.nonnegative x hx).1,
        mul_nonneg hc (hf.nonnegative x hx).2⟩
  · have hc' : 0 ≤ -c := neg_nonneg.mpr (le_of_not_ge hc)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [scalePair, if_neg hc, smul_eq_mul] using hf.convex_snd.smul hc'
    · simpa only [scalePair, if_neg hc, smul_eq_mul] using hf.convex_fst.smul hc'
    · intro x hx y hy hxy
      simp only [scalePair, if_neg hc]
      exact ⟨mul_le_mul_of_nonneg_left (hf.monotone hx hy hxy).2 hc',
        mul_le_mul_of_nonneg_left (hf.monotone hx hy hxy).1 hc'⟩
    · intro x hx
      simp only [scalePair, if_neg hc]
      exact ⟨mul_nonneg hc' (hf.nonnegative x hx).2,
        mul_nonneg hc' (hf.nonnegative x hx).1⟩

theorem Regular.mul {f g : E → ℝ × ℝ} (hf : Regular s f) (hg : Regular s g) :
    Regular s (fun x => mulPair (f x) (g x)) := by
  have hc := productSplit_convex_composition s
    (fun x => (f x).1) (fun x => (f x).2) (fun x => (g x).1) (fun x => (g x).2)
    hf.convex_fst hf.convex_snd hg.convex_fst hg.convex_snd
    (fun x hx => (hf.nonnegative x hx).1) (fun x hx => (hf.nonnegative x hx).2)
    (fun x hx => (hg.nonnegative x hx).1) (fun x hx => (hg.nonnegative x hx).2)
  refine ⟨hc.1, hc.2, ?_, ?_⟩
  · intro x hx y hy hxy
    exact productSplit_monotoneOn
      ⟨hf.nonnegative x hx, hg.nonnegative x hx⟩
      ⟨hf.nonnegative y hy, hg.nonnegative y hy⟩
      ⟨hf.monotone hx hy hxy, hg.monotone hx hy hxy⟩
  · intro x hx
    exact productSplit_nonnegative _

theorem Regular.finset_sum {ι : Type*} (t : Finset ι) (f : ι → E → ℝ × ℝ)
    (hs : Convex ℝ s) (hf : ∀ i ∈ t, Regular s (f i)) :
    Regular s (fun x => ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Regular.zero hs
  | @insert i t hi ih =>
      have hreg := (hf i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.sum_insert hi, addPair] using hreg

theorem Regular.scalar_comp {f : E → ℝ × ℝ} (hf : Regular s f)
    (φ : (ℝ × ℝ) → ℝ × ℝ)
    (hc1 : ConvexOn ℝ univ (fun z => (φ z).1))
    (hc2 : ConvexOn ℝ univ (fun z => (φ z).2))
    (hm : Monotone φ) (hn : ∀ z, 0 ≤ z → 0 ≤ φ z) :
    Regular s (fun x => φ (f x)) := by
  have hj (x y : E) (hx : x ∈ s) (hy : y ∈ s)
      (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
      φ (f (a • x + b • y)) ≤ a • φ (f x) + b • φ (f y) := by
    have hinner : f (a • x + b • y) ≤ a • f x + b • f y :=
      ⟨hf.convex_fst.2 hx hy ha hb hab, hf.convex_snd.2 hx hy ha hb hab⟩
    exact (hm hinner).trans
      ⟨hc1.2 (mem_univ _) (mem_univ _) ha hb hab,
       hc2.2 (mem_univ _) (mem_univ _) ha hb hab⟩
  refine ⟨⟨hf.convex_fst.1, ?_⟩, ⟨hf.convex_snd.1, ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    exact (hj x y hx hy a b ha hb hab).1
  · intro x hx y hy a b ha hb hab
    exact (hj x y hx hy a b ha hb hab).2
  · intro x hx y hy hxy
    exact hm (hf.monotone hx hy hxy)
  · intro x hx
    exact hn (f x) (hf.nonnegative x hx)

theorem Regular.vector_comp {ι : Type*}
    (φ : ((ι → ℝ) × (ι → ℝ)) → ℝ × ℝ)
    (hc1 : ConvexOn ℝ univ (fun z => (φ z).1))
    (hc2 : ConvexOn ℝ univ (fun z => (φ z).2))
    (hm : Monotone φ) (hn : ∀ z, 0 ≤ z → 0 ≤ φ z)
    (hs : Convex ℝ s) (f : ι → E → ℝ × ℝ) (hf : ∀ i, Regular s (f i)) :
    Regular s (fun x => φ ((fun i => (f i x).1), (fun i => (f i x).2))) := by
  let v (x : E) : (ι → ℝ) × (ι → ℝ) :=
    ((fun i => (f i x).1), (fun i => (f i x).2))
  have hj (x y : E) (hx : x ∈ s) (hy : y ∈ s)
      (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
      φ (v (a • x + b • y)) ≤ a • φ (v x) + b • φ (v y) := by
    have hinner : v (a • x + b • y) ≤ a • v x + b • v y := by
      constructor
      · intro i
        exact (hf i).convex_fst.2 hx hy ha hb hab
      · intro i
        exact (hf i).convex_snd.2 hx hy ha hb hab
    exact (hm hinner).trans
      ⟨hc1.2 (mem_univ _) (mem_univ _) ha hb hab,
       hc2.2 (mem_univ _) (mem_univ _) ha hb hab⟩
  refine ⟨⟨hs, ?_⟩, ⟨hs, ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    exact (hj x y hx hy a b ha hb hab).1
  · intro x hx y hy a b ha hb hab
    exact (hj x y hx hy a b ha hb hab).2
  · intro x hx y hy hxy
    apply hm
    exact ⟨fun i => ((hf i).monotone hx hy hxy).1,
      fun i => ((hf i).monotone hx hy hxy).2⟩
  · intro x hx
    apply hn
    exact ⟨fun i => ((hf i).nonnegative x hx).1,
      fun i => ((hf i).nonnegative x hx).2⟩

end Regular
end HiddenMonotonicity.TransformerDC
