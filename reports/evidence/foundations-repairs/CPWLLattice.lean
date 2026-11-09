import Thesis.ConvexCPWL
import Mathlib.Topology.Order.IntermediateValue

/-! Genuine finite lattice representation of continuous finite affine selections. -/
noncomputable section
namespace Thesis.PiecewiseLinear
open Set Filter Matrix Finset Thesis.Tropical
open scoped Topology

/-- A finite continuous selection locally uses only branches active at the
reference point. This is a finite closed-cover fact, with no representation assumed. -/
theorem continuous_finite_selection_local {A X : Type} [Fintype A] [TopologicalSpace X]
    (f : X → ℝ) (g : A → X → ℝ) (hf : Continuous f) (hg : ∀ i, Continuous (g i))
    (hsel : ∀ x, ∃ i, f x=g i x) (x : X) :
    ∀ᶠ y in 𝓝 x, ∃ i, f y=g i y ∧ f x=g i x := by
  have he : ∀ᶠ y in 𝓝 x, ∀ i, f x≠g i x → f y≠g i y := by
    rw [eventually_all]
    intro i
    by_cases h : f x=g i x
    · exact Eventually.of_forall (fun _ hn => (hn h).elim)
    · have hh := ((hf.sub (hg i)).continuousAt).eventually_ne (sub_ne_zero.mpr h)
      filter_upwards [hh] with y hy hn
      exact sub_ne_zero.mp hy
  filter_upwards [he] with y hy
  obtain ⟨i,hi⟩ := hsel y
  exact ⟨i,hi,by by_contra hn; exact hy i hn hi⟩

/-- Endpoint separation for a continuous selection of finitely many affine
lines. One selected affine branch lies above the initial and below the final value. -/
theorem affine_selection_separation {A : Type} [Fintype A]
    (f : ℝ → ℝ) (a b : A → ℝ) (hf : Continuous f)
    (hsel : ∀ t, ∃ i, f t=(1-t)*a i+t*b i) :
    ∃ i, f 0≤a i ∧ b i≤f 1 := by
  classical
  by_contra hsep
  push Not at hsep
  let S : Finset A := univ.filter (fun i => f 0≤a i)
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := hsel 0
    refine ⟨i,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    simpa using hi.le
  let v := (S.inf' hS b+f 1)/2
  have hv : f 1<v := by
    have hm : f 1<S.inf' hS b := (lt_inf'_iff hS).mpr (fun i hi => hsep i (mem_filter.mp hi).2)
    dsimp [v]
    linarith
  have hbi (i : A) (hi : f 0≤a i) : v<b i := by
    have hm : S.inf' hS b≤b i := inf'_le b (mem_filter.mpr ⟨mem_univ _,hi⟩)
    dsimp [v] at hv ⊢
    linarith
  let g := fun t => f t-((1-t)*f 0+t*v)
  have hg : Continuous g := hf.sub (by fun_prop)
  have hline : ∀ i, Continuous (fun t : ℝ => (1-t)*a i+t*b i) := fun _ => by fun_prop
  have hloc := continuous_finite_selection_local f _ hf hline hsel 0
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0<t ∧ t<1 ∧ 0<g t := by
    have hloc' := hloc.filter_mono (nhdsWithin_le_nhds (s:=Ioi (0 : ℝ)))
    have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0<t := self_mem_nhdsWithin
    have ht' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t<1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hloc',ht,ht'] with t ⟨i,hi,hi0⟩ ht ht'
    refine ⟨ht,ht',?_⟩
    have hai : f 0=a i := by simpa using hi0
    have hbi' := hbi i hai.le
    dsimp [g]
    rw [hi,hai]
    nlinarith [mul_pos ht (sub_pos.mpr hbi')]
  obtain ⟨s,hs0,hs1,hgs⟩ := hnear.exists
  have hg1 : g 1<0 := by simpa [g] using sub_neg.mpr hv
  let Z : Set ℝ := Icc s 1 ∩ {t | g t=0}
  have hZ : IsCompact Z := isCompact_Icc.inter_right (isClosed_eq hg continuous_const)
  have hnZ : Z.Nonempty := by
    obtain ⟨z,hz,hzg⟩ := intermediate_value_Icc' hs1.le hg.continuousOn ⟨hg1.le,hgs.le⟩
    exact ⟨z,hz,hzg⟩
  obtain ⟨r,hr,hmax⟩ := hZ.exists_isGreatest hnZ
  have hr0 : 0<r := lt_of_lt_of_le hs0 hr.1.1
  have hr1 : r<1 := lt_of_le_of_ne hr.1.2 (by intro he; subst r; exact hg1.ne hr.2)
  have hlocR := continuous_finite_selection_local f _ hf hline hsel r
  have hright : ∀ᶠ t in 𝓝[>] r, r<t ∧ t<1 ∧ 0<g t := by
    have ht : ∀ᶠ t in 𝓝[>] r, r<t := self_mem_nhdsWithin
    have ht' : ∀ᶠ t in 𝓝[>] r, t<1 := (eventually_lt_nhds hr1).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlocR.filter_mono nhdsWithin_le_nhds,ht,ht'] with t ⟨i,hi,hir⟩ ht ht'
    refine ⟨ht,ht',?_⟩
    have hroot : (1-r)*a i+r*b i=(1-r)*f 0+r*v := by
      have hh := hr.2
      dsimp [g] at hh
      rw [hir] at hh
      linarith
    have hai : a i<f 0 := by
      by_contra hn
      have hb := hbi i (le_of_not_gt hn)
      have hp := mul_pos hr0 (sub_pos.mpr hb)
      have hp' := mul_nonneg (sub_nonneg.mpr hr1.le) (sub_nonneg.mpr (le_of_not_gt hn))
      nlinarith
    have hdelta : 0<(b i-v)-(a i-f 0) := by
      nlinarith
    dsimp [g]
    rw [hi]
    nlinarith [mul_pos (sub_pos.mpr ht) hdelta]
  obtain ⟨t,hrt,ht1,hgt⟩ := hright.exists
  obtain ⟨z,hzt,hzg⟩ := intermediate_value_Icc' ht1.le hg.continuousOn ⟨hg1.le,hgt.le⟩
  have hzr := hmax ⟨⟨hr.1.1.trans (hrt.le.trans hzt.1),hzt.2⟩,hzg⟩
  have := hzt.1
  linarith



variable {I : Type} [Fintype I]

/-- A finite maximum of finite affine minima, stored as negative max-affine
blocks. The representation theorem below constructs this from an actual CPWL cover. -/
structure MaxMinPolynomial (I : Type) where
  Blocks : Type
  finite : Fintype Blocks
  inhabited : Nonempty Blocks
  negativeTerms : Blocks → Polynomial I
attribute [instance] MaxMinPolynomial.finite MaxMinPolynomial.inhabited

def MaxMinPolynomial.eval (p : MaxMinPolynomial I) (x : I → ℝ) : ℝ :=
  finiteMax (fun a => -(p.negativeTerms a).eval x)

/-- The separation lemma on an actual segment in the input vector space. -/
theorem affine_cover_separation (f : (I → ℝ) → ℝ) (hf : Continuous f)
    (C : AffineCover (fun x (_ : Unit) => f x)) (x y : I → ℝ) :
    ∃ a, f x≤C.slope a () ⬝ᵥ x+C.bias a () ∧
      C.slope a () ⬝ᵥ y+C.bias a ()≤f y := by
  let path := fun t : ℝ => (1-t) • x+t • y
  have hp : Continuous path := by dsimp [path]; fun_prop
  have hsel : ∀ t, ∃ a, f (path t)=(1-t)*(C.slope a () ⬝ᵥ x+C.bias a ())+t*(C.slope a () ⬝ᵥ y+C.bias a ()) := by
    intro t
    obtain ⟨a,ha⟩ := C.covers (path t)
    refine ⟨a,?_⟩
    rw [C.affine_on a (path t) ha ()]
    dsimp [path]
    simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]
    ring
  obtain ⟨a,ha,hb⟩ := affine_selection_separation (f ∘ path)
    (fun a => C.slope a () ⬝ᵥ x+C.bias a ())
    (fun a => C.slope a () ⬝ᵥ y+C.bias a ()) (hf.comp hp) hsel
  exact ⟨a,by simpa [path] using ha,by simpa [path] using hb⟩

/-- Every continuous function with an actual finite affine cover admits a finite
max–min representation. The index blocks are precisely upper-piece sets occurring
at input points; their global lower-bound property is proved by segment separation. -/
theorem cpwl_lattice_representation (f : (I → ℝ) → ℝ)
    (hf : CPWL (fun x (_ : Unit) => f x)) :
    ∃ p : MaxMinPolynomial I, ∀ x, f x=p.eval x := by
  classical
  obtain ⟨hcont,⟨C⟩⟩ := hf
  have hc : Continuous f := continuous_apply () |>.comp hcont
  let upper := fun x : I → ℝ => univ.filter (fun a : C.Pieces => f x≤C.slope a () ⬝ᵥ x+C.bias a ())
  have hu (x : I → ℝ) : (upper x).Nonempty := by
    obtain ⟨a,ha⟩ := C.covers x
    refine ⟨a,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    exact (C.affine_on a x ha ()).le
  let T := {S : Finset C.Pieces // ∃ x, S=upper x}
  let : Nonempty T := ⟨⟨upper 0,⟨0,rfl⟩⟩⟩
  have hS (S : T) : S.val.Nonempty := by obtain ⟨x,hx⟩ := S.property; rw [hx]; exact hu x
  let q : T → Polynomial I := fun S =>
    { Terms := S.val
      finite := inferInstance
      inhabited := (hS S).to_subtype
      slope := fun a => -(C.slope a.val ())
      intercept := fun a => -(C.bias a.val ()) }
  let p : MaxMinPolynomial I := ⟨T,inferInstance,inferInstance,q⟩
  refine ⟨p,?_⟩
  intro y
  apply le_antisymm
  · let S : T := ⟨upper y,⟨y,rfl⟩⟩
    have hh : (q S).eval y≤-f y := by
      let : Nonempty S.val := (hS S).to_subtype
      apply finiteMax_le
      intro a
      have ha := (mem_filter.mp a.property).2
      change (-C.slope a.val ()) ⬝ᵥ y+-C.bias a.val ()≤-f y
      rw [neg_dotProduct]
      linarith
    have hm := le_finiteMax (fun S : T => -(q S).eval y) S
    change _ ≤ p.eval y at hm
    linarith
  · apply finiteMax_le
    intro S
    let : Nonempty S.val := (hS S).to_subtype
    obtain ⟨x,hx⟩ := S.property
    obtain ⟨a,ha,hb⟩ := affine_cover_separation f hc C x y
    have ham : a ∈ S.val := by rw [hx]; exact mem_filter.mpr ⟨mem_univ _,ha⟩
    have hm := le_finiteMax (fun a : S.val => (q S).slope a ⬝ᵥ y+(q S).intercept a) ⟨a,ham⟩
    change (-C.slope a ()) ⬝ᵥ y+-C.bias a ()≤(q S).eval y at hm
    rw [neg_dotProduct] at hm
    change -(q S).eval y≤f y
    linarith

/-- Finite maximum closure of genuine differences of finite max-affine polynomials. -/
theorem polynomial_difference_finset_sup {A : Type} [DecidableEq A]
    (v : A → (I → ℝ) → ℝ) (s : Finset A)
    (hrep : ∀ a ∈ s, ∃ g h : Polynomial I, ∀ x, v a x=g.eval x-h.eval x)
    (hs : s.Nonempty) :
    ∃ g h : Polynomial I, ∀ x, s.sup' hs (fun a => v a x)=g.eval x-h.eval x := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    obtain ⟨ga,ha',hea⟩ := hrep a (mem_insert_self _ _)
    by_cases hn : s.Nonempty
    · obtain ⟨gs,hs',hes⟩ := ih (fun b hb => hrep b (mem_insert_of_mem hb)) hn
      refine ⟨(ga.add hs').max (gs.add ha'),ha'.add hs',?_⟩
      intro x
      rw [sup'_insert hn,hea,hes,Thesis.Tropical.Polynomial.eval_max,Thesis.Tropical.Polynomial.eval_add,
        Thesis.Tropical.Polynomial.eval_add,Thesis.Tropical.Polynomial.eval_add]
      change max (ga.eval x-ha'.eval x) (gs.eval x-hs'.eval x)=_
      rw [← max_sub_sub_right]
      congr 1 <;> ring
    · have he : s=∅ := not_nonempty_iff_eq_empty.mp hn
      subst s
      refine ⟨ga,ha',?_⟩
      intro x
      simpa using hea x

/-- Constructive nonconvex CPWL-to-DC bridge, with no convexity or DC
representation hypothesis on the input function. -/
theorem cpwl_polynomial_difference (f : (I → ℝ) → ℝ)
    (hf : CPWL (fun x (_ : Unit) => f x)) :
    ∃ g h : Polynomial I, ∀ x, f x=g.eval x-h.eval x := by
  classical
  obtain ⟨p,hp⟩ := cpwl_lattice_representation f hf
  have hrep : ∀ a ∈ (univ : Finset p.Blocks), ∃ g h : Polynomial I,
      ∀ x, -(p.negativeTerms a).eval x=g.eval x-h.eval x := by
    intro a _
    refine ⟨Thesis.Tropical.Polynomial.monomial 0 0,p.negativeTerms a,?_⟩
    intro x
    simp [Thesis.Tropical.Polynomial.eval_monomial]
  obtain ⟨g,h,he⟩ := polynomial_difference_finset_sup
    (fun a x => -(p.negativeTerms a).eval x) univ hrep univ_nonempty
  exact ⟨g,h,fun x => (hp x).trans (he x)⟩



/-- Exact DC characterization of the independent continuous finite-polyhedral
CPWL definition, including the nonconvex direction. -/
theorem cpwl_iff_polynomial_difference (f : (I → ℝ) → ℝ) :
    CPWL (fun x (_ : Unit) => f x) ↔
      ∃ g h : Polynomial I, ∀ x, f x=g.eval x-h.eval x := by
  constructor
  · exact cpwl_polynomial_difference f
  · rintro ⟨g,h,he⟩
    have hrep : (fun x (_ : Unit) => f x)=(fun x (_ : Unit) => g.eval x-h.eval x) :=
      funext (fun x => funext (fun _ => he x))
    rw [hrep]
    exact polynomial_difference_cpwl (fun _ => g) (fun _ => h)

end Thesis.PiecewiseLinear
