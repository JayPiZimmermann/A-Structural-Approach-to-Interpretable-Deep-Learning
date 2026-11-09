import Thesis.Tropical
import Mathlib.Data.Fintype.Pi

/-! Constructive finite-monomial tropical propagation through the shared Network.
No representability assumption is made: the finite polynomials are built from its weights. -/
noncomputable section
namespace Thesis.Tropical
open Finset Matrix HiddenMonotonicity
variable {I : Type} [Fintype I]

/-- Independent choices of maximizing monomials realize a nonnegative weighted sum. -/
def Polynomial.weightedSum {A : Type} [Fintype A] (w : A → ℝ)
    (p : A → Polynomial I) : Polynomial I where
  Terms := (a : A) → (p a).Terms
  finite := by classical exact inferInstance
  inhabited := inferInstance
  slope := fun terms => ∑ a, w a • (p a).slope (terms a)
  intercept := fun terms => ∑ a, w a * (p a).intercept (terms a)

theorem Polynomial.eval_weightedSum {A : Type} [Fintype A] (w : A → ℝ)
    (p : A → Polynomial I) (hw : ∀ a, 0 ≤ w a) (x : I → ℝ) :
    (weightedSum w p).eval x = ∑ a, w a*(p a).eval x := by
  have he : ∀ t : (weightedSum w p).Terms,
      (weightedSum w p).slope t ⬝ᵥ x+(weightedSum w p).intercept t =
      ∑ a, w a*((p a).slope (t a) ⬝ᵥ x+(p a).intercept (t a)) := by
    intro t
    simp only [weightedSum,sum_dotProduct,smul_dotProduct,smul_eq_mul,
      ← sum_add_distrib,mul_add]
  apply le_antisymm
  · apply finiteMax_le
    intro t
    rw [he]
    exact sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
      (le_finiteMax (fun b => (p a).slope b ⬝ᵥ x+(p a).intercept b) (t a)) (hw a)
  · let choice : (a : A) → (p a).Terms := fun a =>
      Classical.choose (finiteMax_attained (fun b => (p a).slope b ⬝ᵥ x+(p a).intercept b))
    have hc : ∀ a, (p a).eval x = (p a).slope (choice a) ⬝ᵥ x+(p a).intercept (choice a) :=
      fun a => Classical.choose_spec (finiteMax_attained (fun b => (p a).slope b ⬝ᵥ x+(p a).intercept b))
    calc
      (∑ a, w a*(p a).eval x) = ∑ a, w a*((p a).slope (choice a) ⬝ᵥ x+
          (p a).intercept (choice a)) := by simp only [hc]
      _ = (weightedSum w p).slope choice ⬝ᵥ x+(weightedSum w p).intercept choice := (he choice).symm
      _ ≤ (weightedSum w p).eval x :=
        @le_finiteMax (weightedSum w p).Terms (weightedSum w p).finite
          (weightedSum w p).inhabited
          (fun t => (weightedSum w p).slope t ⬝ᵥ x+(weightedSum w p).intercept t) choice

def Polynomial.NonnegativeSlopes (p : Polynomial I) : Prop := ∀ a i, 0 ≤ p.slope a i

def Polynomial.ZeroIntercepts (p : Polynomial I) : Prop := ∀ a, p.intercept a = 0

theorem Polynomial.weightedSum_nonnegative {A : Type} [Fintype A] (w : A → ℝ)
    (p : A → Polynomial I) (hw : ∀ a, 0 ≤ w a) (hp : ∀ a, (p a).NonnegativeSlopes) :
    (weightedSum w p).NonnegativeSlopes := by
  intro t i
  change (∑ a, w a • (p a).slope (t a)) i ≥ 0
  rw [Finset.sum_apply]
  exact sum_nonneg fun a _ => mul_nonneg (hw a) (hp a (t a) i)

theorem Polynomial.weightedSum_zero {A : Type} [Fintype A] (w : A → ℝ)
    (p : A → Polynomial I) (hp : ∀ a, (p a).ZeroIntercepts) :
    (weightedSum w p).ZeroIntercepts := by
  intro t
  exact sum_eq_zero fun a _ => by rw [hp a]; exact mul_zero _

theorem Polynomial.add_nonnegative (p q : Polynomial I)
    (hp : p.NonnegativeSlopes) (hq : q.NonnegativeSlopes) : (p.add q).NonnegativeSlopes :=
  fun a i => add_nonneg (hp a.1 i) (hq a.2 i)

theorem Polynomial.max_nonnegative (p q : Polynomial I)
    (hp : p.NonnegativeSlopes) (hq : q.NonnegativeSlopes) : (p.max q).NonnegativeSlopes := by
  intro a i; cases a with
  | inl a => exact hp a i
  | inr a => exact hq a i

theorem Polynomial.add_zero (p q : Polynomial I)
    (hp : p.ZeroIntercepts) (hq : q.ZeroIntercepts) : (p.add q).ZeroIntercepts := by
  intro a; change p.intercept a.1+q.intercept a.2=0; rw [hp,hq,zero_add]

theorem Polynomial.max_zero (p q : Polynomial I)
    (hp : p.ZeroIntercepts) (hq : q.ZeroIntercepts) : (p.max q).ZeroIntercepts := by
  intro a; cases a with
  | inl a => exact hp a
  | inr a => exact hq a

theorem Polynomial.homogeneous (p : Polynomial I) (hp : p.ZeroIntercepts)
    (c : ℝ) (hc : 0 ≤ c) (x : I → ℝ) : p.eval (c • x) = c*p.eval x := by
  have he : p.eval (c • x) = (p.scale c).eval x := by
    have hp' : ∀ a, p.intercept a = 0 := hp
    simp only [eval,scale,dotProduct_smul,smul_dotProduct,smul_eq_mul,hp',mul_zero,_root_.add_zero]
  rw [he,p.eval_scale c hc x]

def polynomialAffine {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (b : Fin k → ℝ)
    (p q : Fin n → Polynomial I) (i : Fin k) : Polynomial I :=
  ((Polynomial.weightedSum (wp i) p).add (Polynomial.weightedSum (wn i) q)).add
    (Polynomial.monomial 0 (b i))

theorem polynomialAffine_eval {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ) (b : Fin k → ℝ)
    (p q : Fin n → Polynomial I) (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j)
    (x : I → ℝ) (i : Fin k) :
    (polynomialAffine wp wn b p q i).eval x =
      (wp.mulVec (fun j => (p j).eval x)+wn.mulVec (fun j => (q j).eval x)+b) i := by
  simp only [polynomialAffine,Polynomial.eval_add,Polynomial.eval_weightedSum _ _ (hwp i),
    Polynomial.eval_weightedSum _ _ (hwn i),Polynomial.eval_monomial,zero_dotProduct,
    zero_add,Matrix.mulVec,dotProduct,Pi.add_apply,Pi.zero_apply,zero_mul,sum_const_zero]

theorem polynomialAffine_nonnegative {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (b : Fin k → ℝ) (p q : Fin n → Polynomial I)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j)
    (hp : ∀ j, (p j).NonnegativeSlopes) (hq : ∀ j, (q j).NonnegativeSlopes) (i : Fin k) :
    (polynomialAffine wp wn b p q i).NonnegativeSlopes := by
  apply Polynomial.add_nonnegative
  · exact Polynomial.add_nonnegative _ _
      (Polynomial.weightedSum_nonnegative _ _ (hwp i) hp)
      (Polynomial.weightedSum_nonnegative _ _ (hwn i) hq)
  · intro _ _; exact le_rfl

theorem polynomialAffine_zero {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (p q : Fin n → Polynomial I)
    (hp : ∀ j, (p j).ZeroIntercepts) (hq : ∀ j, (q j).ZeroIntercepts) (i : Fin k) :
    (polynomialAffine wp wn 0 p q i).ZeroIntercepts := by
  apply Polynomial.add_zero
  · exact Polynomial.add_zero _ _ (Polynomial.weightedSum_zero _ _ hp)
      (Polynomial.weightedSum_zero _ _ hq)
  · intro _; rfl

/-- Explicit finite monomials of every split coordinate, propagated using products,
nonnegative powers, and binary tropical maxima. -/
def tropicalSplit {n m} : Network n m → (Fin n → Polynomial I) → (Fin n → Polynomial I) →
    (Fin m → Polynomial I) × (Fin m → Polynomial I)
  | .output _, p, q => (p,q)
  | .layer wp wn bp bn tail, p, q =>
      let zp := polynomialAffine wp wn bp p q
      let zn := polynomialAffine wn wp bn p q
      tropicalSplit tail (fun i => (zp i).max (zn i)) zn

/-- The constructed tropical polynomials evaluate exactly to the implemented split
forward pass at every width and depth, including arbitrary split biases. -/
theorem tropicalSplit_eval {n m} (net : Network n m) (hn : net.Nonnegative)
    (p q : Fin n → Polynomial I) (x : I → ℝ) :
    ((fun i => ((tropicalSplit net p q).1 i).eval x),
     (fun i => ((tropicalSplit net p q).2 i).eval x)) =
      net.split (fun j => (p j).eval x) (fun j => (q j).eval x) := by
  induction net with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      rcases hn with ⟨hwp,hwn,ht⟩
      simp only [tropicalSplit]
      rw [ih ht]
      simp only [Network.split,Polynomial.eval_max,polynomialAffine_eval _ _ _ _ _ hwp hwn,
        polynomialAffine_eval _ _ _ _ _ hwn hwp]

theorem tropicalSplit_nonnegative {n m} (net : Network n m) (hn : net.Nonnegative)
    (p q : Fin n → Polynomial I)
    (hp : ∀ j, (p j).NonnegativeSlopes) (hq : ∀ j, (q j).NonnegativeSlopes) :
    (∀ i, ((tropicalSplit net p q).1 i).NonnegativeSlopes) ∧
    (∀ i, ((tropicalSplit net p q).2 i).NonnegativeSlopes) := by
  induction net with
  | output n => exact ⟨hp,hq⟩
  | layer wp wn bp bn tail ih =>
      rcases hn with ⟨hwp,hwn,ht⟩
      apply ih ht
      · intro i
        exact Polynomial.max_nonnegative _ _
          (polynomialAffine_nonnegative _ _ _ _ _ hwp hwn hp hq i)
          (polynomialAffine_nonnegative _ _ _ _ _ hwn hwp hp hq i)
      · exact polynomialAffine_nonnegative _ _ _ _ _ hwn hwp hp hq

def BiasFree {n m} : Network n m → Prop
  | .output _ => True
  | .layer _ _ bp bn tail => bp = 0 ∧ bn = 0 ∧ BiasFree tail

theorem tropicalSplit_zero {n m} (net : Network n m) (hb : BiasFree net)
    (p q : Fin n → Polynomial I)
    (hp : ∀ j, (p j).ZeroIntercepts) (hq : ∀ j, (q j).ZeroIntercepts) :
    (∀ i, ((tropicalSplit net p q).1 i).ZeroIntercepts) ∧
    (∀ i, ((tropicalSplit net p q).2 i).ZeroIntercepts) := by
  induction net with
  | output n => exact ⟨hp,hq⟩
  | layer wp wn bp bn tail ih =>
      rcases hb with ⟨rfl,rfl,ht⟩
      apply ih ht
      · intro i
        exact Polynomial.max_zero _ _ (polynomialAffine_zero _ _ _ _ hp hq i)
          (polynomialAffine_zero _ _ _ _ hp hq i)
      · exact polynomialAffine_zero _ _ _ _ hp hq

def coordinate [DecidableEq I] (i : I) : Polynomial I := Polynomial.monomial (Pi.single i (1 : ℝ)) 0

theorem coordinate_eval [DecidableEq I] (i : I) (x : I → ℝ) : (coordinate i).eval x = x i := by
  rw [coordinate,Polynomial.eval_monomial,single_one_dotProduct,add_zero]

theorem coordinate_nonnegative [DecidableEq I] (i : I) : (coordinate i).NonnegativeSlopes := by
  intro _ j
  change 0 ≤ (Pi.single i (1 : ℝ) : I → ℝ) j
  by_cases h : j=i
  · subst j; simp
  · simp [Pi.single_apply,h]

def inputPolynomials (n : ℕ) : (Fin n → Polynomial (Fin n ⊕ Fin n)) ×
    (Fin n → Polynomial (Fin n ⊕ Fin n)) :=
  (fun i => coordinate (Sum.inl i),fun i => coordinate (Sum.inr i))

/-- thm:split_tropical_rational, constructively: finite monotone max-affine
polynomials represent both actual split streams; their difference is the network. -/
theorem network_tropical_representation {n m} (net : Network n m) (hn : net.Nonnegative) :
    ∃ g h : Fin m → Polynomial (Fin n ⊕ Fin n),
      (∀ i, (g i).NonnegativeSlopes ∧ (h i).NonnegativeSlopes) ∧
      ∀ p q, (∀ i, (g i).eval (Sum.elim p q) = (net.split p q).1 i) ∧
        (∀ i, (h i).eval (Sum.elim p q) = (net.split p q).2 i) ∧
        (∀ i, (g i).eval (Sum.elim p q)-(h i).eval (Sum.elim p q) = net.eval (p-q) i) := by
  let polys := tropicalSplit net (inputPolynomials n).1 (inputPolynomials n).2
  have hn' := tropicalSplit_nonnegative net hn (inputPolynomials n).1 (inputPolynomials n).2
    (fun i => coordinate_nonnegative (Sum.inl i)) (fun i => coordinate_nonnegative (Sum.inr i))
  refine ⟨polys.1,polys.2,fun i => ⟨hn'.1 i,hn'.2 i⟩,?_⟩
  intro p q
  have he := tropicalSplit_eval net hn (inputPolynomials n).1 (inputPolynomials n).2 (Sum.elim p q)
  simp only [inputPolynomials,coordinate_eval,Sum.elim_inl,Sum.elim_inr] at he
  have hg : ∀ i, (polys.1 i).eval (Sum.elim p q) = (net.split p q).1 i :=
    fun i => congrFun (congrArg Prod.fst he) i
  have hh : ∀ i, (polys.2 i).eval (Sum.elim p q) = (net.split p q).2 i :=
    fun i => congrFun (congrArg Prod.snd he) i
  refine ⟨hg,hh,?_⟩
  intro i
  rw [hg,hh]
  exact congrFun (net.correct p q) i

/-- Bias-free streams are actual support functions of finite Newton polytopes,
with nonnegative vertices and positive homogeneity. -/
theorem biasfree_network_support_representation {n m} (net : Network n m)
    (hn : net.Nonnegative) (hb : BiasFree net) :
    ∃ g h : Fin m → Polynomial (Fin n ⊕ Fin n),
      (∀ i, (g i).NonnegativeSlopes ∧ (h i).NonnegativeSlopes ∧
        (g i).ZeroIntercepts ∧ (h i).ZeroIntercepts) ∧
      ∀ p q i, support (g i).newton (Sum.elim p q)-support (h i).newton (Sum.elim p q) =
        net.eval (p-q) i := by
  let p := (inputPolynomials n).1
  let q := (inputPolynomials n).2
  let polys := tropicalSplit net p q
  have hn' := tropicalSplit_nonnegative net hn p q
    (fun i => coordinate_nonnegative (Sum.inl i)) (fun i => coordinate_nonnegative (Sum.inr i))
  have hz := tropicalSplit_zero net hb p q (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨polys.1,polys.2,fun i => ⟨hn'.1 i,hn'.2 i,hz.1 i,hz.2 i⟩,?_⟩
  intro x y i
  rw [← Polynomial.eval_eq_support _ (hz.1 i),← Polynomial.eval_eq_support _ (hz.2 i)]
  have he := tropicalSplit_eval net hn p q (Sum.elim x y)
  simp only [p,q,inputPolynomials,coordinate_eval,Sum.elim_inl,Sum.elim_inr] at he
  have hg := congrFun (congrArg Prod.fst he) i
  have hh := congrFun (congrArg Prod.snd he) i
  change (polys.1 i).eval (Sum.elim x y) = (net.split x y).1 i at hg
  change (polys.2 i).eval (Sum.elim x y) = (net.split x y).2 i at hh
  change (polys.1 i).eval (Sum.elim x y)-(polys.2 i).eval (Sum.elim x y)=_
  rw [hg,hh]
  exact congrFun (net.correct x y) i

/-- The same tropical representation includes a signed, ungated affine final layer. -/
theorem affine_network_tropical_representation {n m k} (net : Network n m)
    (hn : net.Nonnegative) (wp wn : Matrix (Fin k) (Fin m) ℝ) (bp bn : Fin k → ℝ)
    (hwp : ∀ i j, 0 ≤ wp i j) (hwn : ∀ i j, 0 ≤ wn i j) :
    ∃ g h : Fin k → Polynomial (Fin n ⊕ Fin n),
      (∀ i, (g i).NonnegativeSlopes ∧ (h i).NonnegativeSlopes) ∧
      ∀ p q i, (g i).eval (Sum.elim p q)-(h i).eval (Sum.elim p q) =
        ((wp-wn).mulVec (net.eval (p-q))+(bp-bn)) i := by
  obtain ⟨g,h,hpos,he⟩ := network_tropical_representation net hn
  refine ⟨polynomialAffine wp wn bp g h,polynomialAffine wn wp bn g h,?_,?_⟩
  · intro i
    exact ⟨polynomialAffine_nonnegative _ _ _ _ _ hwp hwn (fun i => (hpos i).1)
      (fun i => (hpos i).2) i,
      polynomialAffine_nonnegative _ _ _ _ _ hwn hwp (fun i => (hpos i).1)
      (fun i => (hpos i).2) i⟩
  · intro p q i
    rw [polynomialAffine_eval _ _ _ _ _ hwp hwn,polynomialAffine_eval _ _ _ _ _ hwn hwp]
    have hre : (fun j => (g j).eval (Sum.elim p q))-(fun j => (h j).eval (Sum.elim p q)) =
        net.eval (p-q) := funext (he p q).2.2
    rw [← hre,sub_mulVec,mulVec_sub,mulVec_sub]
    simp only [Pi.add_apply,Pi.sub_apply]
    ring

end Thesis.Tropical
