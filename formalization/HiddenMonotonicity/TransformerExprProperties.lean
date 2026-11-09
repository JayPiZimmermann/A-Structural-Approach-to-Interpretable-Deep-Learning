import HiddenMonotonicity.TransformerExpr
import HiddenMonotonicity.TransformerConvexInput

/-! Structural properties of the recursive split on doubled and signed inputs. -/
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity.TransformerDC
open Set
universe u

abbrev DoubledInput (ι : Type u) := (ι → ℝ) × (ι → ℝ)

def Expr.decompose {ι : Type u} (e : Expr ι) (x : DoubledInput ι) : ℝ × ℝ :=
  e.splitEval (fun i => (x.1 i, x.2 i))

theorem convex_doubled_orthant {ι : Type u} :
    Convex ℝ (Ici (0 : DoubledInput ι)) := by
  intro x hx y hy a b ha hb hab
  exact ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)),
    fun i => add_nonneg (mul_nonneg ha (hx.2 i)) (mul_nonneg hb (hy.2 i))⟩

/-- Both coordinates of a doubled-input projection are affine and positive on the orthant. -/
theorem input_regular {ι : Type u} (i : ι) :
    Regular (Ici (0 : DoubledInput ι)) (fun x => (x.1 i, x.2 i)) := by
  refine ⟨⟨convex_doubled_orthant, ?_⟩, ⟨convex_doubled_orthant, ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    exact le_rfl
  · intro x hx y hy a b ha hb hab
    exact le_rfl
  · intro x hx y hy hxy
    exact ⟨hxy.1 i, hxy.2 i⟩
  · intro x hx
    exact ⟨hx.1 i, hx.2 i⟩

/-- The actual recursive algorithm has convex, monotone, nonnegative heads
on the full nonnegative doubled-input orthant, at every expression depth. -/
theorem Expr.decompose_regular {ι : Type u} (e : Expr ι) :
    Regular (Ici (0 : DoubledInput ι)) e.decompose :=
  e.splitEval_regular (Ici (0 : DoubledInput ι)) convex_doubled_orthant
    (fun i (x : DoubledInput ι) => (x.1 i, x.2 i)) input_regular

theorem Expr.decompose_exact {ι : Type u} (e : Expr ι) (x : DoubledInput ι) :
    value (e.decompose x) = e.eval (x.1 - x.2) := e.splitEval_exact _

/-- Signed raw inputs are embedded by their positive and negative parts. -/
def signedInput {ι : Type u} (x : ι → ℝ) : DoubledInput ι :=
  ((fun i => max (x i) 0), fun i => max (-x i) 0)

theorem signedInput_nonnegative {ι : Type u} (x : ι → ℝ) : 0 ≤ signedInput x :=
  ⟨fun _ => le_max_right _ _, fun _ => le_max_right _ _⟩

theorem signedInput_difference {ι : Type u} (x : ι → ℝ) :
    (signedInput x).1 - (signedInput x).2 = x := by
  funext i
  exact value_constPair (x i)

def Expr.rawDecompose {ι : Type u} (e : Expr ι) (x : ι → ℝ) : ℝ × ℝ :=
  e.decompose (signedInput x)

/-- Each raw-input head is globally convex. Raw-input monotonicity is not asserted. -/
theorem Expr.rawDecompose_convex {ι : Type u} (e : Expr ι) :
    ConvexOn ℝ univ (fun x : ι → ℝ => (e.rawDecompose x).1) ∧
      ConvexOn ℝ univ (fun x : ι → ℝ => (e.rawDecompose x).2) := by
  have h := e.decompose_regular
  constructor
  · exact convex_signed_input_lift (fun z => (e.decompose z).1) h.convex_fst
      (fun _ hx _ hy hxy => (h.monotone hx hy hxy).1)
  · exact convex_signed_input_lift (fun z => (e.decompose z).2) h.convex_snd
      (fun _ hx _ hy hxy => (h.monotone hx hy hxy).2)

theorem Expr.rawDecompose_nonnegative {ι : Type u} (e : Expr ι) (x : ι → ℝ) :
    0 ≤ e.rawDecompose x := e.decompose_regular.nonnegative _ (signedInput_nonnegative x)

theorem Expr.rawDecompose_exact {ι : Type u} (e : Expr ι) (x : ι → ℝ) :
    value (e.rawDecompose x) = e.eval x := by
  rw [Expr.rawDecompose, Expr.decompose_exact, signedInput_difference]

end HiddenMonotonicity.TransformerDC
