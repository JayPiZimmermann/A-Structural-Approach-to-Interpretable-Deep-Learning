import HiddenMonotonicity.TransformerDefinition
import HiddenMonotonicity.TransformerExprProperties

/-! Exact DC decompositions for the actual finite Transformer model. The list
of blocks, number of heads, dimensions and signed parameters are unrestricted
except for the positive normalization constants and nonempty masks in the model. -/
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity.TransformerDC
open Set

/-- Compile the same Transformer parameters and recursively evaluate every scalar
operation with its explicit two-stream formula. -/
def Transformer.decompose {t d o : ℕ} (net : Transformer t d o)
    (x : DoubledInput (Fin t × Fin d)) (i : Fin o) : ℝ × ℝ :=
  (net.syntax i).decompose x

theorem Transformer.decompose_exact {t d o : ℕ} (net : Transformer t d o)
    (x : DoubledInput (Fin t × Fin d)) (i : Fin o) :
    (net.decompose x i).1 - (net.decompose x i).2 = net.eval (x.1 - x.2) i := by
  exact ((net.syntax i).decompose_exact x).trans (net.eval_syntax (x.1 - x.2) i)

theorem Transformer.decompose_regular {t d o : ℕ} (net : Transformer t d o)
    (i : Fin o) :
    Regular (Ici (0 : DoubledInput (Fin t × Fin d))) (fun x => net.decompose x i) :=
  (net.syntax i).decompose_regular

theorem Transformer.decompose_monotoneOn {t d o : ℕ} (net : Transformer t d o) :
    MonotoneOn net.decompose (Ici (0 : DoubledInput (Fin t × Fin d))) := by
  intro x hx y hy hxy i
  exact (net.decompose_regular i).monotone hx hy hxy

/-- Arbitrary-depth Transformer DC theorem. Every block in the finite list
uses the actual coupled softmax, products and input-dependent epsilon LayerNorm. -/
theorem Transformer.dc_decomposition {t d o : ℕ} (net : Transformer t d o) :
    MonotoneOn net.decompose (Ici (0 : DoubledInput (Fin t × Fin d))) ∧
    (∀ i, ConvexOn ℝ (Ici (0 : DoubledInput (Fin t × Fin d)))
      (fun x => (net.decompose x i).1)) ∧
    (∀ i, ConvexOn ℝ (Ici (0 : DoubledInput (Fin t × Fin d)))
      (fun x => (net.decompose x i).2)) ∧
    (∀ x, 0 ≤ x → 0 ≤ net.decompose x) ∧
    ∀ x i, (net.decompose x i).1 - (net.decompose x i).2 =
      net.eval (x.1 - x.2) i := by
  refine ⟨net.decompose_monotoneOn, ?_, ?_, ?_, net.decompose_exact⟩
  · intro i
    exact (net.decompose_regular i).convex_fst
  · intro i
    exact (net.decompose_regular i).convex_snd
  · intro x hx i
    exact (net.decompose_regular i).nonnegative x hx

/-- The positive/negative input lift gives a DC representation on all real embeddings. -/
def Transformer.rawDecompose {t d o : ℕ} (net : Transformer t d o)
    (x : Fin t × Fin d → ℝ) (i : Fin o) : ℝ × ℝ :=
  net.decompose (signedInput x) i

/-- The raw-input heads are globally convex and nonnegative and recover every
signed logit exactly. Monotonicity is confined to the expanded-domain theorem. -/
theorem Transformer.raw_dc_decomposition {t d o : ℕ} (net : Transformer t d o) :
    (∀ i, ConvexOn ℝ univ (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).1)) ∧
    (∀ i, ConvexOn ℝ univ (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).2)) ∧
    (∀ x, 0 ≤ net.rawDecompose x) ∧
    ∀ x i, (net.rawDecompose x i).1 - (net.rawDecompose x i).2 = net.eval x i := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact (net.syntax i).rawDecompose_convex.1
  · intro i
    exact (net.syntax i).rawDecompose_convex.2
  · intro x i
    exact (net.syntax i).rawDecompose_nonnegative x
  · intro x i
    exact ((net.syntax i).rawDecompose_exact x).trans (net.eval_syntax x i)

end HiddenMonotonicity.TransformerDC
