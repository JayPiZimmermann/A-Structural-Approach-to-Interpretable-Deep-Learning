import Thesis.SoftplusGameOccupation
import HiddenMonotonicity.PrefixSources

noncomputable section
namespace Thesis.SoftplusGame
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward
open Thesis.ReLUNetGame Thesis.RoutingBackward Matrix
open scoped BigOperators

/-- Restriction of the actual full strategy to states above a shared layer cut. -/
def suffixStrategy {a b c} : (pre : Network a b) → (suffix : Network b c) →
    Strategy (pre.append suffix) → Strategy suffix
  | .output _, _, profile => profile
  | .layer _ _ _ _ tail, suffix, profile => suffixStrategy tail suffix profile.2

/-- Restriction to actual predecessor subgames rooted at a prefix activation. -/
def prefixStrategy {a b c} : (pre : Network a b) → (suffix : Network b c) →
    Strategy (pre.append suffix) → Strategy pre
  | .output _, _, _ => ()
  | .layer _ _ _ _ tail, suffix, profile => (profile.1,prefixStrategy tail suffix profile.2)

theorem prefixStrategy_gibbs {a b c} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (x : Vec a) :
    prefixStrategy pre suffix (gibbsStrategy θ (pre.append suffix) x)=gibbsStrategy θ pre x := by
  induction pre with
  | output n => rfl
  | layer wp wn bp bn tail ih =>
      change (_,prefixStrategy tail suffix (gibbsStrategy θ (tail.append suffix) _))=(_,gibbsStrategy θ tail _)
      rw [ih]
      rfl

theorem softEval_append {a b c} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (x : Vec a) :
    softEval θ (pre.append suffix) x=softEval θ suffix (softEval θ pre x) := by
  induction pre with
  | output n => rfl
  | layer wp wn bp bn tail ih => exact ih _ _

theorem suffixStrategy_gibbs {a b c} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (x : Vec a) :
    suffixStrategy pre suffix (gibbsStrategy θ (pre.append suffix) x)=
      gibbsStrategy θ suffix (softEval θ pre x) := by
  induction pre with
  | output n => rfl
  | layer wp wn bp bn tail ih => exact ih _ _

/-- The full-network SPNE restricts to the actual subgame at every shared layer
cut, evaluated at the true prefix Softplus activation vector. -/
theorem spne_suffix {a b c} (pre : Network a b) (suffix : Network b c)
    (θ : ℝ) (hθ : 0<θ) (hp : pre.Nonnegative) (hs : suffix.Nonnegative)
    (x : Vec a) (plus minus : Strategy (pre.append suffix))
    (hsp : SubgamePerfect θ (pre.append suffix) plus minus x (-x)) :
    SubgamePerfect θ suffix (suffixStrategy pre suffix plus) (suffixStrategy pre suffix minus)
      (softEval θ pre x) (-(softEval θ pre x)) := by
  rcases (subgamePerfect_iff (pre.append suffix) θ hθ (pre.append_nonnegative suffix hp hs)
    x plus minus).mp hsp with ⟨rfl,rfl⟩
  rw [suffixStrategy_gibbs]
  exact gibbs_subgamePerfect suffix θ hθ hs _

/-- Every true predecessor subgame inherits the full strategy's Gibbs
restriction and saddle bounds against arbitrary randomized deviations. -/
theorem spne_prefix_saddle {a b c} (pre : Network a b) (suffix : Network b c)
    (θ : ℝ) (hθ : 0<θ) (hp : pre.Nonnegative) (hs : suffix.Nonnegative)
    (x : Vec a) (plus minus : Strategy (pre.append suffix))
    (hsp : SubgamePerfect θ (pre.append suffix) plus minus x (-x))
    (plusDev minusDev : Strategy pre) :
    (policyValue θ pre plusDev (prefixStrategy pre suffix minus) x (-x)).1 ≤ softEval θ pre x ∧
    (policyValue θ pre plusDev (prefixStrategy pre suffix minus) x (-x)).2 ≤ -softEval θ pre x ∧
    policyValue θ pre (prefixStrategy pre suffix plus) (prefixStrategy pre suffix minus) x (-x)=
      (softEval θ pre x,-softEval θ pre x) ∧
    softEval θ pre x ≤ (policyValue θ pre (prefixStrategy pre suffix plus) minusDev x (-x)).1 ∧
    -softEval θ pre x ≤ (policyValue θ pre (prefixStrategy pre suffix plus) minusDev x (-x)).2 := by
  rcases (subgamePerfect_iff (pre.append suffix) θ hθ (pre.append_nonnegative suffix hp hs)
    x plus minus).mp hsp with ⟨rfl,rfl⟩
  rw [prefixStrategy_gibbs]
  exact softplus_saddle pre θ hθ hp x plusDev minusDev

/-- The source activation-to-activation gradient formula under the actual full
network SPNE, with its genuine restricted policies and forward prefix values. -/
theorem spne_intermediate_gradient {a b c} (pre : Network a b) (suffix : Network b c)
    (θ : ℝ) (hθ : 0<θ) (hp : pre.Nonnegative) (hs : suffix.Nonnegative)
    (x : Vec a) (plus minus : Strategy (pre.append suffix))
    (hsp : SubgamePerfect θ (pre.append suffix) plus minus x (-x))
    (j : Fin c) (i : Fin b) (q : Bool) :
    fderiv ℝ (softEval θ suffix) (softEval θ pre x) (Pi.single i 1) j =
      (if q then (-1 : ℝ) else 1)*
        (profileOccupation suffix θ (suffixStrategy pre suffix plus) (suffixStrategy pre suffix minus)
          (softEval θ pre x) j i q false-
         profileOccupation suffix θ (suffixStrategy pre suffix plus) (suffixStrategy pre suffix minus)
          (softEval θ pre x) j i q true) :=
  spne_gradient suffix θ hθ hs _ _ _ (spne_suffix pre suffix θ hθ hp hs x plus minus hsp) j i q

end Thesis.SoftplusGame
