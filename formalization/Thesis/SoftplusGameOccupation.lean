import Thesis.SoftplusReadout

noncomputable section
namespace Thesis.SoftplusGame
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward
open Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix
open scoped BigOperators

/-- Probability of an ordinary-input-reaching path under the actual two-player
profile. The last two signs are absolute state owners. Stopped/cemetery paths
contribute zero to ordinary-input occupation and are omitted from this subset.
`softTrace` supplies only the existing varying-width path index type. -/
def profileProbability {n m} (θ : ℝ) : (net : Network n m) → Strategy net → Strategy net →
    (x : Vec n) → Fin m → Fin n → Bool → Bool → Paths (softTrace θ net x) → ℝ
  | .output _, _, _, _, j, i, q, r, _ => if j=i ∧ q=r then 1 else 0
  | .layer wp wn bp bn tail, plus, minus, x, j, i, q, r, path =>
      ((if Bool.xor r path.2.1 then (minus.1 path.1).val else (plus.1 path.1).val)*
        (if path.2.1 then wn path.1 i else wp path.1 i)/fanIn wp wn path.1)*
      profileProbability θ tail plus.2 minus.2 (softLayer θ wp wn bp bn x)
        j path.1 q (Bool.xor r path.2.1) path.2.2

/-- The path product is the actual mixed-policy transition to the next signed
state; no canonical Gibbs probability is built into this off-equilibrium law. -/
theorem profile_step_transition {n k} (wp wn : Matrix (Fin k) (Fin n) ℝ)
    (plus minus : Fin k → Set.Icc (0 : ℝ) 1) (j : Fin k) (i : Fin n) (r b : Bool) :
    mixedTransition (if Bool.xor r b then minus j else plus j) wp wn j
      (Bool.xor r b) (some (i,r)) =
      (if Bool.xor r b then (minus j).val else (plus j).val)*
        (if b then wn j i else wp j i)/fanIn wp wn j := by
  cases r <;> cases b <;>
    simp [mixedTransition,Thesis.StoppingBoundary.transition] <;> ring

theorem profileProbability_gibbs {n m} (net : Network n m) (θ : ℝ) (x : Vec n)
    (j : Fin m) (i : Fin n) (q r : Bool) (path : Paths (softTrace θ net x)) :
    profileProbability θ net (gibbsStrategy θ net x) (gibbsStrategy θ net x) x j i q r path =
      softProbability θ net x j i (Bool.xor q r) path := by
  induction net generalizing q r with
  | output n => cases q <;> cases r <;> simp [profileProbability,softProbability]
  | layer wp wn bp bn tail ih =>
      simp only [profileProbability,gibbsStrategy,gibbsProbability,ite_self,softProbability]
      rw [ih]
      congr 2
      cases q <;> cases r <;> cases path.2.1 <;> rfl

def profileOccupation {n m} (net : Network n m) (θ : ℝ) (plus minus : Strategy net)
    (x : Vec n) (j : Fin m) (i : Fin n) (q r : Bool) : ℝ :=
  ∑ path : Paths (softTrace θ net x),softDiscount θ net x path*
    profileProbability θ net plus minus x j i q r path

theorem spne_occupation_eq {n m} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net)
    (hsp : SubgamePerfect θ net plus minus x (-x)) (j : Fin m) (i : Fin n) (q r : Bool) :
    profileOccupation net θ plus minus x j i q r=softOccupation net θ x j i (Bool.xor q r) := by
  rcases (subgamePerfect_iff net θ hθ hw x plus minus).mp hsp with ⟨rfl,rfl⟩
  simp only [profileOccupation,profileProbability_gibbs,softOccupation]

/-- Source gradient formula with the actual SPNE profile's path probabilities.
The signed difference is a derivative of the ordinary Softplus activation;
individual soft split coordinates are not identified with these occupations. -/
theorem spne_gradient {n m} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net)
    (hsp : SubgamePerfect θ net plus minus x (-x)) (j : Fin m) (i : Fin n) (q : Bool) :
    fderiv ℝ (softEval θ net) x (Pi.single i 1) j =
      (if q then (-1 : ℝ) else 1)*
        (profileOccupation net θ plus minus x j i q false-
          profileOccupation net θ plus minus x j i q true) := by
  rw [spne_occupation_eq net θ hθ hw x plus minus hsp,
    spne_occupation_eq net θ hθ hw x plus minus hsp,
    Thesis.SoftplusBoundary.gradient_occupation net θ hθ hw x j i]
  cases q <;> simp <;> ring

theorem spne_affine_gradient_profile {n m r} (net : Network n m) (θ : ℝ) (hθ : 0<θ)
    (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net)
    (hsp : SubgamePerfect θ net plus minus x (-x))
    (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (j : Fin r) (i : Fin n) (q : Bool) :
    fderiv ℝ (affineOutput θ net C b) x (Pi.single i 1) j =
      ∑ h,C j h*(if q then (-1 : ℝ) else 1)*
        (profileOccupation net θ plus minus x h i q false-
          profileOccupation net θ plus minus x h i q true) := by
  rw [(affineOutput_hasFDerivAt net θ hθ C b x).fderiv]
  change (∑ h,C j h*(softTrace θ net x).originalJac (Pi.single i 1) h)=_
  apply Finset.sum_congr rfl
  intro h _
  rw [← (softEval_hasFDerivAt net θ hθ x).fderiv,
    spne_gradient net θ hθ hw x plus minus hsp h i q]
  ring

end Thesis.SoftplusGame
