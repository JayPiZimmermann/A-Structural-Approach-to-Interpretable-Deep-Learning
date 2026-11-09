import Thesis.SoftplusPolicies
import Thesis.SoftplusEquilibrium
import Thesis.SoftplusPlayerValues
import Thesis.SoftplusReadout
import Thesis.SoftplusGameOccupation
import Thesis.SoftplusSubgames
import Thesis.SoftplusTransitionPayoff
set_option pp.universes true
set_option pp.explicit true
set_option autoImplicit false
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n k : ℕ} (r : Set.Icc (0 : ℝ) 1) (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool), (∑ target,mixedTransition r wp wn j turn target)=1) := @Thesis.SoftplusGame.mixedTransition_normalized
#check @Thesis.SoftplusGame.mixedTransition_normalized
#print axioms Thesis.SoftplusGame.mixedTransition_normalized
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n k : ℕ} (r : Set.Icc (0 : ℝ) 1) (wp wn : Matrix (Fin k) (Fin n) ℝ) (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (j : Fin k) (turn : Bool) (target : Option (Fin n × Bool)), 0≤mixedTransition r wp wn j turn target) := @Thesis.SoftplusGame.mixedTransition_nonnegative
#check @Thesis.SoftplusGame.mixedTransition_nonnegative
#print axioms Thesis.SoftplusGame.mixedTransition_nonnegative
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n k : ℕ} (r : Set.Icc (0 : ℝ) 1) (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool) (hz : fanIn wp wn j=0), mixedTransition r wp wn j turn none=1) := @Thesis.SoftplusGame.mixed_zero_fanIn_absorbs
#check @Thesis.SoftplusGame.mixed_zero_fanIn_absorbs
#print axioms Thesis.SoftplusGame.mixed_zero_fanIn_absorbs
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (hw : ∀ j i,0≤wp j i ∧ 0≤wn j i) (b : Vec k) (p q : Vec n) (j : Fin k), continuation wp wn b p q j=((wp *ᵥ p+wn *ᵥ q)+b) j) := @Thesis.SoftplusGame.continuation_recovery_total
#check @Thesis.SoftplusGame.continuation_recovery_total
#print axioms Thesis.SoftplusGame.continuation_recovery_total
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net),  (policyValue θ net plus (gibbsStrategy θ net x) x (-x)).1≤softEval θ net x ∧  (policyValue θ net plus (gibbsStrategy θ net x) x (-x)).2≤ -softEval θ net x ∧  policyValue θ net (gibbsStrategy θ net x) (gibbsStrategy θ net x) x (-x)=(softEval θ net x,-softEval θ net x) ∧  softEval θ net x≤(policyValue θ net (gibbsStrategy θ net x) minus x (-x)).1 ∧  -softEval θ net x≤(policyValue θ net (gibbsStrategy θ net x) minus x (-x)).2) := @Thesis.SoftplusGame.softplus_saddle
#check @Thesis.SoftplusGame.softplus_saddle
#print axioms Thesis.SoftplusGame.softplus_saddle
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net), SubgamePerfect θ net plus minus x (-x) ↔ plus=gibbsStrategy θ net x ∧ minus=gibbsStrategy θ net x) := @Thesis.SoftplusGame.subgamePerfect_iff
#check @Thesis.SoftplusGame.subgamePerfect_iff
#print axioms Thesis.SoftplusGame.subgamePerfect_iff
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hw : net.Nonnegative) (plus minus : Strategy net) (v : PlayerValues n), advantage (playerValue θ net plus minus v)=policyValue θ net plus minus (advantage v).1 (advantage v).2) := @Thesis.SoftplusGame.playerValue_advantage
#check @Thesis.SoftplusGame.playerValue_advantage
#print axioms Thesis.SoftplusGame.playerValue_advantage
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : PairVec n), playerValue θ net (gibbsStrategy θ net (x.1-x.2)) (gibbsStrategy θ net (x.1-x.2)) (pairValues x)=pairValues (net.decomposeWith (fun z => softSplit θ z.1 z.2) x)) := @Thesis.SoftplusGame.playerValue_gibbs
#check @Thesis.SoftplusGame.playerValue_gibbs
#print axioms Thesis.SoftplusGame.playerValue_gibbs
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n m r : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net) (wp wn : Matrix (Fin r) (Fin m) ℝ) (hrow : ∀ j i,0≤wp j i ∧ 0≤wn j i) (b : Vec r) (j : Fin r),  let read := fun v : PairVec m => continuation wp wn b v.1 v.2 j;  read (policyValue θ net plus (gibbsStrategy θ net x) x (-x))≤affineOutput θ net (wp-wn) b x j ∧  read (policyValue θ net (gibbsStrategy θ net x) (gibbsStrategy θ net x) x (-x))=affineOutput θ net (wp-wn) b x j ∧  affineOutput θ net (wp-wn) b x j≤read (policyValue θ net (gibbsStrategy θ net x) minus x (-x))) := @Thesis.SoftplusGame.affine_saddle
#check @Thesis.SoftplusGame.affine_saddle
#print axioms Thesis.SoftplusGame.affine_saddle
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : PairVec n),  SubgamePerfect θ net (gibbsStrategy θ net (x.1-x.2)) (gibbsStrategy θ net (x.1-x.2)) (x.1-x.2) (-(x.1-x.2)) ∧  (∀ plus minus : Strategy net,SubgamePerfect θ net plus minus (x.1-x.2) (-(x.1-x.2)) ↔ plus=gibbsStrategy θ net (x.1-x.2) ∧ minus=gibbsStrategy θ net (x.1-x.2)) ∧  playerValue θ net (gibbsStrategy θ net (x.1-x.2)) (gibbsStrategy θ net (x.1-x.2)) (pairValues x)=pairValues (net.decomposeWith (fun z => softSplit θ z.1 z.2) x) ∧  (net.decomposeWith (fun z => softSplit θ z.1 z.2) x).1-(net.decomposeWith (fun z => softSplit θ z.1 z.2) x).2=softEval θ net (x.1-x.2)) := @Thesis.SoftplusGame.softplus_forward_spne
#check @Thesis.SoftplusGame.softplus_forward_spne
#print axioms Thesis.SoftplusGame.softplus_forward_spne
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n k : ℕ} (wp wn : Matrix (Fin k) (Fin n) ℝ) (plus minus : Fin k → Set.Icc (0 : ℝ) 1) (j : Fin k) (i : Fin n) (r b : Bool), mixedTransition (if Bool.xor r b then minus j else plus j) wp wn j (Bool.xor r b) (some (i,r))=(if Bool.xor r b then (minus j).val else (plus j).val)*(if b then wn j i else wp j i)/fanIn wp wn j) := @Thesis.SoftplusGame.profile_step_transition
#check @Thesis.SoftplusGame.profile_step_transition
#print axioms Thesis.SoftplusGame.profile_step_transition
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (x : Vec n) (j : Fin m) (i : Fin n) (q r : Bool) (path : Paths (softTrace θ net x)), profileProbability θ net (gibbsStrategy θ net x) (gibbsStrategy θ net x) x j i q r path=softProbability θ net x j i (Bool.xor q r) path) := @Thesis.SoftplusGame.profileProbability_gibbs
#check @Thesis.SoftplusGame.profileProbability_gibbs
#print axioms Thesis.SoftplusGame.profileProbability_gibbs
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net) (hsp : SubgamePerfect θ net plus minus x (-x)) (j : Fin m) (i : Fin n) (q r : Bool), profileOccupation net θ plus minus x j i q r=softOccupation net θ x j i (Bool.xor q r)) := @Thesis.SoftplusGame.spne_occupation_eq
#check @Thesis.SoftplusGame.spne_occupation_eq
#print axioms Thesis.SoftplusGame.spne_occupation_eq
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n m : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net) (hsp : SubgamePerfect θ net plus minus x (-x)) (j : Fin m) (i : Fin n) (q : Bool), fderiv ℝ (softEval θ net) x (Pi.single i 1) j=(if q then (-1 : ℝ) else 1)*(profileOccupation net θ plus minus x j i q false-profileOccupation net θ plus minus x j i q true)) := @Thesis.SoftplusGame.spne_gradient
#check @Thesis.SoftplusGame.spne_gradient
#print axioms Thesis.SoftplusGame.spne_gradient
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n m r : ℕ} (net : Network n m) (θ : ℝ) (hθ : 0<θ) (hw : net.Nonnegative) (x : Vec n) (plus minus : Strategy net) (hsp : SubgamePerfect θ net plus minus x (-x)) (C : Matrix (Fin r) (Fin m) ℝ) (b : Vec r) (j : Fin r) (i : Fin n) (q : Bool), fderiv ℝ (affineOutput θ net C b) x (Pi.single i 1) j=∑ h,C j h*(if q then (-1 : ℝ) else 1)*(profileOccupation net θ plus minus x h i q false-profileOccupation net θ plus minus x h i q true)) := @Thesis.SoftplusGame.spne_affine_gradient_profile
#check @Thesis.SoftplusGame.spne_affine_gradient_profile
#print axioms Thesis.SoftplusGame.spne_affine_gradient_profile
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {a b c : ℕ} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (x : Vec a), softEval θ (pre.append suffix) x=softEval θ suffix (softEval θ pre x)) := @Thesis.SoftplusGame.softEval_append
#check @Thesis.SoftplusGame.softEval_append
#print axioms Thesis.SoftplusGame.softEval_append
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {a b c : ℕ} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (hθ : 0<θ) (hp : pre.Nonnegative) (hs : suffix.Nonnegative) (x : Vec a) (plus minus : Strategy (pre.append suffix)) (hsp : SubgamePerfect θ (pre.append suffix) plus minus x (-x)), SubgamePerfect θ suffix (suffixStrategy pre suffix plus) (suffixStrategy pre suffix minus) (softEval θ pre x) (-(softEval θ pre x))) := @Thesis.SoftplusGame.spne_suffix
#check @Thesis.SoftplusGame.spne_suffix
#print axioms Thesis.SoftplusGame.spne_suffix
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {a b c : ℕ} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (hθ : 0<θ) (hp : pre.Nonnegative) (hs : suffix.Nonnegative) (x : Vec a) (plus minus : Strategy (pre.append suffix)) (hsp : SubgamePerfect θ (pre.append suffix) plus minus x (-x)) (plusDev minusDev : Strategy pre),  (policyValue θ pre plusDev (prefixStrategy pre suffix minus) x (-x)).1 ≤ softEval θ pre x ∧  (policyValue θ pre plusDev (prefixStrategy pre suffix minus) x (-x)).2 ≤ -softEval θ pre x ∧  policyValue θ pre (prefixStrategy pre suffix plus) (prefixStrategy pre suffix minus) x (-x)=(softEval θ pre x,-softEval θ pre x) ∧  softEval θ pre x ≤ (policyValue θ pre (prefixStrategy pre suffix plus) minusDev x (-x)).1 ∧  -softEval θ pre x ≤ (policyValue θ pre (prefixStrategy pre suffix plus) minusDev x (-x)).2) := @Thesis.SoftplusGame.spne_prefix_saddle
#check @Thesis.SoftplusGame.spne_prefix_saddle
#print axioms Thesis.SoftplusGame.spne_prefix_saddle
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {a b c : ℕ} (pre : Network a b) (suffix : Network b c) (θ : ℝ) (hθ : 0<θ) (hp : pre.Nonnegative) (hs : suffix.Nonnegative) (x : Vec a) (plus minus : Strategy (pre.append suffix)) (hsp : SubgamePerfect θ (pre.append suffix) plus minus x (-x)) (j : Fin c) (i : Fin b) (q : Bool),  fderiv ℝ (softEval θ suffix) (softEval θ pre x) (Pi.single i 1) j=(if q then (-1 : ℝ) else 1)*(profileOccupation suffix θ (suffixStrategy pre suffix plus) (suffixStrategy pre suffix minus) (softEval θ pre x) j i q false-profileOccupation suffix θ (suffixStrategy pre suffix plus) (suffixStrategy pre suffix minus) (softEval θ pre x) j i q true)) := @Thesis.SoftplusGame.spne_intermediate_gradient
#check @Thesis.SoftplusGame.spne_intermediate_gradient
#print axioms Thesis.SoftplusGame.spne_intermediate_gradient
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n k : ℕ} (r : Set.Icc (0 : ℝ) 1) (wp wn : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) (turn : Bool) (v : Bool → Vec n), (∑ target : Option (Fin n × Bool),mixedTransition r wp wn j turn target*target.elim 0 (fun t => v t.2 t.1))=r.val*∑ i,(wp j i/rowDiscount wp wn j*v turn i+wn j i/rowDiscount wp wn j*v (!turn) i)) := @Thesis.SoftplusGame.mixed_expected_value
#check @Thesis.SoftplusGame.mixed_expected_value
#print axioms Thesis.SoftplusGame.mixed_expected_value
end
section
open HiddenMonotonicity Thesis.Regularization Thesis.SoftplusBackward Thesis.ReLUNetGame Thesis.RoutingBackward Thesis.BackwardGames Matrix Thesis.SoftplusGame
open scoped BigOperators
example : (∀ {n k : ℕ} (θ : ℝ) (wp wn : Matrix (Fin k) (Fin n) ℝ) (bp bn : Vec k) (plus minus : Fin k → Set.Icc (0 : ℝ) 1) (v : PlayerValues n) (player turn : Bool) (j : Fin k), let r := if turn then minus j else plus j; playerStep θ wp wn bp bn plus minus v player turn j=r.val*(if player=turn then bp j else bn j)+(if player=turn then θ*Real.binEntropy r.val else 0)+rowDiscount wp wn j*∑ target : Option (Fin n × Bool),mixedTransition r wp wn j turn target*target.elim 0 (fun t => v player t.2 t.1)) := @Thesis.SoftplusGame.playerStep_transition
#check @Thesis.SoftplusGame.playerStep_transition
#print axioms Thesis.SoftplusGame.playerStep_transition
end
