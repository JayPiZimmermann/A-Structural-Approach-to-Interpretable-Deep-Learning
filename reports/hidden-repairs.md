# Hidden-monotonicity repair review

All eight new modules AffineHeads, AffineChunk, MaxPool, PoolingCircuit,
DifferentiableHeads, AlmostEverywhere, PrefixSources and DifferentiableBackward
have passed targeted Lean 4.35 source compilation. All 20 independently specified
headline types passed a direct exact-type and transitive-axiom check. Exact-type, axiom, public-import,
and clean-closure receipts are the root integration gate's responsibility;
these local compiles are diagnostic receipts, not a clean publication claim.

The independently specified expected types in hidden-expected-types.json were
written against the mathematical obligations below. They quantify all dimensions,
parameters, hypotheses, policies and universes explicitly. They are not generated
from #print output or weakened in response to elaboration failures.

## Repaired meanings

* HM-02: affineHeads defines both actual ungated readout functions, including
  split biases, and affineLogit defines their matching signed output. Recovery,
  actual pair-input and balanced-input derivatives, actual plain Q formulas,
  both shifted partial invariants, and the literal canonical absolute-readout
  mass are proved. coefficientRow_sign_sum and coefficientRow_sign_difference
  bridge canonical coefficient parts to the original and absolute rows. No
  terminal ReLU, mask, or minimum/Q source has been added to this readout.
* HM-04: linear_chunk_properties bundles biased ungated affine recovery,
  nonnegative outputs under nonnegative parameters/inputs, coordinate monotonicity,
  exact affine interpolation, and ConvexOn for each coordinate of both actual
  streams. Bias nonnegativity is required for output nonnegativity, not for the
  separately proved affine/convex conclusions. It does not substitute ReLU
  recovery for affine recovery.
* HM-06: maxpool_properties treats the exact finite nonempty sup/erase-sum
  functions from the source and proves recovery, nonnegative output, monotonicity
  and ConvexOn for both streams.
* HM-05: PoolWinner is an actual maximizing-index predicate; poolWinner_exists
  proves existence; winnerPool forwards both streams at its chosen certified
  maximizer; winnerPool_recovery concludes equality to the finite pool maximum.
  PoolingCircuit extends the existing Circuit interpreter with convex or actual
  shared-winner maximum-node rules and independently chosen per-node recentering.
  Nested maximum trees inside a pool node recursively forward the winning
  leaf argument pair. All-node recovery and nonnegativity are proved. split_policy_convex_eq bridges
  its convex fixed-center special case to the original interpreter. No shape
  guarantee is asserted for input-dependent winner choices or recentering.
* HM-01: DifferentiableHeads proves a global supporting-affine-map inequality
  for every nonnegative split network, including every tied/identically-zero
  gate. Fermat's theorem identifies a touching support with the actual derivative
  at each head differentiability point. The lifted-head theorem assumes only
  differentiability of that actual balanced-input head, not of each internal
  gate or the full pair-input head. Both actual affine-logit reconstruction and
  the two shifted partial invariants then hold wherever both lifted heads are
  differentiable. Nonnegative readout rows are essential here; canonical rows
  discharge the hypotheses by coefficientRow_monotone. Canonical backbone
  weights discharge Network.Nonnegative via canonical_nonnegative.

## Almost-everywhere completion

AlmostEverywhere proves actual global Lipschitz estimates and applies mathlib's
Rademacher theorem to the actual balanced-input heads. The actual head gradients
and both partial invariants hold almost everywhere; the latter quantify all
backward shifts after one common full-measure set.

PrefixSources then proves the stronger individual-Q derivative result. It uses
Network.append on the same network data, proves the original selected Jacobian
is an actual derivative almost everywhere, and differentiates each minimum as
preactivation minus the next ReLU prefix. The induction appends one layer to the
prefix and always applies Rademacher in the original input space. It does not
assume that activation pushforward measures avoid kink hyperplanes. Thus all
finitely many Q functions have their computed actual derivatives almost
everywhere even when some preactivation is identically zero. Canonical sign
parts connect the generalized common-mode sources with literal absolute tails.

DifferentiableBackward packages affine_Q_closed_form_ae: all actual vector Q
derivatives, the actual affine-logit derivative, and both shifted finite-sum
formulas on a full-measure set. affine_plain_Q_gradients_ae additionally packages
the actual ordinary derivatives of both affine heads and all actual Q sources
on one full-measure set. affine_Q_row_formulas is the selected-row identity at
every input; affine_plain_formulas_of_differentiable turns it into actual head
derivatives at every common head differentiability point.

## Pointwise scope distinction

The old Strict-based theorems also certify every individual vector Q-source
Jacobian as an ordinary derivative, and PrefixSources now supplies that same
certificate almost everywhere without Strict. The new differentiable-head theorem proves
actual final-head derivatives and backward identities without asserting that
all internal or unused Q functions are differentiable at that same point.
Differentiability of a final head alone need not imply differentiability of an
unused auxiliary Q function (a zero readout can discard a kink). This distinction
must remain explicit in source links. Algebraic selected-row formulas can hold
without each selected row being an ordinary derivative at the point.

HM-03, HM-07 and HM-08 are manuscript/metadata convention corrections assigned
to the root, not proof changes in these modules. Existing opposite tie convention
is retained: strict positivity chooses the active gate, zero selects inactive.
At a differentiable head the support argument proves that this choice gives
the actual derivative, even though a local ReLU derivative need not exist.

## Local verification receipts

* Each of the eight modules was compiled sequentially with
  `lake env lean -o .lake/build/lib/lean/HiddenMonotonicity/NAME.olean HiddenMonotonicity/NAME.lean`.
  Every final exit code was 0. There was no concurrent full build.
* The 20 types in hidden-expected-types.json were checked as
  `example : EXPECTED_TYPE := @DECLARATION` after importing their defining
  modules, and each declaration was subjected to `#print axioms` in the same
  Lean invocation. Exit code 0; all 20 transitive axiom sets were exactly
  `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, new axiom,
  `Lean.ofReduceBool`, or `native_decide` was used.
* Boundary checks passed with exit code 0: the audit example
  `winnerPair (10,9) (2,0) = (2,0)` forwards the real winning stream pair;
  the canonical all-zero one-layer network fails Strict at every input but
  satisfies the new actual symmetric-head derivative theorem at every input.
* The full public-root build, manifest import integration, and committed clean
  closure are intentionally left to the root owner's integration gate.

The exact-type driver is reproducible from the manifest: import the unique
`module` values, then for each target open its listed namespaces/scopes and
universes and check `example : expected_type := @declaration`, followed by
`#print axioms declaration`. These checks did not change the expected types.

The degenerate-gate boundary check was:

```lean
import HiddenMonotonicity.DifferentiableBackward
import HiddenMonotonicity.PoolingCircuit
open HiddenMonotonicity

example : winnerPair (10,9) (2,0) = (2,0) := by norm_num [winnerPair]

noncomputable def auditZero : Network 1 1 := .layer 0 0 0 0 (.output 1)
example (x : Vec 1) : ¬auditZero.Strict x ∧
    HasFDerivAt (fun y => (auditZero.affineHeads (ContinuousLinearMap.proj 0) 0 0 0
      (balancedLift 1 y)).1)
      (unified ((auditZero.originalTrace x).run (fun _ => 0)
        (affineReadoutSeed (ContinuousLinearMap.proj 0) 0 0 true))) x := by
  refine ⟨by simp [auditZero, Network.Strict, affineLayer, matrixCLM], ?_⟩
  apply auditZero.affine_symmetric_derivative_of_differentiable
    (by simp [auditZero, Network.Nonnegative]) x (ContinuousLinearMap.proj 0) 0
    (fun _ _ h => h 0) (fun _ _ _ => le_rfl) 0 0 true
  have he : (fun y => (auditZero.affineHeads (ContinuousLinearMap.proj 0) 0 0 0
      (balancedLift 1 y)).1) = fun _ => (0 : ℝ) := by
    funext y
    simp [auditZero, Network.affineHeads, Network.split]
  change DifferentiableAt ℝ _ x
  simp only [ite_true, he]
  exact differentiableAt_const 0
```

Final source/content SHA-256 at handoff:

* `formalization/HiddenMonotonicity/AffineHeads.lean`: `a546cbee9282f9c4260c6169b2e82665ed7e27b9fc41e28b166e30d119cf52f5`
* `formalization/HiddenMonotonicity/AffineChunk.lean`: `bf06fc275ec08ecaa09a6482ef641511366770cb30033816216e932f0f94e382`
* `formalization/HiddenMonotonicity/MaxPool.lean`: `e040609d7e4cdae7e22d4b796be14773ece1b8c5fd935e88f6b053c30ecc5f7c`
* `formalization/HiddenMonotonicity/PoolingCircuit.lean`: `46586f00d5bc55cb8827628a0bffff36fde9356021c3485b704b9d14cc573b72`
* `formalization/HiddenMonotonicity/DifferentiableHeads.lean`: `27179d5aaf2ffabe643cb6cb5f3921d6936efa493df631b8a6dd6de6db5f2a99`
* `formalization/HiddenMonotonicity/AlmostEverywhere.lean`: `43613c8c322c22a7f58261dabd0491f09cc9492df7c9e41c24a7708e8ee53731`
* `formalization/HiddenMonotonicity/PrefixSources.lean`: `e40f1ff926c17137fca7545a311613b6baaaff176b845ab5902278bef7a5762a`
* `formalization/HiddenMonotonicity/DifferentiableBackward.lean`: `0514e365c3a330d84281cd008a079788d683fc88984cc3cf5500f907be1f7438`
* `reports/hidden-expected-types.json`: `49e27210847a31e4a932f84d9025101495dd84cc3d438a6a545d56797b9463bf`
