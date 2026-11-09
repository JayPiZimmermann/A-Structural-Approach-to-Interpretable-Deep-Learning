# Lean mathematics for the thesis

The project uses Lean 4 and mathlib v4.35.0, with dependencies pinned in
`lean-toolchain` and `lake-manifest.json`. This remains a partial formalization
of the thesis. The coverage map records the exact scope of each source theorem;
proved components do not silently count as an entire source theorem.

## Start with the definitions

There is one finite MLP parameter datatype, `HiddenMonotonicity.Network n m`.
A network is either an identity output or one affine layer followed by a smaller
network. `n` and `m` are the input and output widths; every intermediate width
may be different. A layer stores positive/negative weight and bias parts, whose
differences are the ordinary weights and biases.

- `net.eval x` is the ReLU backbone forward pass. `net.affineHeads` and
  `net.affineLogit` append the actual ungated signed affine readout, including
  its split biases. This preserves negative logits and covers zero hidden layers.
- `net.split p q` returns the two split heads, whose difference is
  `net.eval (p - q)`.
- `net.forwardWith activation x` evaluates those same parameters with another
  scalar activation. `net.decomposeWith pairActivation (p,q)` evaluates a
  neuron-local decomposition. A **valid pair activation** simply preserves the
  scalar output difference; induction proves recovery of the full network.
- `net.originalTrace x` records the active gates in an ordinary forward pass.
  `net.trace (p,q)` gets the same gates from split coordinates. A `MaskedTrace`
  is this fixed-gate view of the same network, not an independently chosen model.
- A `Row n` is a continuous linear map from an input perturbation vector to
  a scalar output change. It represents a row of a Jacobian. A `Sensitivity n`
  is a pair of such rows: one for each input stream. `unified` takes half their
  difference, as required by the balanced input lift `(x/2,-x/2)`.
- `stabilized` executes the complete backward recurrence, including every
  equal subtraction from the two sensitivity rows. Its equations are definitions
  of the algorithm, not hypotheses assumed in the closed-form theorem.
- A `QSource` contains the actual auxiliary function, its computed derivative,
  and its shift coefficient. The auxiliary keeps the original prefix, replaces
  one ReLU by a minimum, and uses a linear absolute-weight tail without biases.
  Every listed derivative is proved correct.

For residual and mixed-operation graphs, `Circuit` appends one operation to a
finite table of earlier node values. References preserve sharing. A graph cut
keeps the actual prefix table and evaluates the remaining suffix from that table;
the derivative and full-trajectory visit theorems refer to those same states.
The ordered max-pool adapter preserves the paper's smallest-operand-index ties.

Continuous linear maps carry the finite-dimensional derivatives without hiding
matrix transposes or requiring all layer widths to be equal. They are ordinary
linear functions with continuity recorded for mathlib's differentiation API.

## Convex and monotone DC lifts

`MonotoneDCLift` gives the generic scalar profile criterion: convex profiles with
slopes in a bounded nonnegative interval yield convex, monotone two-input heads.
`CurvatureMonotoneDCLift` constructs such profiles from integrable positive and
negative curvature. The `ExplicitGELU`, `ExplicitSwish`, `ExplicitSigmoidSmooth`,
`ExplicitSigmoidSoftplus`, and `ExplicitSoftplus` leaves prove actual closed forms.
`HiddenMonotonicity.SmoothDC.closed_form_activation_properties` aggregates the selected
ReLU/GELU/Swish/sigmoid/Softplus formulas; `closed_form_affine_network` and
`closed_form_affine_dc` compose them through arbitrary finite MLPs and an ungated
signed affine output. `ModernMonotoneDC` separately packages the integral-based
activation construction. The ReLU pair is exactly `(max(x,y), y)`.

The softmax construction is genuinely multivariate. For `H(z) = log(sum exp(z))`
and component `s_i(z)`, `ExplicitSoftmax` verifies the heads

```
F_i±(x,y) = (H(x-y) + sum(y) ± s_i(x-y))/2 - (log(d)-1/d)/2.
```

`SoftmaxLineCalculus` differentiates the actual exp/log expressions;
`SoftmaxProbability` proves the finite-probability curvature and derivative
bounds; `MultivariateMonotoneDCLift` supplies the composition criterion.
`SoftmaxDC.softmax_split_properties` concludes exactness, global convexity and
coordinatewise monotonicity, plus nonnegativity on the doubled nonnegative orthant.
Its index witnesses nonempty softmax support.

## Actual Transformer and recursive splitting algorithm

The namespace is `HiddenMonotonicity.TransformerDC`. The ordinary model and split
algorithm are defined independently and connected by a compiler theorem:

- `TransformerAffine` stores unrestricted signed weights and biases.
- `TransformerMask` stores a fixed nonempty permitted-key set for each row,
  represented by an injective index map. Causal and full masks fit this interface.
- `TransformerHead` computes signed Q/K/V projections, scaled dot products,
  actual row softmax, Value aggregation and an output projection. A finite list
  of projected heads represents multihead attention without hiding its products.
- `TransformerNorm` contains positive epsilon and unrestricted gain/bias. Its
  evaluator computes the mean and variance from the current input, including at
  inference time. It is not a frozen-statistic affine replacement for LayerNorm.
- `TransformerBlock` is a pre-LayerNorm attention/residual/MLP/residual block.
  `Transformer` stores an arbitrary finite list of blocks, positional bias,
  optional final LayerNorm and a signed affine readout. Zero block depth is allowed.
- `Expr.eval` evaluates the actual scalar operations. `Expr.splitEval` recursively
  replaces constants, signed scaling, addition, products, activations, softmax and
  LayerNorm with their explicit pairs. None of these constructors stores an
  assumed convexity or correctness certificate.
- `Transformer.syntax` compiles those same parameters into expressions, and
  `Transformer.eval_syntax` proves equality with the ordinary forward model.
  `Transformer.decompose` then runs the recursive pair evaluator on that syntax.

The multiplication pair in `PolarizedProductDC` is

```
(A-B)(C-D) = ((A+C)^2 + (B+D)^2)/2 - ((A+D)^2 + (B+C)^2)/2.
```

`LayerNormDCLift` proves the reciprocal-square-root lift using its affine tangent
extension below zero. `LayerNormDC` assembles the actual finite mean, centering,
variance, reciprocal, multiplication, gain and bias. `HiddenMonotonicity.TransformerDC.Regular`
records that both stream functions are convex and nonnegative and the pair is
monotone on the stated convex domain. Primitive composition and structural
induction prove `Expr.splitEval_exact` and `Expr.splitEval_regular`.

The main endpoints in `TransformerCorrectness.lean` are:

- `Transformer.dc_decomposition`: exact equality with every signed output logit
  for the ordinary same-parameter model, convexity of each component, monotonicity
  and nonnegativity on the nonnegative doubled-input orthant, for arbitrary depth.
- `Transformer.raw_dc_decomposition`: the positive/negative raw-input lift gives
  globally convex, nonnegative components whose difference is the model output.
  It does not assert raw-input monotonicity.

These sources compile. Completed leaf reviews include independent exact-type,
axiom and boundary checks; the assembly review and final combined production gate
are pending in this local revision; the last
completed full gate is `0f3cfb0ea660556c14da510e665281f07acc471d`. Consult
[the Lean handover](../HANDOVER_LEAN.md) for current integration status. Contracts
and receipts are under `../reports/evidence/dc-generalization/`,
`../reports/evidence/softmax-dc/` and `../reports/evidence/transformer-dc/`.

The theorem is an exact real-arithmetic construction. It does not prove floating-
point stability, attribution faithfulness, runtime or shared-DAG complexity of the
expression compiler. The separate post-LayerNorm numerical diagnostic has severe
cancellation in fifteen of twenty float64 cases. Fixed masks and positive epsilon
are genuine hypotheses; fully masked rows and stochastic inference are not silently
covered. The backward attention game and its conditional Value-routing semantics
remain separate mathematical objects.

## Main modules

| Module | Mathematical content |
|---|---|
| `HiddenMonotonicity/Network.lean` | Shared finite MLP, original and split evaluation, exact recovery and common-shift law |
| `HiddenMonotonicity/Decomposition.lean` | Same network with generic scalar/pair activations; full-network validity and mixing recovery |
| `HiddenMonotonicity/MonotoneDCLift.lean`, `CurvatureMonotoneDCLift.lean` | Nonsmooth profile criterion and absolute-curvature convex/monotone lifts |
| `HiddenMonotonicity/ClosedFormMonotoneDC.lean`, `ModernMonotoneDC.lean` | Actual closed-form and integral activation pairs, complete MLPs and signed affine readouts |
| `HiddenMonotonicity/ExplicitSoftmax.lean` and its calculus/probability leaves | Exact coupled softmax pair, global convexity and monotonicity |
| `HiddenMonotonicity/PolarizedProductDC.lean` | Convex polarization product and nonnegative-stream composition |
| `HiddenMonotonicity/LayerNormDCLift.lean`, `LayerNormDC.lean` | Reciprocal-root lift and actual finite input-dependent LayerNorm |
| `HiddenMonotonicity/TransformerPairCalculus.lean`, `TransformerExpr.lean` | Explicit recursive pair algorithm and structural exactness/regularity invariants |
| `HiddenMonotonicity/TransformerConvexInput.lean`, `TransformerExprProperties.lean` | Expanded-domain and globally convex raw-input corollaries |
| `HiddenMonotonicity/TransformerDefinition.lean`, `TransformerCorrectness.lean` | Actual masked multihead Transformer, compiler bridge and arbitrary-depth DC theorem |
| `HiddenMonotonicity/Convexity.lean` | Nonnegative split streams are monotone and Jensen convex |
| `HiddenMonotonicity/ConvexInput.lean` | Arbitrary convex input lifts, mixing-one recovery, and convex actual affine heads |
| `HiddenMonotonicity/Convolution.lean` | Indexed multi-channel kernel/stencil sums, exact sparse-matrix bridge, split properties and all four Jacobian blocks |
| `HiddenMonotonicity/SplitDAGSize.lean`, `MaxoutProductSize.lean` | Explicit shared positive graph construction, rank-two split and linear vertex-plus-arc bound under fixed rank/degree or expansion count |
| `HiddenMonotonicity/NetworkDerivative.lean` | Actual Frechet derivatives of the full split network |
| `HiddenMonotonicity/MaskedTrace.lean`, `OriginalTrace.lean` | Gate extraction, original/split Jacobian agreement, canonical absolute-weight products |
| `HiddenMonotonicity/StabilizedBackward.lean` | Full varying-width shifted algorithm, mass law, finite correction sum, half-shift specialization |
| `HiddenMonotonicity/QSources.lean` | Actual Q-function derivatives, closed formulas, and original-gradient reconstruction |
| `HiddenMonotonicity/Backward.lean`, `ClosedFormula.lean` | Explicit rectangular matrix pullbacks and ordered noncommuting finite sums |
| `HiddenMonotonicity/Chunks.lean` | Exact linear/residual/product/max-pooling algebra and strict max derivatives |
| `HiddenMonotonicity/Counterexamples.lean` | Actual vanishing head derivatives despite nonzero sensitivity mass |
| `Thesis/BackwardGames.lean` | Explicit sign-labelled stopping paths, discounts, normalized kernels, and actual MLP gradient recovery |
| `Thesis/RoutingBackward.lean` | Network-derived contribution masses, full alpha-beta recurrence, and discounted routing-path recovery |
| `Thesis/SoftplusBackward.lean` | Actual full Softplus-network derivative and discounted occupation recovery |
| `Thesis/Games.lean` | Finite path laws, dynamic programming, Hellinger overlap, per-pixel partition, Doob conditioning |
| `Thesis/Regularization.lean` | Softplus derivatives, binary entropy optimizer, finite Gibbs variational principle |
| `Thesis/GeneralRegularization.lean` | Compact optimizer existence, convex monotone Lipschitz conjugate activation, arbitrary chosen-pair validity and actual affine readout recovery |
| `Thesis/CPWLLattice.lean`, `SignedMaxReduction.lean` | Genuine finite-polyhedral CPWL cover to a max-affine difference and a signed sum of maxima of at most d+1 affine functions |
| `Thesis/ReLUCompiler.lean`, `CPWLReLUEquivalence.lean` | Actual shared-network realization and the literal ceil(log₂(d+1))+1 total-depth bound |
| `HiddenMonotonicity/ModernActivationCorollary.lean` | Actual GELU, Swish, Mish, tanh, sigmoid and softplus curvature constructions |
| `HiddenMonotonicity/DistributionalRegularity.lean` | Classical regularity derived from weak second derivatives, then full curvature minimality |
| `Thesis/RoutingNetwork.lean` | Actual network game, original log utilities for every profile, canonical SPNE and anchor forward values |
| `Thesis/StoppingRegions.lean`, `StoppingPaths.lean` | Fixed-region affine monotonicity, actual geometric parity paths and bias sources |
| `Thesis/StoppingCircuit.lean` | Shared-graph stopping/WTA recovery and local addition/maxpool derivative–occupation steps |
| `Thesis/StoppingDAGIntermediate.lean` | Full normalized shared-graph paths, bias payoffs, intermediate-state visits and actual stopping/ordinary derivative identities |
| `Thesis/StoppingOrderedPool.lean` | Source smallest-operand-index tie convention, exact pair/kernel forwarding, and source-to-DAG bridge |
| `Thesis/SoftplusLimits.lean` | Actual pair limit as positive temperature vanishes; distinct diagonal/tie limit |
| `Thesis/SoftplusTransitionPayoff.lean` and its imported game modules | Layered mixed-policy softplus SPNE, source player payoffs, zero rows, signed affine readouts, and actual intermediate gradient occupations |
| `Thesis/SoftplusCircuitUniqueness.lean`, `SoftplusCircuitVisits.lean`, `SoftplusCircuitPayoff.lean` | Annotated shared-Circuit softplus SPNE and player payoffs, normalized canonical paths, and input/intermediate discounted occupations; hard-pool derivatives require unique winning operands and equilibrium uniqueness requires no pools |
| `Thesis/ConditionedSurvival.lean` | Actual survival potentials, zero-support pruning and normalized conditioned path laws with positivity only at the initial state |
| `Thesis/ConditionedTrajectory.lean` | Actual full-law conditioned marginals, geometric-kernel/overlap/Hellinger composition, and complete prefix overlap monotonicity for fixed stochastic kernels on a common finite state space |
| `Thesis/AttentionReference.lean` | Extended reference-KL routing objective, exact optimizer including zero entries, and all-zero-total boundary |

## Assumptions and boundaries

The original derivative proofs use strict nonzero preactivations. The newer
`DifferentiableHeads` results prove actual affine-head derivatives at every point
where those heads are differentiable; they admit degenerate zero gates.
`AlmostEverywhere` proves the common full-measure differentiability statement,
and `PrefixSources` certifies every actual auxiliary Q derivative almost everywhere.
Selected backward quantities remain distinct from classical derivatives at
nondifferentiable points. Canonical split weights mean
`Wp = max W 0` and `Wn = max (-W) 0`, so `Wp+Wn = abs W`.

Shifted backward sensitivities are algorithmic quantities. They are not asserted
to be derivatives of a forward function with input-dependent re-centering.
Unshifted sensitivities and the derivatives of every auxiliary Q are genuine
Frechet derivatives. The difference of shifted unified head sensitivities is
also proved to be the derivative of the original target.

Probability kernels use nonnegative masses. Empty streams are explicitly completed
by an absorbing action, including at zero stabilizer. Ordinary path probabilities
are kept separate from discounted occupation measures. `RoutingNetwork` proves
the canonical global equilibrium with pure activation choices and stochastic
routing for the actual ReLU network, using the original log-space preferences.
Every activation log tie selects stopping. This equilibrium theorem and the older
alpha-beta path-recovery theorem use separate trajectory encodings in the public
root. A six-module routing-history extension has passed independent review but
remains unimported; see `../reports/routing-bridge-handover.md` for its exact
input/intermediate occupation and forced-readout scope and promotion steps. The unrestricted signed
affine readout and a global game for signed smooth activations are not included
in that routing equilibrium theorem.

`coverage_map.json` and `claim_inventory.json` identify remaining gaps, including
architectural extensions, geometry, equilibrium claims, and randomization
asymptotics. The Lean proofs do not certify Python implementations, floating-point
behavior, empirical tables, or the correctness of every prose claim.

## Build and audit

From this directory, with `elan` installed:

```sh
lake exe cache get
lake build All
python3 scripts/inventory.py
python3 scripts/verify.py
```

`scripts/verify.py` requires a committed clean closure, builds the complete
`All` root, checks the independently reviewed types in `verification.json`, and
enumerates every imported project theorem through Lean itself for its axiom audit.
It records commands, exit codes, exact source hashes, the commit and generated
Lean checks in `reports/verification/current`. Use `--diagnostic` during development;
that output is explicitly labelled as development evidence. The readable secondary
`Audit.lean` can still be regenerated with `python3 scripts/audit.py`.
The accepted foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, or custom axioms are used.

The local development checkout may reuse a mathlib cache through an ignored
`.lake/packages` symlink. A fresh checkout fetches the pinned dependencies normally;
the development symlink is not needed.

## Source links

`tex_links.json` maps source labels to declarations. The root script
`scripts/generate_lean_links.py` locates each declaration in a committed source
snapshot, checks its exact file contents, and generates permanent GitHub links
with real line numbers. `lean_links.json` records the commit and file hashes.
A **Lean variant** badge links a complete theorem under the stated formal
model's assumptions; **Lean components** links part of a broader statement.
See the corresponding coverage-map entry for the exact distinction.
