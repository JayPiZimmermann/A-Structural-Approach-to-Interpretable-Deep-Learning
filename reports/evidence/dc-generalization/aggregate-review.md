Independent source review of the new DC network construction, 2026-11-09.

No substantive mathematical or modelling defect was found in the reviewed
statements. The source snapshot is recorded in
`aggregate-review-source-sha256.txt`. The review covered
`ConvexMonotoneNetwork.lean`, `ConvexMonotoneReadout.lean`,
`ModernMonotoneDC.lean`, and `TwoInflectionDC.lean`, with the underlying
`Decomposition`, `Network`, `Convexity`, `MonotoneDCLift`, and
`CurvatureMonotoneDCLift` definitions inspected directly.

The final `ClosedFormMonotoneDC.lean` aggregate and all four independently
written expected contracts in `closed-form/contracts.json` were also reviewed.
Its datatype selects the intended actual formulas: ReLU gives `(max(x,y),y)`;
Gaussian GELU uses profiles `2(GELU+φ)` and `GELU+2φ` with width 2; Swish uses
`2 Softplus(1/β)` and its difference from Swish with width 2; sigmoid uses
`(Softplus(1)±sigmoid)/2` with width 1/2; and Softplus uses its log-sum-exp
lift and the identity second branch. These selections were checked against
the definitions in the four explicit activation leaves. In particular, the
sigmoid case selects the smooth root-free formula, not the separate
piecewise curvature-minimal formula.

The relevant scope checks are:

- `Network.Nonnegative` constrains split weight matrices only. Biases are
  unrestricted in the convexity, monotonicity, and recovery theorems.
  `Network.NonnegativeParameters` separately constrains the biases and is
  used only with nonnegative inputs to establish nonnegative stream values.
- `Network.decomposeWith` traverses the actual finite network and retains its
  matrices, biases, and varying widths. It does not replace the network by
  an unrelated existential representation. The base case is identity.
- `Network.affineDecomposeWith` appends a genuine affine output. Its defining
  expression contains no activation. Recovery is against the actual
  signed matrix difference and signed bias difference, so negative logits
  are preserved.
- Joint convexity and coordinatewise monotonicity hold on the whole split
  input space. The affine embedding `x ↦ (x,0)` preserves both properties,
  while the positive/negative-part embedding preserves convexity and exact
  recovery. The latter theorem correctly makes no raw-input monotonicity
  assertion.
- `modern_curvature_pair` obtains differentiability, local absolute
  continuity of the derivative, and integrable curvature from proved facts
  about each actual activation formula. None of those analytic obligations
  is hidden as a constructor assumption. Positive Swish scale and Softplus
  temperature remain explicit and necessary for the stated cases.
- `TwoInflectionDC` assumes slope conditions on the original activation,
  then derives the constructed profiles' convexity and slope bounds. Its
  threshold formulas and derivative joins include both endpoints. The
  zero-baseline claims are explicitly restricted to thresholds surrounding
  zero. This is a sufficient construction, not a claim that these are the
  only possible profiles.

One publication scope restriction should remain visible: the present
`Network.forwardWith` and `Network.decomposeWith` APIs use one shared scalar
activation throughout the hidden layers. They cover every requested
homogeneous activation case, but do not themselves formalize arbitrary
heterogeneous layer activations. Also, the explicit root-free profiles and
the normalized curvature-integral profiles must not be identified without
a separate equality theorem.

The final closed-form aggregate preserves the same network scope: arbitrary
finite widths, weights-only positivity, unrestricted affine biases, all
signed pair inputs, and an ungated signed affine output. Its ordinary-input
corollary uses `(x,0)` and correctly retains convexity, monotonicity, and exact
recovery without adding a nonnegative-value claim. The reviewed expected
contracts retain all quantified dimensions, actual activation choices,
matrix and bias parameters, and exact recovery against the same original
network; no clause was lost during aggregation. No additional direct
consumer was needed for this thin wrapper; the author's separate exact-type
driver is responsible for its kernel contract receipt.

`AggregateReviewBoundary.lean` is a handwritten independent consumer. It
instantiates the actual sigmoid, Gaussian GELU, positive-scale Swish, and
Softplus validity claims; computes a negative ungated affine readout;
checks a zero-width backbone; proves that the negative-part embedding is
not monotone in the original input; and checks values and derivatives at
both piecewise thresholds. The direct command is
`cd formalization && lake env lean ../reports/evidence/dc-generalization/AggregateReviewBoundary.lean`.
Its log and exit marker are `aggregate-review-boundary.log` and
`aggregate-review-boundary.exit`. Headline axiom checks are included in the
same consumer. The final consumer exited with status 0; all printed axiom
sets contain only `propext`, `Classical.choice`, and `Quot.sound`.

This is diagnostic source review and direct-consumer evidence. It does not
claim that the new modules have already passed public-root integration,
the final serial verification gate, or a clean committed reproduction.
