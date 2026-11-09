# Smooth analytic repair frontier

The current stable additions are `CurvatureMinimality.lean`, `ModernTanh.lean`,
`ModernSoftplus.lean`, `ModernActivationBounds.lean`, `ModernGELU.lean`,
`ModernSwish.lean`, `ModernMish.lean`, `ModernActivations.lean`,
`ModernActivationCorollary.lean` and `DistributionalRegularity.lean`. Each has passed its focused Lean compile.
`reports/smooth-expected-types.json` records seventeen manually authored complete type
contracts, including the unchanged `smooth_dc_split`, `canonical_tilt_minimality`,
`sigmoid_smooth_dc_split` and `softplus_smooth_dc_split` declarations. Their explicit
type/axiom checks are under `reports/evidence/smooth-repairs/`.

- `common_affine_of_minimal_curvature` proves that equality in the first a.e.
  minimal-curvature bound forces the same affine summand in both components.
  `curvature_minimality_locally_AC` assembles both lower bounds, common-affine
  uniqueness and least common tilt. These are genuine classical locally-AC
  statements. The separate `DistributionalRegularity` bridge below now derives
  these hypotheses from the source distributional assumption.
- `tanh_smooth_dc_split` proves global curvature integrability and local AC for
  the actual library `Real.tanh`, then constructs convex monotone canonical
  components with the exact valid-pair identity and nonnegative pair outputs.
  The bridge `tanh_eq_scaled_sigmoid` is proved algebraically, rather than
  defining tanh by a convenient stand-in. `tanh_curvature_sech` proves the exact
  displayed second derivative; `tanh_curvature_support` proves both half-line
  curvature-support clauses, including the boundary at zero.
- `softplus_degenerate_split` proves the previously omitted source clauses:
  negative curvature is zero, the negative canonical component is zero, the
  positive canonical component equals softplus itself, and softplus is convex.
  Its nonnegative initial value supplies preservation of nonnegative split pairs.

- `modern_activations_complete` combines all six actual activation formulas, with global
  differentiability, locally absolutely continuous derivative, integrable curvature,
  nonnegative initial value, the entire smooth theorem and nonnegative split-pair
  preservation. Its datatype contains only formula choices and positive parameters.
- Exact Gaussian GELU uses the normalized library standard Gaussian density and
  its actual cumulative integral, rather than a tanh approximation. Its curvature
  formula and exact sign intervals at `sqrt 2` are proved. Global integrability is
  proved from the integrability of a Gaussian and its quadratic weighted moment.
- Swish at every positive scale has its exact curvature formula, a positive
  neighborhood of zero and negative curvature in both tails. Integrability follows
  from exponential domination of sigmoid derivatives and the weighted exponential.
  The theorem does not assert a unique positive-curvature transition radius.
- Mish is the literal `x * tanh (log (1 + exp x))`. The gate derivative is bounded
  by `4 * exp (-abs x)` and its next derivative by three times its first derivative;
  these bounds prove global curvature integrability without an integrability premise.

- `HasSecondDistributionalDerivative f q` means local integrability of `f` and
  `q` and the actual identity `integral f * φ'' = integral q * φ` for every smooth
  compactly supported test function `φ`. It contains no differentiability,
  antiderivative representation or local absolute-continuity assumptions.
- `affine_of_distributional_second_zero` proves that a continuous function with
  zero weak second derivative is affine. The proof convolves with normalized
  compactly supported smooth bumps, proves the resulting classical second
  derivative is zero, and passes affine identities through the approximate-identity
  limit. It does not assume the desired affine representation.
- `localPrimitive_twice_distributional` proves that two actual interval integrals
  of an arbitrary locally integrable `q` realize its weak second derivative.
  Two integrations by parts justify the test identity; supports of test functions
  and derivatives justify passing between interval and whole-line integrals.
- `distributional_second_derivative_regular` subtracts this twice-integrated
  primitive and applies the preceding zero-curvature result. It derives actual
  differentiability, local AC of the derivative, a.e. classical-curvature equality
  with `q`, and an explicit primitive-plus-affine representation.
- `curvature_minimality_distributional` is the complete source proposition.
  Convexity supplies continuity of the components; their weak curvature densities
  supply all needed regularity. The conclusion includes both minimal-curvature
  bounds, uniqueness up to the **same** affine summand, and the minimum common
  monotone tilt. Neither component differentiability nor local AC is assumed.

No source correction was needed for FOUND-06 or FOUND-07. The new standalone
headlines are `HiddenMonotonicity.SmoothDC.curvature_minimality_distributional`
and `HiddenMonotonicity.SmoothDC.modern_activations_complete`.
The smooth decomposition applies globally to signed scalar activations; no
routing-game positivity restriction has been imposed on these results.

These are local diagnostic receipts. Root import/publication and clean committed
closure certification remain the root worker's responsibility.


## Reproduction and scope review

Each new production module was compiled sequentially with the pinned project
`lake env lean -o .lake/build/lib/lean/HiddenMonotonicity/<Module>.olean
HiddenMonotonicity/<Module>.lean`. The exact public contracts are independently
recorded in `reports/smooth-expected-types.json`, including complete binders,
defining modules, scope and review evidence. `ExpectedTypeChecks.lean` checks each
contract by a typed `example := @declaration` and prints its kernel axioms.

The final receipts are under `reports/evidence/smooth-repairs/`: production
compile logs and zero exit markers, `expected-types.log`, `expected-types.exit`,
and `completed-frontier.json` with source/contract/evidence hashes. All seventeen
public declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, custom axiom or `native_decide` was added. These focused checks do not
substitute for root's whole-import/clean-closure gate.
