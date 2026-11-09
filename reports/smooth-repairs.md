# Smooth analytic repair frontier

The current stable additions are `CurvatureMinimality.lean`, `ModernTanh.lean`,
and `ModernSoftplus.lean`. Each has passed its focused Lean compile.
`reports/smooth-expected-types.json` records ten manually authored complete type
contracts, including the unchanged `smooth_dc_split`, `canonical_tilt_minimality`,
`sigmoid_smooth_dc_split` and `softplus_smooth_dc_split` declarations. Their explicit
type/axiom checks are under `reports/evidence/smooth-repairs/`.

- `common_affine_of_minimal_curvature` proves that equality in the first a.e.
  minimal-curvature bound forces the same affine summand in both components.
  `curvature_minimality_locally_AC` assembles both lower bounds, common-affine
  uniqueness and least common tilt. These are genuine classical locally-AC
  statements. The source's distributional-to-local-AC implication is **not**
  assumed by a new definition or claimed to be proved.
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

Swish, exact Gaussian GELU, Mish, and the distributional regularity bridge remain
in progress. Their unverified drafts stay outside the production theorem tree.
The smooth decomposition applies globally to signed scalar activations; no
routing-game positivity restriction has been imposed on these results.

These are local diagnostic receipts. Root import/publication and clean committed
closure certification remain the root worker's responsibility.
