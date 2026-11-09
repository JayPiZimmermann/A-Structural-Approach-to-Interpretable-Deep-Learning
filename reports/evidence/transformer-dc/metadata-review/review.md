Current status: the primitive review below is historical. The later `assembly-review.md` and `transformer-assembly-receipt.json` certify source correspondence for actual LayerNorm and the complete stated pre-LayerNorm architecture; the old assembly deferral is resolved.

Independent metadata review of the six Softmax, polarized-product, and
reciprocal-square-root primitive modules, 2026-11-09.

The proposed mappings are faithful to the current statements. All six
source hashes match their final independent review receipts. Those receipts
record 38 independently authored selected contracts: 24 for the four Softmax
modules, six for the product module, and eight for the normalization
primitive. Their exact checks and boundary checks passed with only
`propext`, `Classical.choice`, and `Quot.sound`. This task inspected those
receipts and the actual source; it did not rerun builds or verification gates.

`coverage-proposal.json` contains four statement entries, and
`tex-links-proposal.json` contains their links plus five equation links.
Every proposed target belongs to the 38 reviewed contracts and every
proposed label currently exists in chapters 03 or 07. These files are
proposals only; no global metadata or TeX source was changed.

The main source distinctions are:

- `prop:multivariate_dc_lift` must receive **Lean components** coverage.
  The manuscript gives arbitrary vector coefficients and converse
  equivalences. The Lean helper proves sufficient conditions for a common
  scalar coefficient, with an optional normalization constant. It does
  not prove the general vector-coefficient or iff statement.
- `thm:softmax_dc_split` matches the actual normalized coupled Softmax
  pair. The proof derives the needed derivatives and curvature bounds;
  it assumes neither the desired convexity nor a surrogate denominator.
  It covers arbitrary finite nonempty index types, including singleton
  rows. The two formula contracts and origin values match the displayed
  normalizer exactly. Mask-specific wrappers and fully masked conventions
  are separate from this row primitive.
- `prop:convex_product_pair` matches the literal polarization formulas.
  Exactness, convexity, and nonnegativity hold even for signed arguments;
  monotonicity is correctly limited to the nonnegative orthant.
  Composition requires nonnegative incoming streams. The square pair is
  the direct specialization using the same operand twice.
- `prop:reciprocal_sqrt_pair` matches the actual tangent extension,
  coefficient, and two heads. Its convexity and monotonicity are global;
  nonnegative values are asserted on the quadrant. Recovery of the
  original reciprocal square root requires nonnegative represented
  variance and strictly positive epsilon. This proves a normalization
  primitive, not complete LayerNorm with centering, variance, learned
  scale, and bias.

No full Transformer badge is proposed. `deferred-claims.json` records the
architecture and full-LayerNorm labels that must wait for the architecture
team's reviewed contracts. It also leaves the general vector-lift equation
and literal Hessian/coordinate-partial displays unbadged, because their
nearest selected contracts use narrower or algebraically different forms.
The Softmax pair equation is marked **Lean components** because its two
literal formula equalities are separate selected declarations.

One metadata integration defect was found and reported: the first six
entries of `reports/softmax-dc-expected-types.json` initially omitted the
reviewed universe and notation metadata and used `Type*` instead of
`Type u`. The original reviewed leaf contracts contain `universes: [u]`
and `BigOperators`. The producer is repairing and rechecking the combined
file; only the corrected frozen aggregate should be imported into the
global verification manifest. This does not affect the reviewed source
semantics.

The TeX owner confirmed that the primitive labels and statements are
stable while the architecture section is being expanded. The current
blanket sentences saying that none of these ingredients has Lean coverage
should be narrowed when the primitive links are integrated. The full
architecture claim must retain its separate status. The owner was also
asked to make nonempty LayerNorm feature dimension explicit alongside the
displayed average.

The receipt in this directory records the reviewed source hashes,
contract sources, and evidence receipts. Public-root integration, the
combined exact-type gate, and any clean committed verification remain
with the integrating agent.
