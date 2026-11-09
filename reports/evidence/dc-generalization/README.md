# General convex monotone DC decomposition: Lean handoff

The fifteen new production modules are compiled and frozen. Existing reviewed
production leaves were not changed. At the parent's explicit request, this team
integrated the public import root, selected verification contracts, source
coverage, and badge metadata. The parent owns the source commit, pinned URL
generation, and final serial complete build. No commit or push was performed.

`reports/dc-generalization-expected-types.json` aggregates 46 selected,
independently authored exact contracts. Every selected contract has passing
exact-type/module/universe/axiom evidence in its `contract_source` directory.
The file aggregates reviewed statements; it does not infer statements from Lean.

## Source-facing endpoints

| Purpose | Module | Declaration |
|---|---|---|
| Convexity iff for `C(x-y)+Ly` | `MonotoneDCLift` | `asymmetricLift_convex_iff` |
| Nonsmooth monotonicity iff | `MonotoneDCLift` | `asymmetricLift_monotone_iff_increments` |
| Differentiable slope iff | `MonotoneDCLift` | `asymmetricLift_monotone_iff` |
| ReLU via generic lift | `MonotoneDCLift` | `relu_asymmetric_split`, `asymmetricLift_relu` |
| Actual absolute-curvature construction | `CurvatureMonotoneDCLift` | `curvature_monotone_dc_split` |
| Arbitrary origin normalization | `CurvatureMonotoneDCLift` | `normalized_curvature_monotone_dc_split`, `normalizedCurvatureLiftPair_nonnegative` |
| Generic complete network | `ConvexMonotoneNetwork` | `Network.convex_monotone_decomposition` |
| Actual signed affine output | `ConvexMonotoneReadout` | `Network.affine_convex_monotone_decomposition` |
| Ordinary affine input embedding | `ConvexMonotoneReadout` | `Network.affine_dc_decomposition` |
| Signed positive/negative input embedding | `ConvexMonotoneReadout` | `Network.affine_signed_input_dc_decomposition` |
| Six actual modern activations, integral pair | `ModernMonotoneDC` | `modern_curvature_pair`, `modern_curvature_affine_network` |
| ReLU plus four actual closed-form pairs | `ClosedFormMonotoneDC` | `closed_form_activation_properties`, `closed_form_affine_network`, `closed_form_affine_dc` |

All unqualified scalar names in this table live in
`HiddenMonotonicity.SmoothDC`; generic network names live in
`HiddenMonotonicity`.

## Verified explicit profiles

Write `z=x-y`, `F1=P(z)+Ly`, `F2=Q(z)+Ly`.

| Activation | P(z) | Q(z) | L |
|---|---|---|---|
| ReLU | max(z,0) | 0 | 1 |
| Exact Gaussian GELU | 2(z Φ(z)+φ(z)) | z Φ(z)+2φ(z) | 2 |
| Swish β>0 | (2/β) log(1+exp(βz)) | P(z)-z sigmoid(βz) | 2 |
| Sigmoid | (softplus₁(z)+sigmoid(z))/2 | (softplus₁(z)-sigmoid(z))/2 | 1/2 |
| Softplus θ>0 | θ log(1+exp(z/θ)) | 0 | 1 |

The Softplus pair is additionally proved equal to
`(θ log(exp(x/θ)+exp(y/θ)),y)`. The sigmoid pair is also proved smooth and
given in explicit exp/log form. The ReLU pair is literally `(max(x,y),y)`.

Alternative certified modules are retained: `ExplicitSigmoidSoftplus` proves
the canonical piecewise sigmoid profile of width 1/4; `TwoInflectionDC` proves
the generic central-convex/tail-concave piecewise construction;
`GELUInflectionBounds`, `SwishThreshold`, and `SwishSlopeBounds` establish
the corresponding exact analytic threshold facts. These alternatives are not
silently identified with the integral-defined profiles.

## Scope and verification

- Global convexity and coordinatewise monotonicity hold on the full pair-input
  space. Nonnegative values are asserted only for nonnegative inputs, with
  nonnegative split biases where network propagation needs them.
- The network API uses one scalar activation throughout hidden layers and a
  genuine ungated final signed affine readout. It includes zero finite widths.
- The ordinary embedding `(x,0)` preserves convexity and monotonicity but does
  not force nonnegative streams. The embedding `(x⁺,x⁻)` preserves convexity
  and provides nonnegative input streams; no raw-input monotonicity is claimed.
- The generic curvature construction integrates its cumulative curvature from
  the finite origin. A weighted integral starting at minus infinity would
  require an additional first-moment convergence hypothesis.
- Necessity iff results concern the specified `C(x-y)+Ly` construction. No
  general global necessity theorem for arbitrary two-dimensional convex heads
  is claimed as Lean-verified here.

The individual directories contain source hashes, direct/module build logs,
exact expected-type drivers, independent boundary consumers, and permitted-axiom
checks. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Aggregate
receipts are `modern/receipt-final.json` (564 imported project theorems) and
`closed-form/receipt-final.json` (585 imported project theorems). These are local
diagnostic receipts; the integrated production closure still needs the parent's
final complete build and audit.

Activation integration is recorded in `integration-receipt.json`: 154 modules
in the current public closure, 416 selected contracts, and 202 source-link
mappings. The 15 new activation leaves and 46 selected contracts are included.
Badge synchronization passed. The inventory contained 203 statements at the
handoff snapshot because the independent Transformer extension had begun
landing. Its six new Lean leaves were intentionally not imported or described
as verified by this activation integration; their later owner must integrate
them after their own checks.

The subsequent softmax and full Transformer integration is now complete. Its
current 167-module, 490-contract, 216-link handoff supersedes those intermediate
pending-integration counts; see
`reports/evidence/transformer-dc/integration/final-metadata-receipt.json` and
the adjacent `README.md`.
