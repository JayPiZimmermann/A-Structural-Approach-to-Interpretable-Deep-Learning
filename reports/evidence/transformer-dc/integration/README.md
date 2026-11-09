# Completed Lean integration handoff

The scalar DC, softmax, primitive, and complete Transformer work is integrated
locally. Production sources and central metadata are frozen at the hashes in
`final-metadata-receipt.json`. No source commit, full gate, or push was performed
by the integration agent.

Current totals are **167 imported production modules, 490 independently reviewed
selected contracts, 216 source links, and 204 inventoried statements**. Relative
to the previous completed source checkpoint, this adds 28 modules, 120 contracts,
and 26 source links. Existing reviewed production leaves were not changed.

The complete Transformer endpoints are
`HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition` and
`HiddenMonotonicity.TransformerDC.Transformer.raw_dc_decomposition` in
`TransformerCorrectness.lean`. They refer to the actual independently defined
pre-LayerNorm forward evaluator: arbitrary finite block/head lists, fixed
nonempty injective masks, actual QK-softmax-AV attention, input-dependent
positive-epsilon LayerNorm, supported block-specific activations, residuals,
positional bias, optional final normalization, and signed affine outputs.
The pair algorithm is the actual structural recursion `Expr.splitEval` after
`Transformer.compile`; no decomposition certificate is supplied as input.

Expanded Transformer heads are convex, monotone, and nonnegative on the
nonnegative doubled-input orthant. Exact recovery holds even for arbitrary real
input-stream pairs. Composing with positive/negative raw-input parts gives
globally convex nonnegative heads; raw-input monotonicity is not claimed.
No floating-point stability, execution-time, expression-size, or all-possible-
Transformer-variants theorem is claimed.

Independent evidence includes:

- `../architecture/handoff.json`: seven assembly modules, source hashes, and
  36 selected assembly contracts.
- `../final-review/review.json`: eight final contracts, 920 imported theorem
  axiom audits, and 28 behavioral/boundary consumers.
- `../assembly-semantic/review.json`: independent source review and ten concrete
  consumers, including two-token attention, depth two, and negative logits.
- `../definition/review.json`: ten actual definition/compiler contracts and
  903 imported theorem audits.
- `../../softmax-dc/integration/receipt.json`: actual softmax construction and
  24 selected contracts. The generic six-contract universe metadata was repaired
  and rechecked using the repository exact driver before integration.

All integrated contract checks accept only `propext`, `Classical.choice`, and
`Quot.sound`. The central static check found every production source reachable,
every selected declaration in its claimed module, no duplicate contracts, and
every source link backed by a selected contract and an existing label. Badge
synchronization passed.

The parent owns the remaining promotion steps: make the local source commit,
run `scripts/generate_lean_links.py --revision <source-commit>` and its `--check`
mode, then run the sole serial complete verification gate. Pinned generated URLs
still point to the previous checkpoint until that step; no new committed
verification result is claimed by these local receipts.
