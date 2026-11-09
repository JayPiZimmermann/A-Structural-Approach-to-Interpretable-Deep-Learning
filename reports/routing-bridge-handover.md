# Routing equilibrium-to-backward bridge handover

Status, 9 November 2026: **six frozen draft modules passed independent review**.
They remain outside the production `All` import closure. This task changed no
production imports, manifest, coverage, TeX mappings, or public links. A clean
committed public gate is required before publication.

Current summary: [routing-bridge-resumption.json](routing-bridge-resumption.json).
Independent review: [adversarial-routing-bridge-review.json](adversarial-routing-bridge-review.json).
The earlier failing `RoutingPolicyBridge` checkpoint was repaired. Its original
`reports/evidence/routing-bridge/RoutingPolicyBridge.log` and `checkpoint.json`
remain unchanged as historical evidence; those failures are no longer the live
frontier.

## Checked modules

All six sources are under `reports/evidence/routing-bridge/draft/Thesis/`.

- `RoutingHistory`: complete histories of the existing `RoutingProfiles.Tree`,
  retaining activation stopping, fair-oracle outcomes and augmented route actions.
  Probabilities are nonnegative and normalized for arbitrary profiles. Discounted
  observation integrals and local recurrences are derived from finite history sums.
- `RoutingPolicyBridge`: actual canonical input/hidden-layer policies have the
  source contribution ratios. Their complete microstep pushforward equals
  `RoutingTransitions.transition`, including cemetery mass. The saved case-layout,
  delta-sum and semireducible-rewrite failures are fixed.
- `RoutingPolicyPaths`: products of actual canonical ordinary microsteps equal
  `rgProbability`; source branch multipliers equal `rgDiscount`. Root owner `q`
  and endpoint owner `r` have parity `Bool.xor q r`. These are ordinary-surviving
  products, distinguished from complete stopped histories.
- `RoutingHistorySteps`: summing actual full-history probability over first-step
  fibers gives the microstep probability, including for arbitrary profiles. The
  canonical input/hidden-layer first-target marginal is the source transition.
- `RoutingObservations`: full canonical-history endpoint occupation equals
  `rgOccupation`, yielding alpha-beta LRP. Intermediate marks observe actual
  prefix roots inside full original histories; `integral_root` integrates every
  lower prefix continuation. An explicit append-tree identity connects this to
  the complete game of the original composed network.
- `RoutingReadoutHistory`: an explicit forced fair oracle over two complete
  routing histories implements an ungated affine output. Half probabilities and
  `2α`/`2β` returns give normalization, forward recovery, occupation equality and
  affine-output LRP. Negative and zero logits remain ungated.

Key source-facing declarations are
`Thesis.RoutingObservations.network_alpha_beta_recovery`,
`Thesis.RoutingObservations.network_intermediateOccupation`, and
`Thesis.RoutingReadoutHistory.affine_output_layer_history_lrp`.
Inspect their full contracts before changing any mapping scope.

## Frozen source hashes

| Module | SHA-256 |
|---|---|
| `RoutingHistory` | `f87cca18086e1254232e33aae1f5549adaff4054e79dc2edd1843bf2a724c8aa` |
| `RoutingPolicyBridge` | `01bb9cc62ba9cd9a3cdef0652dea8820b23188979a096f6549e935cd7a5de3c7` |
| `RoutingPolicyPaths` | `0f6dcf0f73360bb6a68dd1b7747a67f9d939f36d2c960010ec57360dec54fb24` |
| `RoutingHistorySteps` | `ef008d61ffd18251fddad6951067c4fe020c18fa0dac021549617d64545423ac` |
| `RoutingObservations` | `802bfa0ade629ea63e8a7325e8eab3ff9417b5519439801eec0d7e4a92af494a` |
| `RoutingReadoutHistory` | `cf84415738fe05ab5c56568d8922b5237d4784034f11b429aab04eb83968bb1b` |

`reports/evidence/routing-bridge/review/source-sha256.json` also binds imported
production sources, the toolchain, exact checker and independent contracts.
The reviewer verified these hashes remained unchanged.

## Contracts and evidence

**The promotion manifest is the 20 targets in
`reports/evidence/routing-bridge/review/expected-types.json`.** They were manually
authored and independently checked for exact type, defining module, universe
arity and axioms. All six sources were freshly recompiled independently. The
complete imported-project-theorem audit checked **919 constants**, with only
`propext`, `Classical.choice`, and `Quot.sound`.

Producer checks contain **14** full-forall contracts: three in
`HistoryStepsChecks.lean`, six in `observations-expected-types.json`, and five in
`readout-check/expected-types.json`. Eleven overlap the independent 20; their
union contains **23 distinct declarations**. The producer-only exact targets are:

- `Thesis.RoutingHistorySteps.firstStep_probability`
- `Thesis.RoutingObservations.network_integral`
- `Thesis.RoutingObservations.networkOccupation_nonnegative`

Their producer exact checks passed. They were independently source-compiled and
included in the imported axiom audit, but were **not explicit targets of the
independent 20-contract suite**. Independently check their full contracts before
adding them as extra headline targets. There is no 28-contract producer set in
the retained evidence. The exact sets are recorded in the resumption JSON.

The independent Lean boundary consumer passed with an empty log. It exercises
actual intermediate root observation, the full first-history cemetery marginal,
and a negative ungated output with nonzero reversed-owner occupation. Producer
consumers additionally cover signed raw input with negative weight, activation
ties, zero fan-in, bias/outside separation, stabilizer leakage and empty streams
at zero stabilizer. The independent exact-rational experiment passed **168 cases
and 5,208 complete histories**; it is finite evidence, separate from Lean proofs.

Commands actually used, from `formalization/`, had this form for each module:

```sh
lake env bash -c 'export LEAN_PATH="$PWD/.lake/diagnostics/routing-review:$LEAN_PATH"; lean -R ../reports/evidence/routing-bridge/draft -o .lake/diagnostics/routing-review/Thesis/RoutingHistory.olean ../reports/evidence/routing-bridge/draft/Thesis/RoutingHistory.lean'
lake env bash -c 'export LEAN_PATH="$PWD/.lake/diagnostics/routing-review:$LEAN_PATH"; lean ../reports/evidence/routing-bridge/review/ExactTypes.lean'
lake env bash -c 'export LEAN_PATH="$PWD/.lake/diagnostics/routing-review:$LEAN_PATH"; lean ../reports/evidence/routing-bridge/review/Boundary.lean'
```

All final commands exited **0**. The six `review/*-source.log`/`.exit` files,
`review/exact-types.log`/`.exit`, and `review/boundary.log`/`.exit` retain the
results. `review/prepare.py` renders the manually authored contracts through the
existing repository checker; it does not infer expected statements from compiled
types. The generated `ExactTypes.lean` is retained. `review/evidence-sha256.json`
binds the artifacts.

Before rerunning, archive the existing review evidence. Bootstrap the pinned
Lean/mathlib and build production dependencies. Create an isolated diagnostic
`Thesis/` overlay with read-only symlinks to production `.olean` files, excluding
the six draft output names. Compile the drafts sequentially in the order above.
Set `LEAN_PATH` **inside** `lake env`; Lean selects a namespace directory before
looking for individual files, so a partial overlay without production links
fails. `-R` supplies the draft source root when writing objects outside the
production source tree. Initial root/overlay setup failures are preserved in
separate review logs.

Producer receipts are `history-steps-receipt.json`,
`observations-check/receipt.json`, and `readout-check/receipt.json`, all under
`reports/evidence/routing-bridge/`. They record the earlier producer stage; the
canonical independent report records the subsequent completed review.

## Scope to preserve

- The architecture is the shared **layered Network**. Arbitrary residual/maxpool
  routing DAG cases and varying-state-space embeddings remain outside this batch.
- Canonical backward equivalence is at `θ = 1`. Arbitrary-profile history
  normalization is separate from the existing SPNE theorem. No full
  off-equilibrium forced-readout game or new SPNE certificate is asserted.
- Ordinary surviving products, actual first-step marginals and full canonical
  history occupations are separate proved statements. There is no blanket whole
  stopped-history-law equivalence with a separately constructed macro process.
- Raw inputs may be signed; the first layer fuses actual signed products. Hidden
  layers require nonnegative activations, supplied by ReLU. Stabilizer `ε ≥ 0`
  includes empty streams. Every activation log tie selects stopping.
- Algebraic identities allow real `α, β`; nonnegative occupation requires
  `α, β ≥ 0`. Discounted occupations need not be probability measures.
- Readout backbone outputs must be nonnegative, automatic for a nonempty activated
  backbone despite signed raw input. A zero-depth backbone with negative outputs
  needs a separate fused readout construction. The final affine output itself
  may be negative or zero and is ungated.
- The original intermediate-cut corollary uses a nonempty activated prefix.
  Actual input occupation has its own signed-input theorem.

## Promotion instructions

1. Coordinate with the integrating agent after its current committed gate ends.
   Copy all six frozen files byte-for-byte into `formalization/Thesis/`.
2. Add these three imports to `formalization/Thesis.lean`; they reach all six:

   ```lean
   import Thesis.RoutingPolicyPaths
   import Thesis.RoutingHistorySteps
   import Thesis.RoutingReadoutHistory
   ```

3. Append exactly the independently reviewed **20** targets to
   `formalization/verification.json`. Update coverage and reviewed TeX mappings
   to the actual new history/backward declarations, preserving the scope above.
   Manual `review_id` mappings override automatic choices.
4. Commit the source closure and bound configuration. Archive current proof
   evidence, then run `python3 scripts/verify.py` from `formalization/` with HEAD
   and bound files fixed. The diagnostic review does not replace this clean gate.
5. After that gate passes, give the verified commit to the TeX task for link
   regeneration, PDF rebuilding and publication checks. This routing task
   performed no production promotion or publication.
