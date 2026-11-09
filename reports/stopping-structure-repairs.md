# Stopping structure repair handoff

Three new modules are frozen: Thesis.StoppingRegions, Thesis.StoppingPaths and
Thesis.StoppingCircuit. Their final individual Lean compilations exited 0. No
existing HM module, Thesis module, root import, metadata file or TeX file was
changed by this task. Public import/coverage integration and the committed clean
closure belong to the root integration gate.

## Completed finite-MLP source statements

`Thesis.StoppingStructure.stopping_region_nonnegative_affine` supplies the full
source `lem:stop_monotone` statement. `SameGates` recursively compares actual
original-forward gate indicators, and `gateRegion` is defined solely by that
condition. The theorem proves the actual stopping output equals a fixed affine
map on this set, its linear part is the existing `stoppingJac`, that linear part
is monotone, its bias constant is nonnegative for nonnegative split parameters,
and the actual stopping map is `MonotoneOn` the region. It does not assume the
conclusion, require a convex region, or pretend hard-gated stopping streams are
globally monotone or globally continuous.

`Thesis.StoppingStructure.stopping_preactivation_parity_paths` supplies both
source `lem:parity_path` and `ptnb:lem:parity-path` for arbitrary finite
varying-width prefixes. It applies to the actual `net.decomposeWith stopPair`
preactivations. The final affine edge is explicitly ungated, so its path product
contains exactly the intermediate ReLU gates. The input-only formula states the
source's zero-bias restriction explicitly.

`GeometricPaths` consists of ordinary neuron-index paths, without independent
sign-channel choices. `geometricWeight` multiplies actual absolute signed
weights and traversed gates. Its terminal Kronecker factor enforces the chosen
output endpoint. `geometricParity_negative_count` proves that the XOR sign is
exactly `decide (Odd (negativeEdgeCount ...))`, matching the literal count of
negative weights. Canonical sign-part hypotheses bridge these paths to the
existing occupation kernels. Zero-weight edges remain in the finite index set
but contribute zero; no positive-fan-in restriction is imposed.

`stopping_activation_parity_paths` proves the corresponding actual stopping
activation formula, including the top activation gate. The bias remark is
formalized separately and exactly: `biasSources` contains one gated layer-bias
pair propagated through all later stopping gates; `stopping_input_and_bias_sources`
proves its sum is the entire affine offset. `stopping_biased_parity_paths` combines
these explicit bias stubs with the parity-sorted geometric input paths for the
actual stopping activation, without assuming zero biases.

## Shared-graph extension completed

`Thesis.StoppingCircuit.stoppingCircuit` uses the existing `Circuit` and
`SignedExpr`; it does not introduce an unrelated network data model. Each newly
recorded node reads the same predecessor stream values on all outgoing branches.
All-node exact recovery and stream nonnegativity are proved for affine, addition,
maximum and multiplication expressions, including residual sharing.

Its maximum operation forwards both streams from one actual maximizing
argument using the existing `winnerPair`, with arguments reversed so ties choose
the right branch. The explicit `stoppingExpr_relu` bridge proves that
`maximum a (constant 0)` is exactly the thesis `stopPair`, including stopping at
zero. Unique-pool-winner claims are independent of this fixed tie choice. Nested
pools recurse through the actual stopping expression pass.

For addition, `addition_probability_law` proves the fair two-successor oracle
is normalized and nonnegative; its discount is 2.
`addition_derivative_occupation` identifies the actual local addition derivative
with that discounted oracle pullback. For max pooling, `winner_probability_law`
proves the selected deterministic successor law is normalized;
`winner_derivative_occupation` identifies the actual unique-winner WTA differential
with its unit-discount oracle pullback. No ordinary stopping-stream or pooling
derivative is asserted at ties.

## Exact remaining scope

The full arbitrary-DAG stopping-game trajectory/discounted-occupation interpreter
and the end-to-end all-node derivative–occupation theorem have **not** been
implemented in this batch. The completed graph forward semantics and local
addition/maxpool derivative–occupation steps must not be advertised as that
full theorem. Existing MLP stopping-game results and this batch's complete MLP
monotonicity/parity results remain distinct from this residual. Work stopped here
at the root's explicit instruction to prioritize the source-to-thesis omission
and reference audit.

No new claim is made about global hard-stopping differentiability, equilibrium
uniqueness at ties, product-node game semantics, or bias-stub discounted game
payoffs. The bias-stub theorem concerns exact forward decomposition.

## Contracts and reproducibility

`reports/stopping-structure-expected-types.json` contains fifteen independently
specified exact target types with full binders, universes, module names and
scope. They were written against the source obligations above, not obtained by
printing and blessing the elaborated implementation signatures.

The direct checker imports the three modules, opens each target's declared
namespaces/scopes/universes, and checks
`example : EXPECTED_TYPE := @DECLARATION`, then `#print axioms DECLARATION`.
Per-file source compilations used
`lake env lean -o .lake/build/lib/lean/Thesis/NAME.olean Thesis/NAME.lean`,
sequentially; no simultaneous full build was launched.

The final direct exact-type check exited 0 for all fifteen targets. Every
transitive axiom set was exactly `propext`, `Classical.choice`, `Quot.sound`.
No `sorryAx`, new axiom, `Lean.ofReduceBool`, or `native_decide` was used.
These are diagnostic local receipts; the public/committed gate remains separate.

Final handoff content hashes:

* `formalization/Thesis/StoppingRegions.lean`: `e07218302d293c65a4d62c9914809cf288cd0caaa2fcc964d9e205ee9efeca08`
* `formalization/Thesis/StoppingPaths.lean`: `64579e52bb9284daa4f37b9aa37e3a34bcccff746a5b9fe24079a60221116968`
* `formalization/Thesis/StoppingCircuit.lean`: `b04f52a90f2df24b7480456bb46575c35cc07af11fd37806c2f7dea9a0447696`
* `reports/stopping-structure-expected-types.json`: `80ba01d945f8ed871c61fa65dab17f51ca40da3d6d11c8454e2178e37afeca19`
