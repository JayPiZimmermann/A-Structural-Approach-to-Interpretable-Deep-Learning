# Shared-DAG stopping backward and occupation repair

This batch adds ten new leaves only. It leaves the frozen 93-module frontier, roots, mappings, source text, and publication metadata unchanged. All new declarations are in `Thesis.StoppingDAG`. The single import `Thesis.StoppingDAGIntermediate` includes this complete batch.

## Source-facing result

`intermediate_stopping_derivative_occupation` proves the complete source p/q/k formula in `ptnb:thm:deriv-occ` for any intermediate recorded node of the actual shared `HiddenMonotonicity.Circuit`. `intermediate_circuit_derivative_occupation` proves the ordinary scalar activation derivative formula, with arbitrary starting sign q. Their right-hand sides use **full discounted visits under the original graph trajectory law**, not only an input endpoint proxy.

The actual graph is `graft pre suffix`. A target node is the last recorded node of `pre`; `exists_graph_cut` proves that every internal node of every shared circuit has such a cut. The functions being differentiated are the actual downstream stopping/circuit evaluation functions at the **actual forward state** of `pre`. `graft_stopping` and `graft_eval` prove the actual prefix/suffix composition. The ordinary derivative is evaluated at `pre.eval (x.1-x.2)`, not an assumed or independently chosen activation vector. `circuit_hasFDerivAt_split` handles its genuine two-stream representation without assuming that the negative stream is zero.

`fullOccupation_graft_last` proves the central original-graph/cut bridge. Edges strictly decrease recorded node indices, so after a full trajectory crosses below the target node it cannot visit the target again. Full input-node visits are also identified with terminal occupation by `fullOccupation_input`. Thus input and arbitrary intermediate node cases are covered.

## Concrete finite interpreter and source alignment

`DAGPaths` is a finite inductive path type on the existing shared Circuit. A node step either bypasses a later recorded node, chooses an actual signed predecessor and a remaining finite path, or ends at a single cemetery. Impossible path constructors receive probability zero. There are no invented tails after cemetery termination. `pathProbability_normalized`, `pathProbability_nonnegative`, and `pathDiscount_nonnegative` prove the normalized finite law and nonnegative cumulative discounts.

`pathOutcome` tracks the actual input state and XOR sign changes. `occupation` is its discounted terminal indicator expectation. `visitWeight` recursively sums visits to an arbitrary graph state, multiplying all later visits by each traversed local discount; bypasses create no graph visit. `fullOccupation` is the finite probability-weighted sum of those cumulative discounted visits. Its first-step identity `fullOccupation_node` and the actual cut bridge are proved, not assumed.

`expressionKernel` is computed from the actual expression syntax and actual represented forward scores. `dagKernel` composes these nonnegative parity rows through all retained graph values. The actual chain rule produces `stoppingCircuit_hasFDerivAt`; an independent finite-path expansion produces `occupation_eq_kernel`. These meet in the backward identities. Neither definition takes the desired derivative or occupation identity as an invariant or hypothesis.

The primitive bridges are explicit:

- Existing `SignedExpr.affine w b` has local kernel `(max w 0, max (-w) 0)`, discount `sum |w|`, and immediate split bias reward `(max b 0,max (-b) 0)`.
- Addition has discount 2 and the push-forward of the existing fair 1/2,1/2 oracle. Repeated predecessors receive the sum of both probabilities.
- Maxpool selects the input with larger represented value, with a deterministic right winner at equality, and has discount 1. Binary nesting also handles a finite pool; it is not a claim of invariance under arbitrary changes of tie order.
- ReLU is the existing maximum(input,0) encoding; its selected kernel is the input edge if positive, otherwise zero, including stop at zero.
- Constant nodes and all zero-fan-in rows terminate in the cemetery with probability one. The forward interpreter retains their actual signed bias reward.

`expressionOffset` computes bias rewards recursively from expression syntax; it is not defined as a desired affine remainder. `stoppingExpr_affine` proves the selected affine identity. `pathPayoff` accumulates immediate bias rewards and actual input terminal rewards with the same discounts and probabilities. `expectedPayoff_eq_stoppingCircuit` proves that this complete normalized finite interpreter recovers the actual forward stopping streams.

Bias handling follows this paper's **stopping** convention: biases are immediate payoffs, not part of the weight-magnitude routing normalization. Cemetery absorption is genuine at zero fan-in. The separate bias-absorption convention used by routing games has not been substituted into this stopping model.

## Regularity and honest limits

Actual classical derivative theorems assume `CircuitRegular`: each recorded operation is regular at its actual forward state. At a maximum this means distinct represented scores and recursive regularity only in the selected subtree. Affine/addition/scaling nodes introduce no artificial strict-gate premise. This matches the source's open-cell, nonzero-ReLU, unique-pool-winner formulation and avoids imposing regularity on unused losing subtrees.

At ties, `intermediate_selected_occupation` proves the same p/q/k formula for the selected linear operator and original full trajectory law. It does **not** assert a classical derivative of individual stopping streams at discontinuities. No almost-everywhere or merely-head-differentiability extension is claimed here.

The graph theorem covers `Circuit.Additive` (affine, addition, scaling, maxima/ReLU), not multiplicative gates. Internal syntax of a compound expression is collapsed into its selected predecessor row; the full visit measure is on **recorded Circuit states**. The primitive affine/addition/maxpool bridges identify exactly the source structural states. The batch evaluates the source's concrete selected policy; it does not independently prove an extensive-form subgame-perfect equilibrium theorem over all alternative strategies. Public source mapping, independent promotion review, and a clean import-closure rebuild remain root integration work.

## Validation and exact contracts

All ten new leaf modules compiled sequentially with Lean 4.35 using the existing checked dependency frontier. No full concurrent lake build was run. The independent specification fragment is `reports/stopping-dag-expected-types.json`: 28 source-facing contracts, with full explicit forall binders, implicit dimension binders retained, no universe variables (all types are concrete Type 0), defining modules, scope, and evidence linkage. These expected types were written from the intended source claims; they were not copied from `#print` output.

For each contract an independent scratch checker imports its module, elaborates `example : EXPECTED_TYPE := @DECLARATION`, and runs `#print axioms DECLARATION`. Result: **28/28 exact-type checks passed, process exit 0; 28/28 axiom closures are exactly `propext`, `Classical.choice`, `Quot.sound`.** There is no `sorry`, `admit`, new `axiom`, or `native_decide` in the new batch. The remaining compiler output consists of unused-argument/tactic and deprecated-lemma warnings, not proof failures. This is a targeted local validation receipt, not a claimed clean-checkout publication receipt.

Freeze hashes (SHA-256):

| Module | SHA-256 |
|---|---|
| `Thesis.StoppingExpressionKernel` | `2f1e0f42b6977d03b2c4037b31da7affa3c2ce07acb50f07716174fd4ac5e1c0` |
| `Thesis.StoppingDAGDerivative` | `5c638b53f1d96e99e914166dbad8179008d479e7961a2dd9d24f3a02e5b16e79` |
| `Thesis.StoppingDAGPaths` | `532887e4e529e01dc8199fcc62901062f9272a9fcac042dac714bc279c56f413` |
| `Thesis.StoppingDAGOccupation` | `110516fa41533610e17b07e27612cb40732bda707987ed8d3511b89202b8795d` |
| `Thesis.StoppingDAGBackward` | `4cc29e1649949af0fe9b4cd6cf3deaffd7c7c9dd2e0f4fcaa7478f7d90570b38` |
| `Thesis.StoppingDAGPayoff` | `8cce1b058ae697465dafd5bff39b542b8182e0d99df6dd3b628aa64d719f3a25` |
| `Thesis.StoppingDAGPrimitives` | `b8950da5cd04b469f4aaf9c19e8173415db592fc03806a10a72f02219ded68f6` |
| `Thesis.StoppingDAGCuts` | `7941e816a2aa01b88a7d47f8e8aa4ff0504ab1de29bc8494781180e32518d169` |
| `Thesis.StoppingDAGVisits` | `609d4af4e9895dd09ba5b14610e11b5b23e621e4c463abacc4df299ccf0b4d88` |
| `Thesis.StoppingDAGIntermediate` | `9a14501731acee9fdd549bdf86c537a60fc44a3f41aa4500eb7fa414b15f1577` |

Contract manifest SHA-256: `9b5dec21b3fc28b5348b656bf6fe3d6efbd3dc84f8390ad705024f4d0fa960b7`.
