# Routing equilibrium-to-backward bridge handover

Status: **unfinished WIP**, checkpointed immediately at the user's request to push the current state and restart on another server. No proof process is running. No root, configuration, TeX, or frozen source was edited. The two new drafts have been moved out of the production source tree into `reports/evidence/routing-bridge/draft/Thesis/`; neither was imported by a public root. Their source hashes, compile exit codes, and logs are recorded in `reports/evidence/routing-bridge/checkpoint.json` and adjacent files.

## Exact validated frontier

`RoutingHistory.lean` **compiles, exit 0**. It adds a full finite history interpreter on the EXISTING `Thesis.RoutingProfiles.Tree`:

- Terminal history: Unit.
- Activation history: a distinct stop history, or a positive/negative fair-oracle branch followed by its child history.
- Routing history: a dependent pair of the actual augmented routing action and that child's history. Thus ordinary, bias and outside actions remain distinct.
- `probability` consumes arbitrary actual plus/minus `Strategy` profiles. It uses the controlling player's pure activation choice, probability 1/2 at the sign oracle, and the controlling routing policy's normalized probabilities.
- `probability_nonnegative` and `probability_normalized` are proved for all profiles, not only equilibrium.
- `Observation` annotates actual tree states with scalar rewards; it does not replace the network or tree. `pathReturn` sums cumulative-discount-weighted rewards along a realized history. On entry to positive/negative routing states it multiplies by 2α/2β; other moves have multiplier one.
- `integral` is the actual finite expected path return, with derived activation/routing recurrences (`integral_activation`, `integral_routing`). No desired occupation recurrence is assumed.
- `rootObservation`, `root_return`, and `integral_root` prove that marking a subtree root gives exactly that mark, regardless of subsequent normalized histories. This is intended for genuine intermediate-layer visits in the full network tree.

This file has **not** passed independent exact-type/axiom contracts or semantic review. Its successful compile is focused development evidence only. No `sorry` or new axiom is present in the source. The build log has only harmless warnings.

`RoutingPolicyBridge.lean` **does not compile, exit 1**. It is a useful draft, not a validated theorem module. It currently specifies:

- `Step n = Option (Bool × Fin (n+2))`: activation stopping, oracle sign, and complete augmented route action.
- Actual microstep probability, source branch discount, and an explicit ordinary/cemetery target map.
- A literal finite-sum pushforward `collapsed`, meant to prove the actual source microstep has exactly `RoutingTransitions.transition` as its macro transition.
- `inputPositive/inputNegative` and `layerPositive/layerNegative`, obtained by projecting the canonical strategies of the actual `RoutingNetwork.route` trees.
- Route probability ratios and one-step equality with `RoutingTransitions.transition`, using the frozen `route_anchor_ordinary_probability`, `inputLayerGames_selected_gate`, and `layerGames_selected_gate`.

Do not infer the rest of the file was validated from errors occurring earlier. Read the complete preserved compile log.

## First failing checks and likely local fixes

The full error evidence is `reports/evidence/routing-bridge/RoutingPolicyBridge.log`.

1. `stepProbability_nonnegative`, around lines 39–41: indentation/layout after `cases ... <;>` leaves four goals and the subsequent `all_goals` parses as a command. Restructure the case proof with separate explicit branches.
2. `collapsed_normalized`: after swapping finite sums, the chosen `Finset.sum_ite_eq'` rewrite has the equality orientation wrong for `stepTarget q y = x`. Use the matching finite delta-sum lemma or first rewrite equality by symmetry.
3. `input_policy_probabilities`: ordinary `rw` cannot match the frozen route lemma after unfolding semireducible matrix/function types (`posContribution wp wn x j` and negative analogue). This project has similar transparency issues. Prefer explicitly instantiated `have h := route_anchor_ordinary_probability ...` followed by `change`/`simpa`, or `erw` where needed. Do not change hypotheses or enable unsafe reducibility.
4. Inspect later errors independently after fixing the earliest ones; the draft has not been retested beyond this first full compile.

`RoutingHistory` had the same dependent-type pitfalls during development. Explicit tree arguments were needed in finite-sum `change` statements; `Observation (.terminal _)` needed `(0 : ℝ)` rather than an inferred zero. The final copied draft includes those fixes.

## Original task and source facts

Parent request: close the explicit bridge between the actual `RoutingNetwork` / `RoutingProfiles` equilibrium game and `RoutingBackward`'s αβ discounted occupation/path recovery, with genuine probability/sign/discount preservation, ordinary input and intermediate states, nonnegative hidden activations, stopping at every activation log tie, empty-stream/outside absorption, ε≥0, and an ungated final affine readout. Use shared definitions; do not assume the final recurrence or equivalence.

Frozen dependencies read:

- `Thesis/RoutingProfiles.lean`: `Tree`, `Strategy`, actual all-profile auxiliary/reported semantics, `canonical`, and the proved SPNE.
- `Thesis/RoutingNetwork.lean`: `route`, `inputLayerGames`, `layerGames`, `propagate`, `networkGame`, actual canonical route probability lemma, forward-value and selected-gate proofs.
- `Thesis/RoutingTransitions.lean`: closed-form normalized macro transition, cemetery absorption, and ε=0 nonnegativity.
- `Thesis/RoutingBackward.lean`: `routingTrace`, independent `rgProbability`, `rgDiscount`, `rgOccupation`, and `thesis_alpha_beta_recovery`.
- `Thesis/BackwardGames.lean`: shared varying-width `Paths`, parity kernels, `rawWeight`, and path integral.
- `Thesis/AffineOutputBackward.lean`: ungated `affineOutputLRP`, `readoutOccupation`, and algebraic recovery.
- `HiddenMonotonicity/PrefixSources.lean`: actual `Network.append` and its forward composition law.

Source inspected: `arxive/playingTheNetworkBackward/main.tex`, routing recursion around 1610–1707 and recovery around 1949–2195. The fair sign oracle has probability 1/2, switches ownership on the negative branch, and entered routing-state discounts are 2α/2β. Bias and ε terminate. Empty streams select the outside action. Source activation ties stop. Fused input layers split the actual signed products xᵢWᵢⱼ; later layers require nonnegative activations, supplied by ReLU. Existing `networkGame` is a layered activated network; an ungated signed affine readout must not be silently modeled by another canonical activation gate.

No paper correction was proposed or made. Source recovery also includes residual addition and maxpool; the task's immediate missing bridge is the layered actual Network game. Any wider DAG extension must be scoped separately.

## Planned continuation, not completed proofs

1. Finish `RoutingPolicyBridge`; derive both ordinary and cemetery pushforwards of the actual microstep. Normalization should preserve stopped-history mass, including distinct bias/outside/empty-stream origins before collapsing.
2. Add scalar observation annotations on actual route/layer/network game trees. For a route, mark the root, outside and bias terminals zero, and ordinary child subtrees with their supplied observations. Prove its canonical integral is the sum of actual canonical ordinary-action probabilities times child integrals. Combine with the compiled activation integral to derive the layer redistribution law.
3. Recursively propagate these observations through existing `RoutingNetwork.propagate`. Input annotations mark the fused ordinary terminal i with the chosen input/owner indicator; bias/outside remain zero. Derive full-history ordinary endpoint occupation, then identify it with `rgOccupation` using the already proved local policy and sign identities.
4. Also define the ordinary-surviving microstep product directly from projected canonical policies and prove it equals `rgProbability`, with branch discounts equal to `rgDiscount`. The old `BackwardGames.Paths` encodes bottom-up intermediate indices/sign choices. If root owner is q, endpoint owner r and the current lower branch is b, the current parent owner is `Bool.xor r b`; the tail endpoint owner is the same. The parity bridge is `Bool.xor q r`. Base case is matching endpoint index and owner. Preserve source ownership convention: `RoutingProfiles.signed true` means positive, whereas `RoutingBackward` parity false means no sign flip.
5. For an intermediate actual layer, use the literal prefix game's root observations and `integral_root` to integrate away every lower full subtree. Compose the suffix with the existing prefix forest and prove full original-history visits equal the cut occupation. Merely restating an independent suffix recurrence would not close the requested bridge.
6. Treat an ungated affine readout as a forced fair oracle over two existing routing subgames, with no activation choice. Bridge to frozen `AffineOutputBackward.readoutOccupation` and its LRP theorem. Do not claim the existing activated `networkGame` already has this scope.
7. Author literal full-forall contracts before promotion, run exact module/universe/type/axiom driver plus a boundary consumer (negative weights, zero preactivation log tie, ε=0 empty stream, positive bias/ε leakage, zero fan-in, signed raw fused input, intermediate cut, negative ungated readout). Then independent review and parent root integration.

These are proposed proof routes. No conclusion in steps 2–7 has been proved by this WIP batch. If a proof only eliminates oracle states on ordinary surviving paths, label that limitation explicitly; do not present it as a full stopped-history law equivalence.

## Reproduce or resume

In a fresh checkout, stage the drafts back into their intended new source paths (neither path exists in the current production tree):

```
cp reports/evidence/routing-bridge/draft/Thesis/RoutingHistory.lean formalization/Thesis/RoutingHistory.lean
cp reports/evidence/routing-bridge/draft/Thesis/RoutingPolicyBridge.lean formalization/Thesis/RoutingPolicyBridge.lean
cd formalization
lake env lean -o .lake/build/lib/lean/Thesis/RoutingHistory.olean Thesis/RoutingHistory.lean
lake env lean -o .lake/build/lib/lean/Thesis/RoutingPolicyBridge.olean Thesis/RoutingPolicyBridge.lean
```

Compile sequentially (16 GB shared machine), never simultaneous full builds. The second command is expected to fail at the saved frontier. A local unused `RoutingHistory.olean` may still exist from the development compile; it is not source or production verification. No shared cache was deleted.

The five `formalization-*` skills and `math-exposition` skill under `skills/upstream-planar-features/` were read/applied. Keep exact source meaning and zero boundaries, no `sorry`, no new axioms, no `native_decide`, no frozen edits, and parent ownership of roots/config/TeX.

## Prior completed batches from this agent

Before this WIP, the thirteen `SoftplusCircuit*` leaves were frozen with twenty passing exact-type contracts; independent reviewer `attack_hidden` was actively reviewing them. The single `Thesis.ConditionedTrajectory` leaf was subsequently promoted byte-for-byte from foundations' saved draft, compiled, passed five exact module/universe/type/axiom contracts and a concrete zero-survival boundary consumer, and was frozen for independent review. See `reports/softplus-circuit-repairs.md`, `reports/conditioned-trajectory-repairs.md`, and their evidence directories. Do not alter those frozen files as part of resuming this routing draft.
