# Softplus game on the existing shared Circuit

Status: frozen for independent review. All thirteen production leaves compiled individually; all twenty direct exact-type checks passed. Every headline axiom closure is exactly `propext`, `Classical.choice`, `Quot.sound`. Independent publication review remains pending. This batch does not modify any previously frozen module, root, verification configuration, or TeX source.

Source-facing scope: PTNB `ptnb:thm:softplus-forward` and `ptnb:thm:softplus-gradient`, including source affine/ReLU operator syntax, residual/addition nodes, nonempty finite max-pooling, ungated signed affine readouts, and arbitrary intermediate graph states. These are ordinary softplus-network derivatives; the two decomposition components themselves are not falsely assigned the ordinary-network Jacobian.

## Shared model and actual game

`NodeSpec` certifies a basic operator's existing `SignedExpr` syntax. `Plan c` annotates the existing `Circuit c`; it is not a replacement network datatype. An activation certificate has syntax `maximum (affine w b) (constant 0)`. A hard pool certificate has the previously reviewed `orderedInputPool` syntax. Consequently a pool that happens to contain zero remains hard unless it was explicitly annotated as an activation. `graphWith_relu` proves the hard interpretation is exactly `Circuit.eval`, retaining all earlier graph nodes, residual references, and fanout.

`graphSoft` smooths precisely the annotated activation nodes. `graphSplit` uses the source soft stopping split there; affine/addition/pool nodes use the existing stopping decomposition. `graphSplit_recovery` establishes equality to the actual ordinary forward graph for every retained node.

Every activation policy is an arbitrary probability in `[0,1]`. Every pool policy is an arbitrary normalized finite distribution (reusing only `RoutingExtended.Policy` and `pure`, not that routing game's logarithmic utility). Affine and addition nodes have no player decision. `nodePlayer` and `playerValue` separately retain both players' payoffs at both ownership states: actual split biases, signed predecessor routing, continuation-scaled affine values, entropy credited only to the controller, and no pool entropy. `playerValue_advantage` proves for every complete profile that this actual player payoff difference equals the signed game used in the saddle proof.

`graph_saddle` quantifies over arbitrary complete profiles and proves both signed-coordinate bounds at every retained state. `SubgamePerfect` checks each actual node's local optimality at the profile's own evaluated predecessor subgames, not at an assumed invariant. `canonical_spne` proves existence. `subgamePerfect_iff` proves exact complete-policy uniqueness when `NoPools` holds, including zero fan-in, zero preactivation, residual addition, and ungated signed affine outputs. No uniqueness is asserted at tied hard pools.

`playerValue_canonical` proves all four source player/owner coordinates equal the actual split. `softplus_forward_spne` bundles SPNE existence, all four payoff coordinates, and ordinary forward recovery. Source hard-pool ties use the previously reviewed earliest original operand index, with no change to the frozen generic right-tie binary kernel.

## Full stochastic backward interpretation

`nodeWeights` uses the affine row before smoothing (or the actual addition/pool row). `nodeDiscount` is its structural positive-plus-negative fan-in: in particular sigmoid factors are **not** absorbed into the source discount. `nodeProbability` contains the sigmoid continuation probability, the source signed predecessor law, and all stop/cemetery probability. Its normalization/nonnegativity and `node_discount_recovery` include zero fan-in.

`nodePlayer_transition` connects that exact canonical transition law with the source player payoff equation, including bias and entropy. `pathProbability` is a complete finite law on the existing `StoppingDAG.DAGPaths c`, with a separate cemetery trajectory rather than fake lower tails. The proof establishes total mass one from every starting graph state. `pathDiscount` is the product of structural discounts. `occupation` is defined as the finite expected discounted terminal indicator; it is not defined to be a derivative or kernel. `occupation_eq_kernel` proves its equality to the independently recursive nonnegative sign-parity kernel.

`graphSoft_hasFDerivAt` proves the actual end-to-end ordinary derivative by local derivatives and the chain rule. Its concrete `Regular` condition requires unique winning operands only at hard pools. Softplus activation nodes are smooth even at zero preactivation or zero fan-in. The condition imposes no artificial strict activation gates and no strictness of losing nested pool subtrees. `graph_derivative_occupation` is the resulting ordinary-input backward identity. At tied pools the selected occupation/kernel identity still holds, but classical differentiability is not asserted merely from the tie selection.

`graftPlan` attaches annotations to the existing graph graft operation, with `graft_soft` proving exact prefix/suffix composition at the actual prefix forward state. `fullOccupation` directly sums cumulative-discount-weighted visits along the **original full graph's** normalized trajectories. `fullOccupation_graft_last` proves equality to the suffix terminal law at the chosen intermediate node. `intermediate_derivative_fullOccupation` therefore proves the actual intermediate-state gradient formula with full original-graph visits, with the source starting-sign factor. It does not replace the original graph by an unrelated independently chosen suffix.

`pathPayoff` uses each node's predictable immediate reward, namely the conditional expectation of its source split-bias and entropy payment. This preserves the expected payoff even when the cemetery state lumps explicit stopping with continued zero-fan-in absorption. `expectedPayoff_eq_playerValue` proves that the normalized finite trajectory interpreter equals each canonical player's actual recursive expected payoff; `expectedPayoff_eq_split` connects this to the source decomposition.

## Exact boundary and remaining scope

- This batch covers the source's basic annotated affine/activation/addition/nonempty finite-pool nodes. It does not automatically infer an activation annotation for every arbitrary nested `SignedExpr`, and does not claim source semantics for multiplication nodes.
- The full finite trajectory interpreter is for the canonical SPNE. Arbitrary-profile deviations are covered by the direct recursive player-value and signed saddle/SPNE proofs; this batch does not introduce a second full-trajectory probability datatype for every off-equilibrium profile.
- The predictable-reward trajectory interpreter proves expected payoff equality, not pathwise equality to a finer sampled stop/continue reward process. The stop/zero-row cemetery lumping is explicit.
- Classical hard-pool derivatives use explicit unique winners. A separate almost-everywhere differentiability theorem for smooth-plus-hard-pooling DAGs is not claimed here.
- Uniqueness is proved for `NoPools`, exactly the source's no-maxpool uniqueness scope. General tied pool equilibria can have multiple policies.
- The existing layered `Network` softplus batch remains intact; this batch extends the shared `Circuit` architecture with a separate source-syntax annotation. There is no newly claimed compiler equivalence between every arbitrary `Network` and `Circuit` instance.

## Production modules

Top imports: `Thesis.SoftplusCircuitUniqueness`, `Thesis.SoftplusCircuitVisits`, `Thesis.SoftplusCircuitPayoff`. Together these import all thirteen leaves:

1. `SoftplusCircuitModel`
2. `SoftplusCircuitLocal`
3. `SoftplusCircuitEquilibrium`
4. `SoftplusCircuitPlayers`
5. `SoftplusCircuitRows`
6. `SoftplusCircuitDerivative`
7. `SoftplusCircuitPaths`
8. `SoftplusCircuitOccupation`
9. `SoftplusCircuitCuts`
10. `SoftplusCircuitVisits`
11. `SoftplusCircuitUniqueness`
12. `SoftplusCircuitTransition`
13. `SoftplusCircuitPayoff`

The exact-type contract file is `reports/softplus-circuit-expected-types.json`, containing twenty explicitly quantified source-facing targets, manually stated independently of pretty-printed declaration types. Parent publication must retain independent review and its clean import/type/axiom gate before promotion.

## Frozen file hashes

- `formalization/Thesis/SoftplusCircuitCuts.lean`: `f15a205c07749cf491937783a1bc63e943d550bf5cc43ce6e667d7254813a8af`
- `formalization/Thesis/SoftplusCircuitDerivative.lean`: `bee728e4a650c16e223b3cc2074fcf2658c14d9e79cdc2caf76ee9dc651354fb`
- `formalization/Thesis/SoftplusCircuitEquilibrium.lean`: `b06267422a5b58511a34a2dad94bb14ea72b002f7ee1007e13a7b00f07930c1e`
- `formalization/Thesis/SoftplusCircuitLocal.lean`: `a7f11ae693874395a25a562467b389b96314a923b8f30c275c8052f19d9567e6`
- `formalization/Thesis/SoftplusCircuitModel.lean`: `e3ff8b6ea0d8122c19fde230ec7b8717ebd47d91a3bcd557d5c223768aefc625`
- `formalization/Thesis/SoftplusCircuitOccupation.lean`: `be5bbeb2eb779e42d88a97a6c24a9d7b38fa94cc1523b78875f23af0cdc47c34`
- `formalization/Thesis/SoftplusCircuitPaths.lean`: `d1b67bace50c5a5af7f472da75b53c41079b4a661e5c4cd9423f8b8fb28f2681`
- `formalization/Thesis/SoftplusCircuitPayoff.lean`: `b3b9536ccd71bc7b09661512b13a4261308da92cb0fdba08b8d45358604d7110`
- `formalization/Thesis/SoftplusCircuitPlayers.lean`: `16ec9d833289afe8c6d19713d613fed144a5a6eba0c0eeb3b69f6dc833b96d1b`
- `formalization/Thesis/SoftplusCircuitRows.lean`: `45a34fcc6621f95d6c92aaa748f1f60c5e4066eb0a9f0d1c8f29ead697ec3c10`
- `formalization/Thesis/SoftplusCircuitTransition.lean`: `414856f4a9aae674e7a12a54ca33c1cafd3093a522e173d000f604e42182a20a`
- `formalization/Thesis/SoftplusCircuitUniqueness.lean`: `89b105c2288d7feb7634185bd10e35886091d6fa5c4df41e3d1090b72d754f48`
- `formalization/Thesis/SoftplusCircuitVisits.lean`: `eb7731b6aa7d8ac2def2032e969f99047fb990814e8e9b5651bfbe32078b20a9`

Validation: sequential `lake env lean -o ...` for each leaf; `/tmp/SoftplusCircuitContracts.lean` directly assigns each manually specified full type to its fully qualified declaration and prints the kernel axiom closure. Exit status 0. No simultaneous full `lake build` was run. No `sorry`, new axiom, or `native_decide` was introduced.
