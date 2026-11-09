# Full layered Softplus stopping-game repair

This is a coherent **layered `HiddenMonotonicity.Network`** batch. It repairs the missing full two-player game/SPNE content behind the earlier local variational and derivative-path lemmas. It does **not by itself prove** the source's broader residual/addition/maxpool DAG Softplus statements. Those need a separate `Circuit` extension, requested by root after this batch freezes. Source badges for `ptnb:thm:softplus-forward` and `ptnb:thm:softplus-gradient` must preserve this layered scope.

Seven NEW leaves are frozen below; importing `Thesis.SoftplusTransitionPayoff` imports the full batch. No existing/frozen Lean definitions, roots, manifests, or TeX were modified. Declarations are in `Thesis.SoftplusGame`.

## Actual game and arbitrary profiles

The strategy space is exactly the existing `Thesis.ReLUNetGame.Strategy net`: each player's continuation probability at each controlled signed neuron lies in [0,1], with stop probability 1-p. Both players may independently randomize at every state, including pure endpoint probabilities. The theorem is not restricted to a single common policy or to pure deviations.

`mixedTransition` combines stopping with the existing total signed weight kernel (`StoppingBoundary.transition`). Its law is normalized and nonnegative; a zero-fan-in continuation is absorbed in the cemetery. `continuation_recovery_total` proves the original normalized continuation formula recovers its affine value even on zero rows, from nonnegative weights rather than an assumed nonzero-row condition. The signed bias is retained at continuation. There is no assumption that structural discounts are at most one.

`PlayerValues` retains all four player/turn coordinates. `playerStep` gives the routed expectation and split bias to each player, while the entropy bonus theta H(p) is credited **only to the active player**. `playerStep_transition` proves that this definition is precisely the actual normalized stochastic Bellman expectation, with cemetery value zero, continuation-scaled bias, structural discount, and controller-only entropy credit. It holds for every off-equilibrium profile, not only Gibbs policies.

`policyValue` is the signed plus-minus value with +theta H at plus-controlled states and -theta H at minus-controlled states. The independent all-profile theorem `playerValue_advantage` proves it equals the difference of the actual two player payoffs. Thus the equilibrium proof is not an unrelated zero-sum model with an unproved source identification.

## Full equilibrium and source player values

`softplus_saddle` proves arbitrary-profile saddle inequalities for both signed-state coordinates, and the canonical value equals (softEval,-softEval). The induction allows arbitrary ordered boundary values, which is necessary to control deviations across several layers and arbitrary width changes.

`SubgamePerfect` quantifies local best response over every mixed action at every signed neuron, evaluated against the profile's own realized lower-state values. It does not assume network values, Gibbs probabilities, equilibrium, or the desired invariant. `subgamePerfect_iff` proves that at positive temperature a profile is subgame perfect **if and only if both complete strategies equal `gibbsStrategy`**. Zero preactivation and zero fan-in do not create extra optima. `spne_prefix_saddle` further proves full arbitrary-strategy deviation bounds at every true predecessor subgame using the actual restriction of a whole-network SPNE.

`playerValue_gibbs` proves that the four source player/turn coordinates are the actual `net.decomposeWith softSplit` coordinates, with sign determined by player XOR turn. `softplus_forward_spne` bundles existence, uniqueness, player-specific values, and ordinary forward recovery. This is the missing full game content of the layered source theorem, not merely the previously available arithmetic difference identity.

## Occupation, shared cuts, and affine output

`profileProbability` is the product of the actual profile's continuation probabilities and normalized signed weight transitions along an ordinary-input-reaching path. Both state signs are absolute owners. `profile_step_transition` proves each off-equilibrium path factor is the actual normalized mixed-kernel transition. `profileProbability_gibbs` identifies these genuine policy products with the existing `softProbability`; `spne_occupation_eq` obtains this identity from the proved SPNE characterization.

`spne_gradient` and `spne_affine_gradient_profile` express actual classical derivatives in terms of these profile occupations, for arbitrary starting sign q. They reuse the already proved zero-fan-in `SoftplusBoundary.gradient_occupation`. They identify **only the ordinary activation/logit derivative** with an occupation difference, never an individual soft-decomposition coordinate derivative.

`Network.append` is the existing shared composition. `softEval_append`, `prefixStrategy`, and `suffixStrategy` connect the actual full policy with its true prefix and suffix restrictions. `spne_intermediate_gradient` evaluates the actual suffix derivative at the actual prefix Softplus activation vector and uses the restricted whole-network SPNE. No independently chosen intermediate state or assumed chain invariant is substituted.

`affine_saddle` and the affine derivative statements retain a **forced ungated** final readout, signed weights and bias. Zero readout fan-in is allowed. There is no output sigmoid or output entropy bonus.

The path products index the ordinary-input-reaching subset, as in the existing derivative-path library. Stopped/cemetery trajectories contribute zero ordinary-input occupation and are not represented as fake input paths. Normalization is proved for the total one-step mixed kernels; this batch does not introduce a separate complete-history PMF datatype. The finite profile payoff is the recursive discounted Bellman expectation, explicitly connected to those kernels by `playerStep_transition`.

## Scope and remaining work

All game, uniqueness, player-coordinate, intermediate-layer and affine-output results here are for the finite varying-width **layered Network**. The general source theorem's residual/addition/ordered-maxpool **Circuit** SPNE and corresponding general DAG Softplus gradient remain a separate extension. The prior ReLU game declarations and their NonzeroRows hypotheses have not been changed or silently declared repaired. General convex-regularizer SPNE beyond this literal Shannon-entropy game is also not claimed; the proof reuses the existing entropy variational/uniqueness lemmas and the shared source strategy/continuation definitions.

Positive temperature is explicit. State-based arbitrary behavioral probabilities match the source's pi(s) policies; no theorem over a separate history-dependent strategy datatype is asserted. Independent promotion review, source mapping, and clean import-closure publication checks are root-owned next steps.

## Validation

All seven modules compiled sequentially by targeted Lean calls against the existing dependency frontier. No full lake build ran concurrently from this agent. `reports/softplus-game-expected-types.json` contains **21 hand-specified full-forall contracts**, including implicit dimensions, defining modules, evidence and layered scope. An independent scratch checker elaborated `example : EXPECTED_TYPE := @DECLARATION` and printed every axiom closure. **21/21 exact-type checks passed, exit 0; every closure is exactly `propext`, `Classical.choice`, `Quot.sound`.** No sorry, admit, new axiom, or native_decide was introduced. The expected types were not extracted from #print output.

This is a targeted local validation receipt, not a clean-checkout publication claim.

Freeze SHA-256:

| Module | SHA-256 |
|---|---|
| `Thesis.SoftplusPolicies` | `cce5f2f5c41614f6195b32a0170003d48a3bc9d72d5d69e14e8a217cee59c936` |
| `Thesis.SoftplusEquilibrium` | `63520c7d242d5aff9b1360294a8b0b2db592fcd9c8364219a3cf8c9851c6acb1` |
| `Thesis.SoftplusPlayerValues` | `92a7a5433eddb898f52de8378c0e0013f7aa1983698a72ef63566eb8eb7af70c` |
| `Thesis.SoftplusReadout` | `eb99ef0969590ac6a21a29fbcd2382725b039179b9f508b0456b0a37cefc6931` |
| `Thesis.SoftplusGameOccupation` | `8bc96e65fe9b76e69a051e683cd4f22bde05ef0ad0c619ea2cffbf2f2c1be901` |
| `Thesis.SoftplusSubgames` | `0704cd335881e77c3c1919f122ea49cd3ec8b77c30c463015fbbed7e48fc4d65` |
| `Thesis.SoftplusTransitionPayoff` | `5ffb395cd165bbe84fdf1f67f226649c28b06d18a68968f8d3a82e765d47e9d4` |

Contract manifest SHA-256: `67cb68174a8c41b18840ec4ce24fd6a988f2e022b7ab98b65626c03da8c53018`.
