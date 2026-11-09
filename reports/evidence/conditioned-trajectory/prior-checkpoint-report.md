# Conditioned trajectory composition checkpoint

Status: the complete new draft compiles with exit zero and an empty diagnostic
log. It has **not** been promoted into `formalization/Thesis`, imported into the
public root, or subjected to its independent exact-type and adversarial review
gates. Root requested this checkpoint so an agent slot can move to the user's
new editorial priorities. The original mathematical task remains active.

Draft: `reports/evidence/conditioned-survival/ConditionedTrajectory.lean`.
Compile log: `reports/evidence/conditioned-survival/trajectory-draft.log`.
Planned defining module: `Thesis.ConditionedTrajectory`.
All declarations extend the `Thesis.ConditionedSurvival` namespace.
No frozen production file was changed for this draft.

The prerequisite `formalization/Thesis/ConditionedSurvival.lean` is separately
frozen and independently reviewed. Its complete passed receipt is
`reports/evidence/conditioned-survival/receipt.json`.

The new draft contains genuine composition proofs of the remaining ordinary
conditioned-survival clauses, rather than definitions encoding the conclusions:

* `prefixMass` is the literal endpoint marginal of the original prefix path law.
* `timeMass` is the literal time-index marginal of the complete length-N path
  law, using the actual `stateAt` function on `Games.Paths`.
* `timeMass_factorization` splits the full trajectory sum at that time and proves
  that its mass is the original prefix mass times the remaining computed
  survival probability. The proof inducts through the finite path sums and
  handles time zero and the terminal layer.
* `conditioned_time_marginal` applies the already verified full conditional
  path-law quotient to derive the source layer-marginal formula. The result is
  for a marginal of the full conditioned distribution, not a newly defined
  prefix reweighting.
* `conditioned_geometric_kernel` proves the actual geometric-mean edge identity,
  including the zero-row extension. Its zero-denominator formula uses Lean's
  totalized real quotient and agrees with the explicit guarded kernel. The
  prerequisite supplies the mathematical support-pruning justification.
* `conditioned_overlap_paths` and `conditioned_overlap_DP` identify the actual
  conditioned path-law overlap with the geometric path-product sum and the
  backward dynamic program respectively.
* `conditioned_overlap` gives the original surviving-path overlap divided by
  the square root of the two computed initial survival masses.
* `conditioned_hellinger` proves the formula for the actual finite square-root
  distance sum, using normalization of both complete conditioned laws.

The combined headline `conditioned_survival_statistics` packages both models'
layer-marginal formulas, the geometric-edge identity, both path-product and DP
overlap formulas, the normalized overlap formula and the actual squared
Hellinger formula. Only the two initial survival probabilities need be positive;
intermediate zero-potential states are permitted.

The other combined headline, `trajectory_bc_monotone`, gives the entire source
`ptnb:lem:bc-monotone` chain on actual full row-stochastic prefix path laws:
initial overlap one, all-depth bounds in [0,1], antitone overlap, monotonicity of
the actual squared Hellinger sum, its equality with one minus overlap, and the
geometric-kernel DP identity at every depth. Its finite ambient state space may
include a cemetery. This theorem uses stochastic rows and does not confuse
ordinary surviving sublaws with complete probability laws.

Five independently authored literal contracts are saved in
`reports/conditioned-trajectory-expected-types.json`. Their authoring source is
`reports/evidence/conditioned-survival/trajectory_expected_types.py`. They have
not yet been independently exact-type checked, so they must not be merged into
the public verification manifest as approved contracts yet.

To resume:

1. Confirm the saved draft/contract hashes in `trajectory-checkpoint.json`.
2. Promote the compiled draft as the new `Thesis/ConditionedTrajectory.lean` and
   compile that module sequentially against the frozen prerequisite.
3. Generate and run the direct exact-type/module/universe/axiom driver for the
   five saved contracts.
4. Add a concrete full-path marginal example with an ordinary positive prefix
   entering a zero-future-survival state, and a pair of different conditioned
   supports for the BC/Hellinger formulas.
5. Hand the frozen production module, contracts and receipts to `attack_hidden`
   or another independent mathematical reviewer before root import integration.

The compiled draft can be reproduced from `formalization` with:

```
lake env lean ../reports/evidence/conditioned-survival/ConditionedTrajectory.lean
```
