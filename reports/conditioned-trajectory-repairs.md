# Conditioned trajectory composition

Status: **frozen for independent review**. `Thesis.ConditionedTrajectory` is now a production leaf, copied byte-for-byte from the compiled checkpoint draft. Production compilation, all five saved exact-type/module/universe/axiom contracts, and the concrete boundary consumer pass. Independent semantic review and the parent's clean public import gate remain pending. No existing frozen production leaf, root, verification configuration, or TeX source was changed.

The production SHA-256 is `f981b0b7669441009d6145714d7f5c518869eefae0deaa67671c4d940cfb49fe`. The original checkpoint, its four recorded hashes, and all five previously authored contracts matched before promotion; the contract file was not edited to obtain a passing check. The historical report is preserved at `reports/evidence/conditioned-trajectory/prior-checkpoint-report.md`.

## Mathematics and source scope

This extends the independently reviewed `Thesis.ConditionedSurvival` using the existing `Games.Paths`, `pathLaw`, `backwardDP`, and actual finite square-root overlap. Its source targets are PTNB `thm:conditioned-survival` clauses (ii)–(iv), especially `eq:conditioned-alpha`, `eq:conditioned-geom-kernel`, `eq:conditioned-bc-kernel`, `eq:conditioned-bc-posthoc`, `eq:conditioned-h2`, and `lem:bc-monotone`. Source layers descend from L to 0; the Lean trajectory time counts transitions forward from 0 to N.

`prefixMass` is the literal original prefix endpoint mass. `timeMass` is the actual time-index marginal of the full length-N path distribution. `timeMass_factorization` proves by finite path-sum induction that the latter is the former multiplied by computed remaining survival. `conditioned_time_marginal` then proves the source marginal quotient for the actual conditioned full path law; it does not define a new object by the desired marginal formula.

`conditioned_geometric_kernel` proves the geometric edge identity for the existing guarded conditioned kernel. Zero-survival rows remain present with mass zero. On those rows the totalized real quotient agrees with that explicit zero-row extension; it is not an assertion that ordinary mathematical division by zero is defined. The prerequisite proves that nonzero conditioned paths from a positive initial survival state cannot visit those rows.

`conditioned_survival_statistics` combines both models' actual layer marginals, the geometric-kernel formula, path-product and backward-DP representations of overlap, the overlap normalized by the square root of computed initial survival masses, and the actual finite squared Hellinger sum. It assumes nonnegative substochastic original rows and positive survival only at the two initial states. Reachable original states with zero future survival are allowed, and no strict intermediate-positivity premise was added.

`trajectory_bc_monotone` separately applies to **complete row-stochastic path laws** on a common finite state space, which may include a cemetery. It proves initial overlap one, all-depth bounds in [0,1], antitone overlap, monotone actual squared Hellinger distance, the exact identity H² = 1 − BC, and the geometric-kernel DP formula at every depth. This statement does not conflate complete distributions with the ordinary surviving substochastic sublaws used by the conditioning theorem.

The ambient time-indexed kernel uses one finite state type, as in the existing `Games` formalization. This batch does not introduce a new dependent family of state types or a new neural-network-to-Markov compiler. It composes the source conditioned marginal/comparison clauses in the established finite-kernel model; the previously reviewed prerequisite supplies the survival, normalization, and zero-support pruning clauses.

## Boundary consumer

`reports/evidence/conditioned-trajectory/BoundaryConsumer.lean` defines two different two-step ordinary kernels on Bool. Both give each first-step state mass 1/2. Model A subsequently survives only through false and model B only through true. Thus both initial survival masses are 1/2, while each has a reachable intermediate state with zero future survival.

The consumer uses the combined theorem to prove both dead-state conditioned marginals vanish and to derive BC = 0 and H² = 1. Separate direct enumeration checks the actual conditioned path laws: A assigns mass one to (false,false), B assigns mass one to (true,true). Additional boundary checks cover the zero horizon, a retained zero row and geometric zero denominator, and failure of normalization when initial survival is zero. These are Lean proofs using finite sums and exact arithmetic, without sampling or `native_decide`.

## Verification and handoff

- Production leaf: `formalization/Thesis/ConditionedTrajectory.lean`.
- Unchanged five full-forall contracts: `reports/conditioned-trajectory-expected-types.json`.
- Exact driver: `reports/evidence/conditioned-trajectory/ExactTypes.lean`, generated with the repository's existing `formalization/scripts/verify.py::exact_driver` and the new leaf as its import root.
- Driver checks: independently elaborated expected type, definitional equality of full declaration types, defining module, universe arity, and allowed transitive axioms. All five pass; each has only `propext`, `Classical.choice`, and `Quot.sound`.
- Imported environment audit: all 351 project theorem declarations in this leaf's import closure pass the permitted-axiom check. This is a focused development receipt, not the parent's clean committed public-closure receipt.
- Durable receipt, command lines, exit codes, hashes, logs, and environment dump: `reports/evidence/conditioned-trajectory/receipt.json` and adjacent files.

All compiles were sequential. The production leaf has no diagnostics; the boundary consumer has no diagnostics. The exact driver emits only expected type displays and unused-binder warnings from the literal independently authored contracts. No `sorry`, new axiom, unsafe reduction, or `native_decide` was introduced. The new root import and source badge integration are intentionally left to the parent after independent review.
