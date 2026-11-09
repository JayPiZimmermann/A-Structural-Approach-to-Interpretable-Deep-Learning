# Explicit Swish DC pair: targeted evidence

For every positive scale β, the elementary scalar profiles are

- P(z) = (2/β) log(1 + exp(βz));
- Q(z) = P(z) − z σ(βz).

The two-stream branches are F₁(x,y)=P(x−y)+2y and
F₂(x,y)=Q(x−y)+2y. Both are globally convex and coordinatewise
nondecreasing, and F₁−F₂=Swishβ(x−y). They are nonnegative on the
nonnegative orthant. Their common value at the origin is (2/β)log 2;
this construction does not use a zero normalization.

The proof establishes P′ in [0,2] and Q′ in [0,1]. Nonnegativity of
Q″ follows from t(2σ(t)−1) ≥ 0. The exact elementary pair is a convex
majorant construction and is not asserted to be the canonical split of
the positive and negative parts of Swish curvature.

## Checked sources

- `formalization/HiddenMonotonicity/ExplicitSwish.lean`: main elementary pair.
- `formalization/HiddenMonotonicity/SwishSlopeBounds.lean`: optional exact
  endpoint and tangent-intercept identities for the canonical piecewise pair.
- The separate `swish-threshold` evidence directory certifies the unique
  positive curvature turning point, its bracket (2,4), and exact sign regions.

## Successful checks

All commands below ran from `formalization/`. Exit markers are zero.

1. `lake env lean HiddenMonotonicity/SwishSlopeBounds.lean`:
   `slope-build-03.log` and `.exit`, empty successful log.
2. `lake build +HiddenMonotonicity.SwishSlopeBounds`:
   `slope-lake.log` and `.exit`.
3. `lake env lean HiddenMonotonicity/ExplicitSwish.lean`:
   `explicit-build-02.log` and `.exit`, empty successful log.
4. `lake build +HiddenMonotonicity.ExplicitSwish`:
   `explicit-lake.log` and `.exit`. Existing dependency warnings are replayed;
   the new leaf compiles without warnings.
5. `lake env lean ../reports/evidence/dc-generalization/swish/ExplicitSwishContracts.lean`:
   `contracts-02.log` and `.exit`.

The contract driver contains independently authored full-forall expected
propositions, center values and derivatives, both signs of x−y, stream-axis
nonnegativity, and diagonal recovery. Ten headline axiom checks use only
`propext`, `Classical.choice`, and `Quot.sound`.

Earlier failed iterations are retained under their numbered log names. These
are targeted leaf checks, not evidence of a completed production-wide gate.
No production root, frozen theorem file, or contract manifest was edited.

## Integration contracts

`contracts.json` supplies four parent-integratable reviewed contracts: the
three elementary-pair headlines and optional exact curvature sign regions.
Each expected proposition was manually authored from the checked independent
contract files above; none was read from Lean's inferred declaration types.

The repository's `formalization/scripts/verify.py::exact_driver` renders
`exact-elementary/driver.lean` and `exact-threshold/driver.lean` from those
records, grouped by defining module. These targeted drivers check the
independently elaborated expected proposition, universe arity, defining module,
definitional equality of the full theorem type, and allowed axioms.

Both `exact-only.lean` drivers pass with `exact-only.exit` equal to zero.
These drivers retain the repository renderer's exact-contract section and
omit its broader environment-audit tail. The initial complete drivers were
intentionally interrupted during that redundant broader audit (exit 130),
so their `build.exit` files do not claim a successful environment-wide audit.
The parent controls the final production-wide audit.
