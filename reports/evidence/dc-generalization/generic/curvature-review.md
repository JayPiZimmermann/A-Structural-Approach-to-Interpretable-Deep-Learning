# Curvature lift semantic review

The new module constructs actual profiles from the existing integrated Jordan
decomposition of the classical second derivative. It adds the same linear term
`a x`, with `a = max (-s₋) 0`, to both profiles and takes the common coefficient
`L = max (s₋ + a + ∫ f''₊) (a + ∫ f''₋)`. Both resulting derivatives lie in `[0,L]`.
The asymmetric lift is `C(x-y) + L y`, so its two partial derivatives are
nonnegative. Convexity follows from convexity of the scalar profile under an
affine map. Exact cancellation preserves `f(x-y)`.

The analytic hypotheses are genuine differentiability of `f`, local absolute
continuity of its derivative on every finite interval, and global integrability
of the actual second derivative. No slope bound or desired split is assumed.
The sum of the positive and negative curvature integrals is proved equal to the
integral of the absolute second derivative. The resulting convexity and
coordinatewise monotonicity are global on the real plane.

The original pair has origin values `(f(0),0)` and is nonnegative on the
nonnegative quadrant when `f(0) ≥ 0`. The optional normalized pair adds the same
constant `max(-f(0),0)` to both components, preserving the split and requiring no
sign hypothesis for nonnegative outputs. A concrete constant activation `f=-1`
checks admissibility, the original origin values `(-1,0)`, normalized values
`(0,1)`, and application of the general nonnegativity theorem.

`curvature-expected-types.json` contains independently authored full quantified
contracts for five headline claims; these were not extracted from inferred Lean
types. The standard repository renderer checks exact type equality, defining
module, and only `propext`, `Classical.choice`, and `Quot.sound` as allowed axioms.
These receipts are diagnostic shared-tree evidence until the parent integrates
the new module into the public root and performs the committed closure gate.

The initial compile exposed beta-reduction issues in an integral identity and
origin evaluation, and function-addition elaboration in derivative proofs.
Explicit reduction and conversion repaired them without changing statements.

An independent read-only review by the `audit_curvature_leaf` agent found no
blocking issue: the coefficient orientation, full-plane scope, exact
cancellation, common normalization, and all five contract quantifiers agree
with the intended mathematics. That review did not run builds or axiom checks.

Final diagnostic receipts all passed with exit code zero:

- `curvature-final-build.log`: targeted module build after narrowing the generic
  lift's imports and adding the explicit curvature dependency.
- `curvature-exact/contracts.log`: all five exact contracts, defining modules,
  and allowed-axiom checks passed; the imported environment audit covered 322
  project theorem declarations.
- `curvature-boundary.log`: the negative-constant nonvacuity and normalization
  consumer passed with the permitted axioms only.

From the repository root, regenerate the driver with
`python3 reports/evidence/dc-generalization/generic/check_curvature.py`.
From `formalization`, run `lake build HiddenMonotonicity.CurvatureMonotoneDCLift`,
then `lake env lean ../reports/evidence/dc-generalization/generic/curvature-exact/ExactContracts.lean`
and `lake env lean ../reports/evidence/dc-generalization/generic/CurvatureBoundary.lean`.
`curvature-source.sha256` binds the source, author contracts, boundary consumer,
and generator used for these receipts.
