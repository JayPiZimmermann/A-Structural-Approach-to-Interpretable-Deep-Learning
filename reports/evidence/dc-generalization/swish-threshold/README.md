# Exact Swish turning-point evidence

The new leaf `formalization/HiddenMonotonicity/SwishThreshold.lean` proves existence
and uniqueness of a positive real root `r` of `r * (2 * sigmoid r - 1) = 2`, with
the exact bracket `2 < r < 4`. It proves the complete strict and zero curvature
sign classification for every Swish scale `β > 0`, with thresholds `|β*x| = r`,
and the exact endpoint slopes `(2-r)/4` and `(2+r)/4` for every nonzero scale.
The constant is defined by a unique root; no elementary expression for it is
asserted and no floating-point approximation enters the proof.

Validation commands, run from `formalization/`:

```sh
lake env lean HiddenMonotonicity/SwishThreshold.lean
lake build +HiddenMonotonicity.SwishThreshold
lake env lean ../reports/evidence/dc-generalization/swish-threshold/SwishThresholdContracts.lean
```

All three commands returned exit status 0, recorded in the corresponding
`.exit` files. The module build contains the repository's existing module-system
and tactic warnings, including a module-system warning for the explicit IVT
import in this leaf. The direct source and contract checks contain no warnings.

`SwishThresholdContracts.lean` contains independently written full quantified
expected propositions, a concrete positive-curvature central witness, both
zero-curvature boundary orientations for all positive scales, and strict
negative-curvature witnesses in both tails. Its six headline axiom audits use
only `propext`, `Classical.choice`, and `Quot.sound`.

This is a checked optional leaf and diagnostic evidence from the shared working
tree. It is not yet claimed to be imported by the public root or included in the
public claim manifest; parent integration owns that decision. The simpler
elementary Swish decomposition does not require this implicit root.
