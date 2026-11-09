# Lean mathematics for the thesis

The project uses Lean 4 and mathlib v4.35.0, with dependencies pinned in
`lean-toolchain` and `lake-manifest.json`. This remains a partial formalization
of the thesis. The coverage map records the exact scope of each source theorem;
proved components do not silently count as an entire source theorem.

## Start with the definitions

There is one finite MLP parameter datatype, `HiddenMonotonicity.Network n m`.
A network is either an identity output or one affine layer followed by a smaller
network. `n` and `m` are the input and output widths; every intermediate width
may be different. A layer stores positive/negative weight and bias parts, whose
differences are the ordinary weights and biases.

- `net.eval x` is the ordinary ReLU forward pass.
- `net.split p q` returns the two split heads, whose difference is
  `net.eval (p - q)`.
- `net.forwardWith activation x` evaluates those same parameters with another
  scalar activation. `net.decomposeWith pairActivation (p,q)` evaluates a
  neuron-local decomposition. A **valid pair activation** simply preserves the
  scalar output difference; induction proves recovery of the full network.
- `net.originalTrace x` records the active gates in an ordinary forward pass.
  `net.trace (p,q)` gets the same gates from split coordinates. A `MaskedTrace`
  is this fixed-gate view of the same network, not an independently chosen model.
- A `Row n` is a continuous linear map from an input perturbation vector to
  a scalar output change. It represents a row of a Jacobian. A `Sensitivity n`
  is a pair of such rows: one for each input stream. `unified` takes half their
  difference, as required by the balanced input lift `(x/2,-x/2)`.
- `stabilized` executes the complete backward recurrence, including every
  equal subtraction from the two sensitivity rows. Its equations are definitions
  of the algorithm, not hypotheses assumed in the closed-form theorem.
- A `QSource` contains the actual auxiliary function, its computed derivative,
  and its shift coefficient. The auxiliary keeps the original prefix, replaces
  one ReLU by a minimum, and uses a linear absolute-weight tail without biases.
  Every listed derivative is proved correct.

Continuous linear maps carry the finite-dimensional derivatives without hiding
matrix transposes or requiring all layer widths to be equal. They are ordinary
linear functions with continuity recorded for mathlib's differentiation API.

## Main modules

| Module | Mathematical content |
|---|---|
| `HiddenMonotonicity/Network.lean` | Shared finite MLP, original and split evaluation, exact recovery and common-shift law |
| `HiddenMonotonicity/Decomposition.lean` | Same network with generic scalar/pair activations; full-network validity and mixing recovery |
| `HiddenMonotonicity/Convexity.lean` | Nonnegative split streams are monotone and Jensen convex |
| `HiddenMonotonicity/NetworkDerivative.lean` | Actual Frechet derivatives of the full split network |
| `HiddenMonotonicity/MaskedTrace.lean`, `OriginalTrace.lean` | Gate extraction, original/split Jacobian agreement, canonical absolute-weight products |
| `HiddenMonotonicity/StabilizedBackward.lean` | Full varying-width shifted algorithm, mass law, finite correction sum, half-shift specialization |
| `HiddenMonotonicity/QSources.lean` | Actual Q-function derivatives, closed formulas, and original-gradient reconstruction |
| `HiddenMonotonicity/Backward.lean`, `ClosedFormula.lean` | Explicit rectangular matrix pullbacks and ordered noncommuting finite sums |
| `HiddenMonotonicity/Chunks.lean` | Exact linear/residual/product/max-pooling algebra and strict max derivatives |
| `HiddenMonotonicity/Counterexamples.lean` | Actual vanishing head derivatives despite nonzero sensitivity mass |
| `Thesis/BackwardGames.lean` | Explicit sign-labelled stopping paths, discounts, normalized kernels, and actual MLP gradient recovery |
| `Thesis/RoutingBackward.lean` | Network-derived contribution masses, full alpha-beta recurrence, and discounted routing-path recovery |
| `Thesis/SoftplusBackward.lean` | Actual full Softplus-network derivative and discounted occupation recovery |
| `Thesis/Games.lean` | Finite path laws, dynamic programming, Hellinger overlap, per-pixel partition, Doob conditioning |
| `Thesis/Regularization.lean` | Softplus derivatives, binary entropy optimizer, finite Gibbs variational principle |

## Assumptions and boundaries

ReLU derivative statements require strict nonzero preactivations at every reached
layer. Algebraic statements about a selected gate can also hold at a tie, but do
not assert classical differentiability there. Canonical split weights mean
`Wp = max W 0` and `Wn = max (-W) 0`, so `Wp+Wn = abs W`.

Shifted backward sensitivities are algorithmic quantities. They are not asserted
to be derivatives of a forward function with input-dependent re-centering.
Unshifted sensitivities and the derivatives of every auxiliary Q are genuine
Frechet derivatives. The difference of shifted unified head sensitivities is
also proved to be the derivative of the original target.

Probability kernels and their positivity require the stated nonnegative weights
and positive normalizers. Ordinary path probabilities are kept separate from
discounted occupation measures. Gradient/LRP recovery for specified policies
does not by itself prove that those policies form a global game equilibrium.

`coverage_map.json` and `claim_inventory.json` identify remaining gaps, including
architectural extensions, geometry, equilibrium claims, and randomization
asymptotics. The Lean proofs do not certify Python implementations, floating-point
behavior, empirical tables, or the correctness of every prose claim.

## Build and audit

From this directory, with `elan` installed:

```sh
lake exe cache get
lake build
python3 scripts/inventory.py
python3 scripts/audit.py
lake env lean Audit.lean
```

`Audit.lean` prints transitive axiom dependencies for every project theorem
and checks every mapped theorem name, including the names used by TeX links.
The accepted foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, or custom axioms are used.

The local development checkout may reuse a mathlib cache through an ignored
`.lake/packages` symlink. A fresh checkout fetches the pinned dependencies normally;
the development symlink is not needed.

## Source links

`tex_links.json` maps source labels to declarations. The root script
`scripts/generate_lean_links.py` locates each declaration in a committed source
snapshot, checks its exact file contents, and generates permanent GitHub links
with real line numbers. `lean_links.json` records the commit and file hashes.
A **Lean variant** badge links a complete theorem under the stated formal
model's assumptions; **Lean components** links part of a broader statement.
See the corresponding coverage-map entry for the exact distinction.
