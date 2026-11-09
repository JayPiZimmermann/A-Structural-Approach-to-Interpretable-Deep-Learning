# Nonconvex CPWL representation repairs

The frozen leaf `Thesis.CPWLLattice` proves a genuine arbitrary CPWL-to-DC
representation from the existing independent `CPWL` definition: continuity and
an actual finite closed-polyhedral cover with affine pieces. No convexity,
lattice representation or DC decomposition is assumed.

The endpoint separation lemma starts with a continuous finite selection of
affine lines. Finite local active-set control, the intermediate-value theorem
and a greatest zero in a compact level set show that one affine branch lies
above the initial and below the final function value. Applying this along actual
input segments gives separation for the original affine pieces.

`cpwl_lattice_representation` takes as blocks all upper-piece subsets occurring
at input points. Each block's minimum is globally below the function by the
proved separation lemma. The block at the evaluation point attains the function.
This proves the finite max-min representation from the cover.

`cpwl_polynomial_difference` then constructs finite max-affine polynomials `g,h`
with `f = g.eval - h.eval`. Finite maximum closure uses the actual identity
`max(g1-h1,g2-h2) = max(g1+h2,g2+h1)-(h1+h2)`; each affine minimum is already the
negative of a max-affine polynomial. `cpwl_iff_polynomial_difference` also proves
the converse using the existing explicit active-piece polyhedral cover.

Nine independently reviewed complete type contracts are in
`reports/cpwl-expected-types.json`. The focused production compile and explicit
expected-type/axiom checks are recorded in
`reports/evidence/foundations-repairs/CPWLLattice-production.*`,
`CPWLExpectedTypeChecks.lean` and `cpwl-expected-types.*`. No sorry, custom axiom,
or native_decide is used. Whole-tree publication and closure checks belong to root.

The complete source theorem now also compiles in the new
`Thesis.CPWLReLUEquivalence` leaf. Its headline
`Thesis.PiecewiseLinear.cpwl_relu_equivalence` includes both directions and
explicit shared `HiddenMonotonicity.Network`/readout witnesses obeying the literal
`⌈Real.logb 2 (n+1)⌉₊ + 1` depth bound. The final affine readout counts as one
layer. The zero-dimensional input case and zero-summand representations are
included, and no width bound is claimed.

The new `Thesis.ReLUCompiler` leaf stores actual networks with affine readouts in
`AffineHead`. It proves composition evaluation and additive hidden depth, constructs
a one-hidden-layer pairwise maximum using three signed-value rails, and compiles
whole binary max forests with exactly `k` hidden layers. A proved surjection pads
arbitrary nonempty term types of size at most `2^k` to binary leaves without changing
the maximum. Arbitrary signed sums are absorbed into the affine output and add no
hidden layers. These are constructive data and evaluation theorems, not an
assumed realizability predicate.

The independent `Thesis.SignedMaxReduction` frontier supplies the dimension-only
signed-max reduction; see `reports/repairs-signed-max.json` and its separate exact
contracts. The source assembly first uses the actual-cover CPWL-to-DC bridge, then
that reduction, then the compiler with `k = Nat.clog 2 (n+1)`. The library theorem
`Real.natCeil_logb_natCast` proves the bridge from integer ceiling logarithm to the
literal source real-logarithm bound. The reverse direction uses the existing
actual active-piece polyhedral cover for a network with an affine readout.

All three new production leaves are frozen after their focused sequential compile.
All nine complete expected types and axiom checks pass; the only kernel axioms
are `propext`, `Classical.choice`, and `Quot.sound`. The production receipts are
`CPWLLattice-production.*`, `ReLUCompiler-production.*`, and
`CPWLReLUEquivalence-production.*` under `reports/evidence/foundations-repairs/`.
`cpwl-completed-frontier.json` binds the module and contract hashes. Root owns
module exports, source mappings, publication, and whole-import closure validation.

The original FOUND-04 gap is now proved rather than narrowed: arbitrary nonconvex
finite-cover CPWL is covered, with the dimension-only bound. No new source
correction is needed beyond the already adopted affine-output network convention.
