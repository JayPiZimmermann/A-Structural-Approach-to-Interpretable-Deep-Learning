# Foundations repair frontier

The repaired source-facing contracts are listed in `reports/foundations-expected-types.json`.
They preserve the independent CPWL definition, actual convex hulls/extreme points,
actual Fréchet derivatives, normalized randomized policies, and signed ungated
readouts. No `sorry`, custom axiom, `native_decide`, or representation hypothesis
has been introduced. All five focused source modules and 22 explicit expected-type checks compile.
All 22 headline axiom receipts contain only `propext`, `Classical.choice`, and
`Quot.sound`. These are local diagnostic receipts; the parent owns the clean
closure certificate.

## Repaired mathematical bridges

- **FOUND-05 (convex CPWL representation):** `Thesis.PiecewiseLinear.convex_cpwl_iff_max_affine`
  proves both directions for scalar functions. CPWL remains continuity plus a finite
  closed-polyhedral affine cover. A cell with nonempty interior supplies a global
  affine minorant by convex local-to-global minimality; the finite closed cover has
  dense interiors, and continuity extends the finite maximum identity everywhere.
  Empty-interior cells are discarded by a proved density argument, not an assumption.
- **FOUND-05 (homogeneous support and vertices):**
  `homogeneous_convex_cpwl_unique_polytope` and
  `homogeneous_convex_cpwl_vertices` start with an arbitrary scalar function and
  its genuine CPWL, convexity and positive-homogeneity hypotheses. Scaling proves
  that intercepts can be removed. The resulting nonempty finite hull is unique,
  and its mathlib extreme points are exactly actual attainable Fréchet gradients.
  This closes the missing arbitrary-function bridge in the previous support theorem.
- **FOUND-10 (biased affine slice):** `Thesis.Tropical.slice_attainable_gradients`
  and `Thesis.SourceFoundations.biased_vertices_gradients` prove that actual input
  gradients are exactly projections of lifted vertices uniquely exposed by permitted
  directions `(x,1)`. `SliceVisible` is an actual singleton exposed-face condition;
  it does not define vertices or gradients. Every projected maximizing lifted point
  is identified by Fermat's theorem. Equal input projections and equal slice values
  then determine the intercept, proving singleton-face necessity. Strict exposure
  gives local affine equality and a genuine derivative, proving sufficiency.
- **FOUND-08 (all subgames, all randomized ties):**
  `Thesis.ReLUNetGame.subgamePerfect_iff_gateOptimal` quantifies over the same
  recursive `Strategy` type as the original game. `SubgamePerfect` asks for
  randomized best responses at every signed state using actual predecessor policy
  values. It is equivalent to both players continuing with probability one for
  strictly positive original preactivations, probability zero for strictly negative
  preactivations, and any probability in `[0,1]` at zero. The concrete pure strategy
  satisfies the predicate; every satisfying profile has the original signed values.
- **FOUND-03 (affine output):**
  `Thesis.SourceFoundations.split_tropical_rational_affine` constructs the two
  ungated output polynomials and bundles zero intercepts, nonnegative slopes,
  convexity, monotonicity, positive homogeneity, exact actual split affine heads,
  exact signed-logit recovery and the two final weighted Minkowski sums.
  `Thesis.SourceGeometry.minkowski_propagation_affine_network` also includes
  basis-singleton initialization and the complete hidden set recursion.
  `Thesis.SourceFoundations.relu_net_game_value_affine` combines the selected
  randomized saddle, actual affine logit, complete tie characterization and value
  of every recursive subgame-perfect profile. Zero hidden layers are allowed.

## Source corrections required (parent owns TeX)

1. A finite intersection of closed halfspaces is a **polyhedron**. The equivalent
   halfspace definition of a **polytope** requires boundedness; for real-valued
   support maxima in these statements it also requires nonemptiness (FOUND-01).
2. Backward induction gives existence of optimal policies and uniqueness of the
   value. It does not give policy uniqueness when actions tie (FOUND-02).
3. Apply the max split recurrence only to hidden ReLU layers. The signed affine
   final layer uses the two affine sums, with no output max gate (FOUND-03).
4. On a fixed homogenizing slice, use projections of **slice-visible** lifted
   vertices. Ambient lifted vertices need not all be reachable (FOUND-10).
5. In the finite-hull maximum clause say "nonempty finite set" (FOUND-13).
   The existing nonempty compact-convex support wrapper already has the right scope.

## Genuine residuals

- **FOUND-04:** The full arbitrary nonconvex CPWL-to-ReLU converse and the source's
  dimension-only depth bound are not yet proved. Forward arbitrary-weight network
  CPWL and the full convex CPWL/max-affine equivalence are proved. No DC or lattice
  representation assumption has been substituted for the missing nonconvex bridge.
- **FOUND-09:** The source-facing generic stochastic game theorem remains an exactly
  layered model with a common nonempty finite action type. An arbitrary finite-DAG,
  state-dependent-action encoding preserving payoffs and strategies is not proved.
  The old prose claim that duplicate actions alone provides this encoding is not a
  checked theorem.
- Distributional curvature/activation work is outside this assignment and is owned
  by the hidden-monotonicity repair worker. Public integration and clean committed
  closure certification are owned by the root worker.

## Verification

Focused commands run from `formalization/` use `lake env lean` with explicit
`.olean` output for dependencies. Logs and exit markers are under
`reports/evidence/foundations-repairs/`. `ExpectedTypeChecks.lean` states the
reviewed expected complete types as Lean examples, checks explicit declarations,
and prints transitive axioms. The parent verifier additionally checks level arity,
exact definitional equality, all environment theorem axioms, imports and source
freshness. These local receipts do not alone claim a clean-clone certificate.

## FOUND-04 investigation and reopening point

The full mathlib source search is retained in
`reports/evidence/foundations-repairs/mathlib-representation-search.txt`; none of
the 96 matches supplies a CPWL/DC, lattice max-min, or ReLU representation theorem.
The missing mathematical step is precisely the global finite-affine-selector
lattice theorem: for continuous `f` with finitely many affine pieces `lᵢ`,
construct a finite family of nonempty index sets `S` such that
`f(x) = max_S min_{i∈S} lᵢ(x)` for every real input. A useful intermediate claim is
the two-point selector property
`∀ x y, ∃ i, lᵢ(x) ≥ f(x) ∧ lᵢ(y) ≤ f(y)`, proved along the segment from `x` to `y`.
This is not among the current hypotheses or definitions. Proving it, or an actual
finite-polyhedral DC decomposition, would reopen the general representability
construction. A max/min network construction alone would not establish the
source's dimension-only depth bound: that additionally needs the independent
signed-sum representation using maxima of at most `d+1` affine functions. No
unproved version of any of these statements was added to the production library.

## Tested frontier

| Module / check | Result | Receipt |
| --- | --- | --- |
| `Thesis.AffineSliceGeometry` | exit 0 | `affine-slice.log`, `affine-slice.exit` |
| `Thesis.ConvexCPWL` | exit 0 | `convex-cpwl.log`, `convex-cpwl.exit` |
| `Thesis.ReLUNetEquilibrium` | exit 0 | `relu-equilibrium.log`, `relu-equilibrium.exit` |
| `Thesis.SourceGeometryStatements` | exit 0 | `source-geometry.log`, `source-geometry.exit` |
| `Thesis.SourceFoundationsStatements` | exit 0 | `source-foundations.log`, `source-foundations.exit` |
| 22 explicit expected-type examples and axiom checks | exit 0 | `expected-types.log`, `expected-types.exit` |

The snapshot manifest `sha256.json` binds the final module sources, reviewed
contracts, explicit check file and local logs. The source scan of the five changed
modules contains no `sorry`, `admit`, `native_decide`, or custom `axiom` declaration.
