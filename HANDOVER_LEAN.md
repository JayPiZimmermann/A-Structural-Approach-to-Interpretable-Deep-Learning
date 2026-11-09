# Lean handover — resumed 9 November 2026

The current revision adds convex/monotone activation splitting and an actual
arbitrary-depth Transformer DC algorithm. Those new sources compile and have
separate independent reviews; final assembly integration and the complete clean
gate are still pending. **The formalization as a whole remains unfinished.**
The last completed full gate remains `0f3cfb0` until a newer passing receipt is
recorded below. Six independently reviewed routing-history modules remain outside
the production import closure; this new Transformer work does not promote them.

The independent editorial and empirical state is in [HANDOVER_TEX.md](HANDOVER_TEX.md).
Current changes and official-code repair commits are local only; the user asked
for local execution first. Do not publish this revision under the earlier
checkpoint's push authorization.

## New DC and Transformer work awaiting the final integrated gate

The 15 activation leaves add the nonsmooth profile criterion, absolute-curvature
lift, closed-form GELU/Swish/sigmoid/Softplus pairs, exact ReLU `(max(x,y), y)`,
and complete network composition with an ungated affine readout. The 46 selected
contracts and independent leaf/source reviews are indexed by
`reports/dc-generalization-expected-types.json` and
`reports/evidence/dc-generalization/README.md`. The integration receipt is
`reports/evidence/dc-generalization/integration-receipt.json`.

Four softmax leaves prove the actual exp/log formula, its difference identity,
global convexity and coordinatewise monotonicity, and nonnegativity on expanded
nonnegative inputs. The 24 reviewed contracts are in
`reports/softmax-dc-expected-types.json`. Generic universe metadata was corrected
and passed the enforcing exact driver; use the final explicit-universe contracts,
not a stale copy. `PolarizedProductDC` proves the square-based multiplication pair
and nonnegative-stream composition. `LayerNormDCLift` proves the actual tangent
extension of the reciprocal square root, and `LayerNormDC` assembles the mean,
centered variance, reciprocal, signed scale and bias into input-dependent
LayerNorm. It is not frozen-statistic normalization.

The actual Transformer development uses these source modules:

- `TransformerPairCalculus`: reusable convex, monotone, nonnegative stream
  composition, with signed affine operations and polarized products.
- `TransformerExpr`: actual scalar operation syntax, ordinary evaluation, recursive
  split evaluation, exactness and the structural invariant; no constructor stores
  an assumed certificate for an entire operation.
- `TransformerConvexInput` and `TransformerExprProperties`: expanded nonnegative
  input and global convex raw-input pullbacks.
- `TransformerDefinition`: actual finite pre-LayerNorm blocks, signed Q/K/V and
  output projections, coupled masked softmax, Value products, residual additions,
  supported activation MLPs, positional bias, optional final LayerNorm, and signed
  affine output logits. Blocks form an arbitrary finite list, including zero
  blocks. Masks have nonempty allowed support and injective key enumeration.
- `TransformerCorrectness`: `Transformer.decompose`,
  `Transformer.dc_decomposition`, and `Transformer.raw_dc_decomposition` connect
  the splitting algorithm to the ordinary same-parameter forward computation.

The full Transformer theorem has compiled; independent exact, axiom, source and
boundary reviews and final integration must be read before claiming a passed
production gate. The current primitive integration receipt,
`reports/evidence/transformer-dc/integration/primitives-receipt.json`, records
160 reachable modules, 454 selected contracts and 211 mappings at that intermediate
stage. These are **not final gate counts** and exclude pending assembly promotion.
The integration owner controls roots, coverage, inventory, exact contracts and
source links; do not edit them concurrently with that owner.

Preserve these scope distinctions:

- The softmax pair is convex and monotone on the whole doubled real space. The
  composed Transformer has those properties on the nonnegative doubled-input
  orthant. Pulling back by `(x⁺,x⁻)` gives globally convex, nonnegative raw-input
  heads, without raw-input monotonicity.
- Normalization epsilon is strictly positive; masks are fixed and nonempty.
  Standard LayerNorm remains input dependent in evaluation mode. Fixed-statistic
  BatchNorm is an affine operation and belongs to the simpler existing case.
- The expression compiler and actual architecture theorem do not establish a
  shared-DAG size bound, runtime bound, numerical stability, full attention-game
  equilibrium, or unconditioned Query/Key attribution identity.
- The absolute-curvature theorem's displayed normalization is a mathematically
  equivalent variant of the reviewed normalized integral construction. Its
  coverage records the missing literal-formula bridge. Global necessity and
  bounded-interval extensions are not silently covered by a sufficient-condition
  kernel theorem.

The runnable float64 diagnostic `scripts/transformer_dc_demo.py` independently
compares a small post-LayerNorm Transformer with ordinary PyTorch. It is not the
pre-LayerNorm architecture record's execution certificate. Its 20-case receipt
retains severe cancellation: 15 cases exceed `1e-8` final error, and streams reach
`5.95e111` at small epsilon. Read
`reports/evidence/transformer-dc/numeric-review.json`; exact DC existence does not
supply a practical stable Transformer implementation.

The reviewed game-prose additions now explicitly handle signed affine logits and
zero-mass cemetery completion. Local official-code fixes have 48 boundary tests,
but they are separate from a full global Lean attention-game proof. Code pins are
HM `43a8bce45ac1d61b28dfa5ddc7eaf32e8ad35f4f` and game
`7b5cd387f0a690b0d3451aa60bc8d897bd442a38`; see the TeX handover for 27 HM tests,
23 subtests, 33 statistical tests, 13 regenerated tables and historical limitations.

The subsequent real-ViT implementation, stabilization and heatmap request is a
separate active empirical task in a local HM worktree based on `43a8bce`.
It does not change the thesis submodule pin or enlarge the present Lean theorem's
numerical guarantees. No real-ViT execution result is claimed here yet.

## Bootstrap and last completed verified snapshot

```sh
git clone --recurse-submodules https://github.com/JayPiZimmermann/A-Structural-Approach-to-Interpretable-Deep-Learning.git
cd A-Structural-Approach-to-Interpretable-Deep-Learning/formalization
lake exe cache get
lake build All
python3 scripts/verify.py
```

Install Lean's `elan` beforehand. `lean-toolchain` pins **Lean 4.35.0**;
`lake-manifest.json` pins **mathlib v4.35.0** and transitive dependencies.
Do not run `lake update` merely to bootstrap. Use the shared downloaded dependency
cache, but do not copy stale `.olean` files from the previous machine.
Build sequentially on a 16 GB machine. Independent agents may run targeted
diagnostics into separate directories; do not run competing full builds or let
them write the same production artifacts.

The last complete clean gate passed at source commit
**`0f3cfb0ea660556c14da510e665281f07acc471d`**:

- **139 modules** in the `All` import closure.
- **370 independently reviewed exact declaration contracts**, including newly
  reviewed definition contracts, with module and universe-arity checks.
- **3,048 imported project theorem constants** axiom-audited, including generated
  and secondary results. This is not a count of 3,048 source-paper theorems.
- Allowed axioms only: `propext`, `Classical.choice`, `Quot.sound`.

Evidence is in `reports/verification/current/` and archived under
`reports/verification/commit-0f3cfb0/`. Earlier verified snapshots are also
retained. Read the receipt's `source.commit`, exact counts and hashed files; do
not infer a clean verification of later unimported files from a nearby log.
The handover/artifact commit necessarily follows the verified source commit.
That historical snapshot remains immutable; the current working root and bound
configuration have since changed and require the new gate described above.

The previous published TeX has **190 mapped links**, pinned to that verified commit.
It includes the two integrated batches and does not advertise the unimported
routing extension. The source normalization from `e42fe47` to `0f3cfb0` changed
only JSON order/encoding: all 190 mapping values were identical. The independent
promotion review, `reports/lean-frozen-promotion-review.json`, records the final
source hashes and this normalization. All 140 clean-gate commands exited zero;
the source/configuration snapshot was unchanged throughout the run.

The previous `current` receipt and every referenced artifact/log were confirmed
identical to the `commit-7c3c9c2` archive before refreshing `current`. Unreferenced
older logs may remain there; the receipt's command list and hashes are authoritative.

## User requirements and proof discipline

Formalize all mathematics of both papers and the thesis, especially every
backward identity. The thesis statements should appear as readable Lean theorems,
using simple shared definitions. Cheap agents are appropriate for routine
editorial/inventory work; use strong agents for Lean and mathematical review.
Independently attack proofs, assumptions, boundaries, and source correspondence.

Read and apply the downloaded instructions under `skills/upstream-planar-features/`:
`formalization-architecture`, `formalization-build`, `formalization-certificates`,
`formalization-conventions`, `formalization-research`, and `math-exposition`.
Their source URLs/hashes are recorded in that directory. The user's explicit
instructions take precedence.

- No `sorry`, `admit`, new axioms, or `native_decide` in production proofs.
- A successful Lean build verifies the encoded statement, not its correspondence
  to the paper. Do not assume the result as a field/hypothesis or verify a surrogate
  recurrence while claiming an actual game, network, path law, or derivative.
- State exact universes, implicit parameters, hypotheses and defining module in
  manually authored full-forall contracts. Do not generate the expected statement
  from Lean's printed inferred type and call that an independent check.
- Keep frozen reviewed leaves immutable. Extend with new leaves and import them
  only after review. Only the integrating agent edits roots, coverage, manifest,
  and TeX mapping files.
- Report mathematical errors to the user before correcting source papers.
  Preserve the original prose as much as possible outside necessary corrections.
- “Caveat free” means closing real gaps, not suppressing necessary hypotheses or
  disguising a component as a proof of a complete source theorem.
- The routing game requires non-negative activations. GELU's routing argument is
  local. All activation **log-space ties select stopping**, with original
  extended-log utilities preserved. Do not replace them with real `log 0 = 0`.
- Ordinary trajectory probabilities are non-negative and normalized. Structural
  discounts can exceed one. Discounted occupations and their signed differences
  are separate objects, and may not be probability measures.
- At nonsmooth gates/pool ties, distinguish a selected backward quantity from an
  ordinary derivative. Do not impose unnecessary strictness where degeneracy
  permits a real derivative, or silently drop the strictness a proof needs.

## Shared mathematical architecture

`formalization/README.md` explains the main types and modules. Important anchors:

- `HiddenMonotonicity.Network n m`: one finite varying-width MLP with split
  weights/biases, ordinary evaluation, pair decomposition, and explicit ungated
  signed affine readout. Zero input width and zero rows are meaningful cases.
- `Circuit` and `SignedExpr`: actual finite shared DAG syntax. References preserve
  sharing; graph cuts retain the actual prefix table. Avoid replacing it with an
  unrelated recurrence or double-counting a shared subgraph.
- `Row`, `Sensitivity`, `MaskedTrace`, `OriginalTrace`: genuine continuous linear
  maps, pair sensitivities, extracted gates and actual matrix products.
- `unified`: half the difference of the two input-stream sensitivities. The balanced
  input lift is `(x/2,-x/2)`. Shifted backward quantities are algorithmic, not
  automatically derivatives of input-dependent recentering.
- `QSource`/`QSources`/`PrefixSources`: actual auxiliary functions and their proved
  derivatives, including common full-measure statements.
- `Thesis.Games`: finite path laws, dynamic programming, overlap/Hellinger,
  terminal-fibre decomposition and conditioning.
- `RoutingProfiles.Tree` and `RoutingNetwork`: actual game/profile objects and
  canonical equilibrium with extended log payoffs. `RoutingBackward` separately
  provides alpha-beta path recovery; their missing explicit bridge is the WIP below.

The historical 139-module root already includes actual affine readouts, a.e. derivative
results, exact modern-activation curvature constructions (including Gaussian
GELU), weak/distributional regularity bridges, CPWL representation with depth
bounds, indexed convolution, explicit split-DAG size bounds, general regularized
pair validity, full stopping-DAG/intermediate gradient occupations, ordered
max-pool ties, layered softplus SPNE, zero-support survival conditioning, and
local attention reference-KL optimization. Consult exact contracts and scopes;
these summaries do not enlarge them.

## Extensions already integrated in the last verified root

### 1. Softplus Circuit extension

All thirteen `formalization/Thesis/SoftplusCircuit*.lean` leaves are imported by
`Thesis.lean` through:

```lean
import Thesis.SoftplusCircuitUniqueness
import Thesis.SoftplusCircuitVisits
import Thesis.SoftplusCircuitPayoff
```

Their twenty independently reviewed contracts are in `verification.json`.
The frozen producer contracts remain in `reports/softplus-circuit-expected-types.json`;
independent semantic/boundary review is
`reports/adversarial-softplus-circuit-review.json`. Production source bytes were
not changed during promotion. Coverage, both source/thesis inventory records,
and the reviewed forward/gradient mappings now describe the actual Circuit scope.

This extends the annotated shared Circuit to entropy-softened activation nodes
while keeping pooling hard. It proves arbitrary-profile saddle bounds, actual
SPNE, source player payoffs, normalized complete canonical trajectories, source
discounts, and input/intermediate derivative–occupation identities. Preserve the
boundaries: ordinary hard-pool derivatives require unique winners; selected
occupation remains defined at ordered ties; equilibrium uniqueness requires
`NoPools`; full path laws are canonical. Expected path payoffs use conditional
expected immediate rewards, without a separate finer sampled reward-history
datatype. No a.e. hard-pool differentiability or arbitrary Network-to-Circuit
compiler equivalence is claimed.

### 2. Conditioned trajectory composition

`formalization/Thesis/ConditionedTrajectory.lean` is imported and its five
reviewed contracts are in `verification.json`. The source remains frozen at
SHA-256 `f981b0b7669441009d6145714d7f5c518869eefae0deaa67671c4d940cfb49fe`.
It composes actual full-path marginals, geometric kernels, normalized BC/Hellinger
formulas, and full-prefix overlap antitonicity/Hellinger monotonicity with the
previously verified zero-support conditioning leaf.

The independent `nontrivial_overlap` consumer was repaired by exposing the
`Bool × (Bool × Unit)` sum domain. The complete consumer compiled with exit zero;
its original failure evidence is retained as `boundary-before-resumption.*`.
See `reports/evidence/conditioned-trajectory-review/boundary-resumption.json` and
`reports/adversarial-conditioned-trajectory-review.json`, now
`pass_with_explicit_scope`. The report writer now checks recorded exit statuses
instead of manufacturing success from an error-string search.

Only initial survival must be positive; intermediate dead states are pruned.
No normalized conditional law exists at zero initial survival. The representation
uses a common finite ordinary state type; explicit cemetery completion and
varying-layer state embeddings remain separate. Prefix monotonicity concerns a
fixed pair of full stochastic processes, not separately conditioned horizons.

## Reviewed routing extension awaiting production promotion

Read **`reports/routing-bridge-handover.md`** and
`reports/routing-bridge-resumption.json`. The old failing policy draft was repaired;
its saved failure log is historical, not the live frontier. Six frozen sources
remain under `reports/evidence/routing-bridge/draft/Thesis/`:

- `RoutingHistory`: normalized actual full game histories and discounted observations.
- `RoutingPolicyBridge`: actual canonical policy ratios and complete microstep pushforward.
- `RoutingPolicyPaths`: ordinary surviving policy products and source discounts.
- `RoutingHistorySteps`: full-history first-step marginals, including cemetery mass.
- `RoutingObservations`: actual full-history input/intermediate occupation and alpha-beta recovery.
- `RoutingReadoutHistory`: a forced ungated affine readout, including negative outputs.

Independent review **passed**: all six fresh source compiles, **20 independently
stated exact contracts**, **919 imported theorem axiom closures**, and the Lean
boundary consumer. The separate rational experiment checked 168 cases and
5,208 histories. This is focused diagnostic evidence, not a clean production gate.

Use exactly the twenty targets in
`reports/evidence/routing-bridge/review/expected-types.json` for promotion. The
producer checks have fourteen targets; eleven overlap the independent set,
so their union has twenty-three. Three producer-only targets are listed explicitly
in the routing handover and need independent exact checks before becoming extra
headline targets. Do not repeat the superseded twenty-eight-contract estimate.

The architecture is a layered Network. Signed raw inputs are fused in the first
layer; hidden activations are nonnegative; stabilizer epsilon may be zero; log
ties stop. Ordinary products, full first-step marginals and full canonical
occupations are separate results, not a blanket macro/full-history law equality.
The affine readout backbone outputs must be nonnegative, automatic for a nonempty
activated backbone. A negative zero-depth input requires a separate fused
readout. Residual/pooling routing DAGs remain outside this batch.

A separate queued Lean task, after the current DC/Transformer gate, is to copy
these six sources byte-for-byte into
production, add `RoutingPolicyPaths`, `RoutingHistorySteps`, and
`RoutingReadoutHistory` to `Thesis.lean`, integrate the twenty reviewed contracts
and exact mapping scopes, commit, and run a new clean gate. Do not repin TeX to
this extension before that gate passes. This routing batch has not been promoted by the current DC/Transformer work.
Its focused receipts must not be confused with either full production gate.

## Other outstanding mathematical work

Use `formalization/coverage_map.json`, `claim_inventory.json`, and
`reports/lean-link-coverage-review.json` as inventories, not completion certificates.
The link audit classified every active labelled display/result and recorded
remaining representation/contract gaps. Notable remaining work includes:

1. **Gaussian/probit noisy-gate duality** (`lem:noisy-gate-dual`): the old unrelated
   softplus link was removed. Prove the actual Gaussian-smoothed ReLU expectation
   and probit regularizer conjugacy, including endpoint conventions. Existing
   `ModernGELU` supplies the real Gaussian density/CDF and derivatives.
2. **Full attention game**: the local reference-KL value/policy theorem is checked,
   including zero support and all-zero total. Whole attention SPNE, inactive-player
   bookkeeping, absorption and occupation composition are not yet bundled/proved
   by that local result.
3. **Concrete randomization models**: conditional affinity/alive-probability
   contraction theorems exist; derive their assumptions from the actual randomized
   weights, including conditioning/measurability. Do not replace a deterministic
   source row bound by an unmentioned expectation hypothesis.
4. **Architectural/source bridges**: arbitrary game DAG to network embedding,
   complete concrete CNN architecture assemblies, remaining routing residual/pool
   cases and varying-state-space embeddings. Shared local convolution/pool/DAG
   results exist but do not silently discharge every architecture theorem.
5. Review source definitions/remarks and unlabelled mathematical displays as well
   as named theorems. The named coverage map is not a complete audit of every
   mathematical sentence in the thesis.

## Prose precision corrections during resumption

The normalized routing law alone does not determine backward magnitudes: positive
one-edge ReLU weights 1 and 2 have the same normalized route and different
structural discounts/gradients. The TeX task qualified the affected broad claims
to normalized routing and model-dependent discounted occupation projections.
`reports/routing-law-precision-review.json` preserves the original counterexample;
Hellinger identities on the normalized law are unaffected.

The suspected issue in `rem:freg_smooth_connection` was confirmed and reported
before the TeX correction. Smooth strict convexity of the regularizer alone can
leave a singular curvature measure in its conjugate. The corrected connection
to the L1-curvature theorem requires the gate to be locally absolutely continuous;
positive interior second derivative of a C2 regularizer is sufficient.
`reports/regularizer-curvature-review.json` records the counterexample, endpoint
argument and independent handwritten review. This argument is not a new Lean
certificate, and existing general-regularizer theorem scopes were not changed.

## Promotion and publication workflow

1. Keep task-owned new leaves separate. Finish exact contracts and independent
   review, including zero/tie/empty/readout counterexamples. Freeze source hashes.
2. Merge only reviewed imports/contracts. Preserve explicit source scope in
   `coverage_map.json` and `tex_links.json`; do not retain stale manual mapping
   scopes after upgrading a result. `review_id` mappings override auto-selected
   coverage links in the synchronizer.
3. Commit the new source closure and bound configuration. Run
   `python3 scripts/verify.py` from `formalization/` with HEAD and bound files fixed
   for the entire run. The script builds all imported modules, elaborates exact
   contracts independently and audits every imported project theorem's axioms.
   `--diagnostic` is for explicitly labelled development evidence, not a clean
   publication claim.
4. Archive passed evidence before starting another run. Complete proof source
   commits can precede an artifact commit; do not attempt a self-referential
   receipt claiming its own artifact commit was the source snapshot.
5. Give the TeX task the verified commit. Run the link generator/check against it,
   rebuild the public PDF, verify rendered links and bibliography, update the
   public build record, and commit artifacts locally. Keep the present revision
   local until publication is authorized for it.

Earlier checkpoint publication was authorized; the current revision is local
first and has not been pushed. Keep private registration metadata out. Both official code repositories remain pinned
submodules. The Lean proofs certify their stated mathematical models; they do
not certify the Python implementations or regenerate experimental evidence.

Historical evidence may contain absolute old-machine paths. Use the committed
source files, relative paths and pinned toolchain to rerun diagnostics on the new
server. The current integration is still active; use completed receipts and frozen
source hashes rather than assuming every nearby working file is verified.
