# Lean handover for Astra — 9 November 2026

The user explicitly requested a complete checkpoint for restarting on another
server. All agents were asked to stop and save their state. No original agent
or build should be assumed to continue on the old machine. The formalization
is **unfinished**. This handover distinguishes the clean verified root, frozen
extensions awaiting promotion, and an unfinished routing draft.

The independent editorial task is documented in [HANDOVER_TEX.md](HANDOVER_TEX.md).
Do not require that agent to solve the mathematical obligations below.

## Bootstrap and current verified snapshot

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
**`7c3c9c209ddfd728c48afb195d4ddaddd1c080a3`**:

- **125 modules** in the `All` import closure.
- **345 independently reviewed exact declaration contracts**, including newly
  reviewed definition contracts, with module and universe-arity checks.
- **2,760 imported project theorem constants** axiom-audited, including generated
  and secondary results. This is not a count of 2,760 source-paper theorems.
- Allowed axioms only: `propext`, `Classical.choice`, `Quot.sound`.

Evidence is in `reports/verification/current/` and archived under
`reports/verification/commit-7c3c9c2/`. Earlier verified snapshots are also
retained. Read the receipt's `source.commit`, exact counts and hashed files; do
not infer a clean verification of later unimported files from a nearby log.
The handover/artifact commit necessarily follows the verified source commit.
The imported source closure and its bound configuration are unchanged.

The published TeX currently has **186 mapped links**, pinned to that verified
commit. It does not yet advertise the unintegrated extensions below.

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

The 125-module root already includes actual affine readouts, a.e. derivative
results, exact modern-activation curvature constructions (including Gaussian
GELU), weak/distributional regularity bridges, CPWL representation with depth
bounds, indexed convolution, explicit split-DAG size bounds, general regularized
pair validity, full stopping-DAG/intermediate gradient occupations, ordered
max-pool ties, layered softplus SPNE, zero-support survival conditioning, and
local attention reference-KL optimization. Consult exact contracts and scopes;
these summaries do not enlarge them.

## Frozen extensions included but not imported by All

### 1. Softplus Circuit extension: ready for promotion

Thirteen new `formalization/Thesis/SoftplusCircuit*.lean` leaves are present.
Their three top imports are:

```lean
import Thesis.SoftplusCircuitUniqueness
import Thesis.SoftplusCircuitVisits
import Thesis.SoftplusCircuitPayoff
```

Producer: `reports/softplus-circuit-repairs.md`.
Contracts: `reports/softplus-circuit-expected-types.json` (**20 contracts**).
Independent review: `reports/adversarial-softplus-circuit-review.json` (**PASS**).
Evidence: `reports/evidence/softplus-circuit-review/` and producer paths in the report.
All 13 sources were independently recompiled; exact module/universe/type checks
and 1,889 imported theorem axiom closures passed. Boundary consumers and the
independent path/saddle/derivative experiment passed.

This extends the actual annotated shared Circuit to entropy-softened activation
nodes while keeping pooling hard. It proves arbitrary-profile saddle bounds,
actual SPNE, source player payoffs, normalized complete canonical trajectories,
source discounts, and input/intermediate gradient–occupation identities.
Preserve the exact boundaries: ordinary hard-pool derivatives require unique
winners; selected occupation remains defined at ordered ties; uniqueness is
proved for `NoPools`; full path law is canonical; path rewards use conditional
expected immediate rewards rather than a separate finer sampled reward-history
datatype. Do not silently claim a.e. hard-pool differentiability or uniqueness
at pooling ties.

Next: integrate the three imports and 20 contracts; update source coverage and
the softplus-forward/gradient mappings to the appropriate exact new declarations;
run the clean committed gate. Current mappings still honestly describe the older
layered scope because this promotion was intentionally deferred for handover.

### 2. Conditioned trajectory composition: one review consumer pending

`formalization/Thesis/ConditionedTrajectory.lean` is frozen at SHA-256
`f981b0b7669441009d6145714d7f5c518869eefae0deaa67671c4d940cfb49fe`.
It composes actual full-path marginals, geometric kernels, normalized BC and
Hellinger formulas with the previously verified zero-support conditioning leaf.
It also proves actual full-prefix BC antitonicity/Hellinger monotonicity.

Producer: `reports/conditioned-trajectory-repairs.md` and
`reports/evidence/conditioned-trajectory/receipt.json`.
Contracts: `reports/conditioned-trajectory-expected-types.json` (**five**).
Production compile, all five exact contracts, 351 imported theorem axiom checks,
and the producer's zero-survival/disjoint-support consumer passed.

Independent report: `reports/adversarial-conditioned-trajectory-review.json`.
It deliberately says **semantic and exact checks pass; boundary consumer pending**.
Independent fresh compilation, explicit checks, and the 161-pair path experiment
passed. The sole remaining independent consumer failure is the finite Bool product
sum in `reports/evidence/conditioned-trajectory-review/Boundary.lean`, theorem
`nontrivial_overlap`, near line 60. Simplify the literal sum over `Paths Bool 2`,
rerun that consumer and `report.py`, then review/promotion can finish. Do not call
that consumer passed merely because the production theorem passed.

Only initial survival must be positive; reachable intermediate zero-survival states
are pruned. No conditioned probability law exists when initial survival is zero.
The source uses varying layers/reversed indices; this leaf uses a common finite
state type and ordinary substochastic kernels. Preserve that representation scope.
Prefix monotonicity is for a fixed pair of full stochastic processes, not a family
of separately survival-conditioned horizons.

### 3. Routing equilibrium-to-backward bridge: unfinished draft

Read **`reports/routing-bridge-handover.md`** first. It contains the detailed proof
route, sign conventions, exact failing checks, dependencies and restore commands.
The two draft files are outside production:

```
reports/evidence/routing-bridge/draft/Thesis/RoutingHistory.lean
reports/evidence/routing-bridge/draft/Thesis/RoutingPolicyBridge.lean
```

`RoutingHistory` compiles: it defines normalized actual full Tree histories for
arbitrary profiles and cumulative-discount observation integrals, with proved
recurrences. It has no independent exact contract/review yet.
`RoutingPolicyBridge` **does not compile**. Its first complete error log and source
hashes are saved in `reports/evidence/routing-bridge/`. Known first problems are
case-proof layout, a finite delta-sum equality orientation, and matching a route
lemma across semireducible function types. No later result is credited as proved.

The intended theorem connects actual canonical game policies/microsteps to the
older alpha-beta path products and occupations, including real intermediate cuts,
empty streams, stabilizer/bias absorption, signed fused inputs, and a forced
ungated affine readout. Eliminating oracle microstates on ordinary surviving
paths is not automatically a full stopped-history law equivalence. The detailed
handover records the distinction. No root, manifest, or TeX imports these drafts.

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

An integrating-agent inspection also flagged a question for future review, not a
confirmed correction: `rem:freg_smooth_connection` should be checked carefully
for whether strict convexity/smoothness of the regularizer alone ensures the
claimed integrable weak curvature of its conjugate. Do not change it without a
precise argument or counterexample and reporting to the user.

## Confirmed prose precision issue to coordinate with TeX

`reports/routing-law-precision-review.json` preserves the source passages and a
concrete one-edge counterexample: with an active ReLU and positive weight 1 versus
2, the normalized stopping-game trajectory is the same but the structural discount
and gradient differ. The paper already states this limitation in its detailed
Hellinger discussion. Intro/conclusion phrases saying Pi alone “is the backward
computation” need qualification to **normalized routing**, with attribution a
model-dependent discounted occupation projection. Hellinger identities on Pi
remain valid. No new Lean witness or source correction was made before handover;
report the proposed prose correction to the user before making it.

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
   public build record, commit artifacts, and push.

The user explicitly authorized the public repository and pushes. Keep private
registration metadata out. Both official code repositories remain pinned
submodules. The Lean proofs certify their stated mathematical models; they do
not certify the Python implementations or regenerate experimental evidence.

Historical evidence may contain absolute old-machine paths. Use the committed
source files, relative paths and pinned toolchain to rerun diagnostics on the new
server. All active work was checkpointed; no unsaved result from an old agent is
needed to continue.
