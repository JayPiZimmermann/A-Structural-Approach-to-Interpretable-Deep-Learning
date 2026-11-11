# TeX handover for Astra — 11 November 2026

The user requested this checkpoint so the thesis can be continued on another
server. This document is sufficient to start the TeX task independently. The
mathematical continuation has a separate [Lean handover](HANDOVER_LEAN.md).

## Current local revision and verification boundary

The single-PDF consolidation starts from `b43bc24`. The earlier thesis and cover
checkpoint, `61d4d90`, tightens the author's new introduction, removes pasted chat
text and duplicate drafts, reduces the contribution list to an overview, and
removes roughly 4,000 words of unused tropical/polyhedral background. The
Transformer DC algorithm is stated briefly in the existing DC contribution.
The subsequent reference audit checks all 190 original bibliography entries and
405 citation contexts. Its portable evidence, corrected source identities,
claim resolutions, and full-text access limits are in `reports/reference-audit/`.
The retained BibTeX entries link to primary sources and checksum-identified local
files in the ignored `literature/references/` directory; full texts are not
redistributed through Git. Four unverified records with wrong identifiers are
quarantined in the audit ledger. The source-paper archives remain unchanged.
The audit follow-up has passed the final build, warning, citation-provenance
and publication checks recorded in `reports/publication-build.json`. Full publication builds enable both rendering switches; the current temporary review setting is described below.

The subsequent literature update adds eleven references with short, scoped
comparisons across five chapters. Selection, placement, metadata, and source
access are recorded in `reports/recent-literature/`. Ten selected PDFs are stored
locally; GEF remains unavailable as a local full text and was checked through
indexed primary-source excerpts. The earlier 190-entry audit remains a historical
record, separate from this update. Quantus is one sentence in the existing metrics
paragraph, with no separate paragraph or taxonomy catalogue.

The subsequent prose-concision pass reduces main and supplement prose by roughly
17% while preserving their order, displayed equations, labels, and citation keys.
The chapter ledgers, independent proof and qualification reviews, source audit,
and build evidence are in `reports/prose-concision/`. Its baseline includes the
author's uncommitted introduction edit; the parent commit and exact patch are
recorded. The MNIST section and introduction now motivate directly trained
difference models as a study of the opposing-stream mechanisms exposed by
pretrained-network decomposition. This pass changes proof exposition, not Lean
source or numerical experiment results.

The generalized convex/monotone DC construction, closed-form activation and
softmax splits, arbitrary-depth Transformer definition and splitting algorithm,
and requested review repairs remain. The complete clean Lean gate passed at
source commit `1f886dd524d0c9f3b38192a55fd7cfa5a20dfe06`: **167 modules,
490 independently reviewed exact contracts and 3,640 imported project theorem
axiom audits**. All 168 commands exited zero. Evidence remains in
`reports/verification/commit-1f886dd/` and `reports/verification/current/`;
the previous `0f3cfb0` gate is archived.

The consolidation merged the former 123-page thesis and 80-page supplement
into **one 147-page PDF**, with proofs in their chapters and extended experiments
in appendices. Adding the completed ViT extension produced a 148-page full build.
The target remains 150 pages. On 11 November the user requested restoration of
the longer Section 1.1 and temporarily disabled tables and qualitative image
grids for text review. The restored section follows the pre-compression wording
and paragraph order, retaining the requested question of what explanations
explain, a brief white-box/black-box distinction, and the revised MNIST motivation.
The current PDF is therefore a text-review draft, not a full-content page-budget
measurement. Treat `reports/publication-build.json` and its referenced
`reports/introduction-restoration/` checks as authoritative for this copied PDF;
`reports/single-pdf/` records the earlier consolidation.
The introductory figure uses a compact layout. Static `tex/main.xmpdata` supplies PDF metadata for reproducible builds without
metadata-generation warnings.

The unused geometry section has no downstream technical dependencies. Its
22 mapped statement/equation labels are explicitly retired in
`tex/preamble/lean_links_retired.json`; the checked Lean library, pinned mapping,
and stable badge numbers are retained. Before consolidation the two PDFs contained
194 active Lean link occurrences covering 123 unique targets; the current
publication guard records retained targets and deduplicated occurrences. Active and
retired labels together account for all 216 pinned mappings. The publication
guard checks the exact active PDF link occurrences and internal reference targets,
while all **176 proof-bound files** must still match the verified source hashes.
No Lean source or proof-bound metadata was changed by this editorial work.

The earlier compression audit against `91d4d27` remains historical evidence:
that revision accounted for all 804 original content blocks and preserved all
314 displayed formulas, with no substantive loss found by independent reviewers.
Its crosswalks remain under
`reports/evidence/page-budget/{text,math,evidence}-retention.json`. Those claims
must not be read as a retention assertion for this later, explicitly requested
removal of unused geometry exposition and formulas.

Build only `tex/main.tex`. Detailed game, attention, and trajectory proofs are
integrated into their chapters; extended experiments are included as appendices.
The separate supplement root is retired. `reports/single-pdf/` records the
consolidations and independent retention reviews. Compact tables belong beside
their discussion; only extensive matrices and sweeps remain in appendices.
The complete ViT comparison is printed once in the main results chapter.
At the consolidation checkpoint, counted chapter, appendix and abstract prose fell by 23.8%
against `b43bc24`; the count excludes separately input table/figure text and the
bibliography. That checkpoint retained all 618 original label names, 153 citation
keys and 194 figure assets. The later user-requested removal of the peripheral
functional-identifiability clause removes its citation from the introduction;
the bibliography record remains. Repeated statements use canonical labels and reviewed aliases. The RG
recovery claim was also corrected: ungated $\alpha\beta$-LRP recovery covers the
stated affine/ReLU-chain or positive-support cases; the residual extension uses
explicit activation gates. Its forward addition identity retains unit temperature
and the active-player condition. See `reports/single-pdf/integration.json` for the
source-bound retention evidence and this intentional mathematical correction.
`python3 reports/single-pdf/build_experiment_views.py --check` verifies the
merged duplicate rows and the cross-model validation-rank matrix.
Reference coverage now reports **67 of 74 HM source labels retained**, with
six labels for three removed geometry-background references and one unsupported
biological-plausibility citation intentionally omitted. Their bibliography
records remain. The reasons are recorded in
`reports/paper-reference-editorial-omissions.json` and
`reports/paper-reference-reviewed-corrections.json`. All **72 game-paper source
references** remain. The corrected ImageNet-S citations use one canonical key,
`gao2022luss`, so that the bibliography contains one entry for that work. The checker distinguishes these reviewed omissions from
unexplained missing citations and continues checking bibliography entries and
aliases. The source-reference checker and badge synchronizer follow the single active
source tree. Deliver `docs/thesis.pdf`; all thesis references resolve internally.

### Quantus extension integration

`scripts/complete_vit_extension.py --watch --publish` watches the local CAM and
SplitCAM campaigns and adds completed results at the reserved marker in
`tex/chapters/08_experiments.tex`. The extension uses the existing ten-column ViT
CI layout, copied Gradient values, and freshly computed displayed-family paired
tests with Holm correction. It first includes fixed-attention/fixed-LayerNorm
SplitCAM, then the completed adaptive-policy ablations. Incomplete results stay
out of the thesis. Builds run in an isolated snapshot and must pass the existing
150-page publication guard before replacing the local PDF; the watcher does not
commit or push.

Exclude all ViT DC backward-shift alpha ablation tables and figures from the
thesis (user instruction, 11 November 2026). None are present in the current
PDF: the extension contains only validation-selected configurations. Keep their
selected alpha values for reproducibility. The original VGG-16 alpha ablations
and the game-method ablations are distinct and remain in scope.

The user rejected the ten qualitative candidates on 11 November 2026:
do not include these comparisons in the thesis. The files in
`reports/vit-extension/qualitative/` and later releases are diagnostic archives
only. `reports/vit-extension/latest-artifacts.json` points to updated
renders after publication. Read `reports/vit-extension/status.json` and
`watcher.pid` for live state, and `completion-coordinator.txt` for restart and
retry commands. Cooperating manual builds must take the persistent
`reports/vit-extension/tex-build.lock`; do not delete lock files. The coordinator
preserves concurrent edits and records each publication in the main receipt.

### DC terminology

Use **DC decomposition** for the construction, **split-pair** for $(g,h)$,
**split-streams** for its components, and **split network** for the implementing
network. Section 1.1 defines these terms. Use **split-stream activations** and
**split-stream gradients**; keep stopping decompositions and general activation
pairs distinct. See `reports/dc-terminology/consistency.json` for the source check.

### Independent rendering switches

`tex/preamble/rendering.tex` defines `\RenderTables` and
`\RenderQualitativeImageTables`, currently both set to `0` for the user's
temporary text review (11 November 2026). A value of `0` omits the content while
retaining a compact placeholder, the full caption,
the list entry and the label. The first controls regular tables, including the
result longtables. The second controls
the six qualitative image grids; ordinary diagrams, plots and acronym lists are
unaffected. The switches apply independently throughout the complete thesis.

For a temporary command-line override, use an isolated build directory with the
TeX source subdirectories linked into it, then invoke, for example:

```sh
pdflatex -interaction=nonstopmode -halt-on-error -jobname=main \
  '\def\RenderTables{0}\def\RenderQualitativeImageTables{1}\input{/absolute/path/to/tex/main.tex}'
```

Settle the single document's cross-references. Keep draft auxiliary files and
PDFs separate from the normal publication build. All four switch combinations are covered by the evidence in
`reports/evidence/rendering-switches/`; restore these settings for the final full publication:
`\RenderTables=1` and `\RenderQualitativeImageTables=1`.

After copying the compiled PDF, run from the repository root:

```sh
python3 reports/evidence/page-budget/verify_publication.py
```

This checks the 150-page target, final log, PDF/source equality, Lean
URIs, internal destinations, and unchanged proof-bound source hashes.
The final result belongs in `reports/publication-build.json` and the single-PDF
evidence directory. Earlier page-budget reports document the historical layout.

The two revised source papers already compile independently: Hidden Monotonicity
has 38 pages and Playing the Network Backward has 83 pages. References and
citations resolve, and comparison with `afcbb42` found no newly introduced
layout warnings. Existing source-paper overfull boxes remain recorded in
`reports/evidence/paper-builds/`; this does not certify the separate thesis build.

## Mathematical and editorial changes

Chapter 03 now starts the DC development with the generic convex, monotone
profile criterion and network composition theorem. Its absolute-curvature
construction covers smooth activations; explicit GELU, Swish, sigmoid and
Softplus formulas recover ReLU exactly as `(max(x,y), y)`. The final classifier
layer is an ungated signed affine readout. The earlier symmetric construction
remains a separate variant, and the smooth section has moved from Chapter 02.

The new softmax pair is globally convex and coordinatewise monotone on the
expanded space. Chapter 07 combines it with square-polarization products and
input-dependent positive-epsilon LayerNorm. It defines a finite pre-LayerNorm
Transformer with fixed nonempty attention masks, arbitrary block-list depth,
optional final normalization, and signed affine logits, then gives the recursive
splitting algorithm. The whole Transformer heads are convex, monotone and
nonnegative on **nonnegative doubled inputs**. Their positive/negative raw-input
pullbacks are globally convex and nonnegative, but generally not monotone.
LayerNorm still uses input statistics in evaluation mode; fixed-statistic
BatchNorm is the affine case.

Keep the numerical limitation prominent. The post-LayerNorm diagnostic in
`scripts/transformer_dc_demo.py` is a separate instance of the same primitive
construction, not the precise pre-LayerNorm record used by the formal assembly.
Of 20 deterministic float64 cases, 15 exceed `1e-8` final absolute error; all
six tested epsilon `1e-5` cases lose output accuracy and stream magnitudes reach
`5.95e111`. A benign fixture is accurate to `2.78e-17`. All cases are retained in
`reports/evidence/transformer-dc/numeric.json` and its independent review.
Exact real-arithmetic decomposition does not establish a stable implementation.

Both source papers and thesis now distinguish full-model score changes from
individual-stream sensitivities, weak rank association from independence,
non-rejection from equivalence, and localization from faithfulness. The game
presentation explicitly bridges signed affine output logits and defines zero-mass
routing by cemetery absorption. Unit-seeded released routing is distinguished
from signed logit-seeded LRP. Runtime prose states the measured 14–29-fold cost
relative to ordinary Grad-CAM/LayerCAM, actual timer/setup scope, and unresolved
historical hardware, precision and Guided Grad-CAM/Guided LayerCAM label provenance.
Dataset exclusion flow, explanation targets, scalar channel-feature Pixel
Flipping and its baseline are aligned with the inspected implementations.

Publication provenance remains explicit: **Hidden Monotonicity is a CVPR 2026
Highlight; Playing the Network Backward is an arXiv preprint (v2)**. Thanks to
Wojciech Samek for the Responsible AI lecture are retained. The introduction and
provenance appendix now state the author's reported roles: developing theory,
developing and conducting experiments, writing all appendices and most paper text
outside the introductions. The original game-paper AI statement is historical;
the separate thesis disclosure records Codex assistance with mathematical proof
development, formalization, code, statistics and writing. Historical AI products
and software/model versions still require factual author input; do not invent them
or silently weaken the declaration's disclosure requirements.

## Review repairs and empirical evidence

The [twelve academic reviews](reports/thesis-reviews/README.md) and
[master's-level assessment framework](reports/thesis-reviews/assessment-criteria.md)
remain historical review snapshots. The current resolution audit is
`reports/thesis-reviews/resolution-audit.json`: 13 specific findings are resolved
at their stated scope, and five areas remain partial. Those are historical
experimental artifacts, AI identifiers, historical timing provenance, conflicting
VGG values, and stronger fixed-rule numerical-stability evidence. Do not rewrite
the old reviews to suggest their findings never existed.

The official repositories remain pinned submodules, with local committed repairs:

- Hidden Monotonicity: `43a8bce45ac1d61b28dfa5ddc7eaf32e8ad35f4f` on
  `thesis-local-reproducibility`. **27 tests and 23 subtests pass**. Repairs include
  executable instructions/API examples, precision propagation and timing metadata,
  independently measured Pixel Flipping initial scores, and deterministic 90/10
  training-pool validation with test data used only after fitting. The default
  validation seed is 42 and independent of model initialization. Final-epoch
  evaluation is explicit; no best-checkpoint reload is implied. Evidence:
  `reports/evidence/hm-reproduction-repair/summary.json`.
- Playing the Network Backward:
  `7b5cd387f0a690b0d3451aa60bc8d897bd442a38` on
  `local/voc-image-cluster-inference`. **33 statistical tests** and **48 routing
  boundary tests** pass. Zero-denominator linear, convolution and attention
  routing is defined; positive-epsilon regression outputs are bit-for-bit
  unchanged. Evidence: `reports/evidence/routing-boundaries/receipt.json` and
  `reports/evidence/voc-cluster-repair/`.

VOC uncertainty now resamples 2,293 original images, preserving all 2,743
image–class records and method pairing. The record-weighted estimand is unchanged.
The 10,000-resample CPU reaggregation leaves all 126 finite means, winners and
120 VOC winner-comparison decisions unchanged. Interval widths change by a median
+1.47%; 94 intervals differ at displayed precision. Holm correction now uses the
full eligible method-pair family before extracting winner comparisons; ten
ImageNet comparisons become non-rejections, and the prose reflects that change.
All ImageNet intervals and all point estimates remain unchanged.

Strict regeneration and canonical checks pass for **all 13 supported outputs**.
Adapted outputs are in thesis tables, and exact raw outputs are mirrored into the
archived game source. See `reports/evidence/voc-cluster-repair/table_integration.json`
and `reports/table-adapter-verification.json`. No pretrained-model reevaluation
was needed for this reaggregation. Six game diagnostic outputs, historical HM
per-image inputs/environment and six historical MNIST configurations remain
unavailable. CPU fixtures and the notebook-derived example do not reproduce those
historical campaigns. The duplicate VGG configuration values are retained with
an explicit provenance limitation, not an invented cause.

The earlier routing-law and regularizer-curvature corrections remain valid:
`reports/routing-law-precision-review.json` and
`reports/regularizer-curvature-review.json` record them.

## Completed real-ViT implementation campaign

The official HM worktree `/home/jzimmermann/code/hidden-monotonicity-transformer-dc` contains the completed experiment on
branch `research/transformer-dc-stabilization`. Its execution commit is
`aa2d8c2d46744d7fee8ada2ac66be4d4534dd888`; final analysis/rendering is at
`5dd534989463b3e690b900f6a2ca3021213cf79f`. The final artifact commit is
`4c02ba66c681437b03a6bd76fad1cae24f45da4e`; the worktree is clean. These are
local commits. The thesis submodule remains pinned to the separately validated
repair commit `43a8bce`. The committed
`reports/vit_dc_comparison/README.md` gives reproduction commands; read its
`campaign_receipt.json` and `reports/vit_dc_baselines/final_campaign_audit.json`
for the execution and independent review.

The campaign evaluated torchvision ViT-B/16 IMAGENET1K_V1 on six fixed paper
qualitative images, at alpha 0, 0.25, 0.4 and 0.5: **24 split cases and 36 freshly
computed baseline maps**. Five images are from validation and one from test;
this is not a new benchmark. The maximum absolute reconstruction errors are
`5.329e-15` for logits, `1.353e-15` for separately computed stream-head gradient
reconstruction, and `6.523e-16` for intermediate gradients. There is no activation
assimilation, gradient assimilation or reference-score substitution.

The stable calculation uses canonical forward recentering and shifted/capped
algorithmic stream sensitivities. It does **not** preserve the original convex
heads' individual derivatives. At alpha 0.4, SplitCAM differs from the ordinary
activation-times-gradient control by only **0.0040–0.279% relative L2**;
SplitGrad differs from the ordinary mean-layer-gradient control by 0.014–0.478%.
Half-shift controls match to roundoff. Accurate reconstruction is established;
improved attribution quality is not. Alpha 0 still uses the adaptive gain cap
and must not be presented as the raw unshifted DC gradient. Naive local DC pairs
remain ill-conditioned, with a recorded local identity error as large as 32,771.

The final receipt verifies the persisted arrays and rendered artifacts. Direct
local review links:

- [Red fox in snow detail](/home/jzimmermann/code/hidden-monotonicity-transformer-dc/results/vit_dc_comparison/comparison/red_fox_snow_detail.png).
- [Six-image method comparison](/home/jzimmermann/code/hidden-monotonicity-transformer-dc/results/vit_dc_comparison/comparison/method_comparison.pdf).
- [Machine-readable numerical summary](/home/jzimmermann/code/hidden-monotonicity-transformer-dc/results/vit_dc_comparison/comparison/summary.json).

Keep the original synthetic instability diagnostic and this stabilized campaign
separate. Neither the empirical checks nor the close agreement with gradient
controls enlarge the Lean theorem or establish faithfulness.

## Start here

```sh
git clone --recurse-submodules https://github.com/JayPiZimmermann/A-Structural-Approach-to-Interpretable-Deep-Learning.git
cd A-Structural-Approach-to-Interpretable-Deep-Learning
```

The title is **A Structural Approach to Interpretable Deep Learning**. The
subtitle is **From DC Decompositions to Two-Player Games**. Use the clone root;
old absolute paths in historical evidence refer to the previous workstation.

Install TeX Live with the packages used by `tex/preamble/packages.tex`, `latexmk`,
Biber, MakeIndex, Python 3, and Poppler utilities. On an Ubuntu server, a full
TeX Live installation is the least complicated option. Build from `tex/`:

```sh
cd tex
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
makeindex main.nlo -s nomencl.ist -o main.nls
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The public cover deliberately has an empty `\mymatriculationnumber` in
`tex/preamble/meta.tex`. Do not replace it with metadata or a PDF from the old
private workspace. `docs/thesis.pdf` is built from this public source tree. Rebuild after moving
labels or changing references.

## User requirements that remain binding

- Merge the motivation, insights, and content of both papers. The central
  motivation is reliable inspection of vision models and shared visual grounding
  with human perception. Attribution helps assess whether predictions rely on
  intended evidence; targeted correction follows diagnosis and needs separate
  validation. Preserve original paper formulations wherever possible;
  do not paraphrase sentences merely to restate them. Avoid duplicate material.
- Deliver ONE PDF containing all substantive material. Integrate proofs into
  the current chapters and extended experiments into appendices; remove duplicate
  exposition and simplify proofs. Aim at or below 150 pages without silently
  deleting scientific content or shrinking typography.
- Preserve every source-paper reference, experiment, figure, table, and substantive
  point in the integrated thesis. Source corrections and a common notation are intentional exceptions to
  verbatim preservation. The reference checker assesses the active source tree and preserves all 74
  Hidden Monotonicity and all 72 revised game-paper source keys.
- Use **interpretability** in authored prose in place of XAI/explainability.
  Retain official publication/method titles, quotations, URLs, and code identifiers.
- Use one spelling/name per object. The spelling policy is executable in
  `scripts/normalize_thesis_terms.py`. Do not merge different objects: in particular,
  the DC and stopping decompositions differ, and the two Pixel Flipping metrics
  differ. Use US spellings, `pre-activation`, `non-negative`, `layer-wise`,
  `feedforward`, `GELU`, `DeepLIFT`, `GradientSHAP`, `VGG-16`, and the source's
  `winner-takes-it-all` pooling name.
- The global routing game assumes non-negative activations. GELU discussions
  are local or concern a separate exact DC construction, not a global signed
  routing game. At every activation log-space tie, explicitly select **stopping**.
- Report mathematical errors to the user before changing the paper. Coordinate
  mathematical edits with the Lean task; preserve hypotheses and distinctions
  between a selected backward rule and a classical derivative.
- Use cheap agents for routine editorial work and strong agents for Lean or
  mathematical review. Independently attack source correspondence and edge cases.

## Source/content state

`arxive/playingTheNetworkBackward/` contains the preprint source revised for AISTATS,
arXiv **2605.06212v2**, not the superseded version. Unchanged downloaded inputs and
checksums are in `arxive/downloads/`. `arxive/hiddenMonotonicity/` contains the
other paper and already reported mathematical corrections. Do not replace the
merged chapters with an older source dump.

The content audits are `reports/paper-merge-restorations.json`,
`reports/hidden-paper-merge-audit.json`, `reports/ptnb-paper-merge-audit.json`,
and `reports/final-paper-content-review.json`. Fifteen identified omissions were
restored before this checkpoint. Later source-wording restoration is recorded
in `reports/terminology-source-wording-restoration.json`.

The trajectory comparison is `sec:nrm_comparison` in
`tex/chapters/11_trajectory.tex`, comparing the trajectory view with **Normalized
Relevance Measure as a Unifying Framework to Explain Neural Network Latent
Structures**, Xiong, Schnake, Montavon, Müller, and Nakajima, arXiv **2606.00557v1**.
The existing `Xiong2026nrm` bibliography record now includes the DOI and URL.
The comparison was independently checked in `reports/nrm-comparison-review.json`.
NRM relevance is signed; game trajectory probabilities are non-negative;
attribution uses signed differences of discounted occupation measures. An
NRM/CRP equivalence is proposed future work, not a theorem proved here.

The third-party source/PDF was downloaded and checked locally. Its arXiv license
does not grant this repository general redistribution rights. Recreate the exact
download on the new server with Python 3.12 or newer:

```sh
python3 scripts/fetch_nrm_source.py
```

The script uses versioned URLs and verifies the hashes in
`reports/nrm-source-provenance.json`; the resulting literature directory is
ignored by Git. This is the only external literature source needed for the latest
comparison. Both user-authored paper source trees are already committed.

## Acknowledgements

The current English acknowledgements include Gerrit Holzbach, Georg Loho,
Grégoire Montavon, Wojciech Samek, Klaus Robert Müller, and Shinichi Nakajima.
Preserve these specific intentions:

- Holzbach: opportunity to work on ML and gain a practical perspective.
- Loho: deep learning theory and polyhedral geometry.
- Montavon: DC decomposition discussions, Quantus, and attribution evaluation.
- Samek: the Responsible AI lecture, which introduced the author to problems
  in this area and strategies for addressing them; transformers;
  **asking the author to study parameter randomization**; conceptual discussions;
  and organizational support. Do not use “sanity check” in this acknowledgement.
- Müller: interesting discussions of the results.
- Nakajima: discussions and comparing the author's trajectory distribution view
  with NRM's signed-measure perspective on LRP and CRP.

## Tables and terminology

All original point estimates are retained; uncertainty intervals and significance
markers have the intentional changes documented above. Entirely unmeasured MaxS/AvgS columns were
removed from the VOC table (formerly A.16); its source explicitly did not evaluate
those metrics. Elsewhere `n/r` means not reported and `n/a` means not applicable.
Do not invent numerical values to replace an unavailable result.

The split tables use score-drop AUC **PF^drop_5 / PF^drop_20, higher is better**,
112 scalar channel features per step. The game tables use remaining-logit AUC
**PF_5 / PF_20, lower is better**, 1,568 scalar channel features per step.
A 224×224 RGB input has 150,528 such features; these counts are not spatial
pixels. The two metrics and target conventions are not interchangeable.
The chapter defines metric/method abbreviations. Best values use the game paper's
dark blue shading and bold type; light blue ablation comparison defaults are
explicitly distinguished from statistical ties.

The official implementations are pinned Git submodules, not copied algorithm
forks. `scripts/generate_thesis_tables.py` invokes the game repository's CPU
summary-to-TeX writer, then `scripts/table_presentation.py` applies the thesis
presentation rules. It runs no experiments and downloads no datasets.

```sh
python3 scripts/generate_thesis_tables.py --python /path/to/experiment-environment/bin/python --check
python3 scripts/check_paper_references.py --check
python3 scripts/normalize_thesis_terms.py --check
python3 scripts/sync_lean_badges.py --check
```

The writer needs the official repository's Python dependencies, including torch.
All 13 reproducible outputs matched after adaptation. Inputs for six diagnostics
and the Hidden Monotonicity ImageNet tables are absent from the official summaries;
their published source tables remain included. See `scripts/table_sources.json`,
`reports/table-adapter-verification.json`, and
`reports/split-table-numeric-preservation.json` (all ten split-table numeric
sequences matched). The initial final-layout review found A.1 and A.16 fit the
page and no table-grid overflow. Later typography edits need the final build
record in `reports/publication-build.json`; do not infer full-PDF cleanliness from
the table review alone.

## Lean links and coordination

Theorem/lemma/definition headings contain numbered `Lean_1`, `Lean_2`, … links
inside their heading brackets, following the style of arXiv 2610.01728v2.
Equation numbers link directly to declarations. The verified source has
**216 mappings**. Check the current active/retired/aliased inventory and
PDF occurrences against the single document; duplicate source formulations
may share a canonical statement and label alias.
The links target the clean verified source commit `1f886dd524d0c9f3b38192a55fd7cfa5a20dfe06`. These new commit URLs will be
publicly resolvable only after the local source commit is published.

`formalization/tex_links.json` records declaration and scope; the manual review
is `reports/lean-link-coverage-review.json`. `scripts/sync_lean_badges.py` retains
independently reviewed mappings and inserts heading commands. The generator
resolves actual declaration lines from Git; never guess or hard-code a line.
Do not regenerate links against an arbitrary moving HEAD while Lean is changing.
The Lean agent must first supply a committed, verified source snapshot. Then:

```sh
python3 scripts/generate_lean_links.py --revision VERIFIED_COMMIT
python3 scripts/generate_lean_links.py --revision VERIFIED_COMMIT --check
```

## Resume priorities and final publication checks

1. Read the last typography/checkpoint reports and the public build receipt.
   Rebuild after any changes; check actual final log and rendered pages.
2. Use `reports/thesis-reviews/resolution-audit.json` to distinguish completed
   repairs from the remaining factual and empirical limits. Read the original
   reviews for their rationale, not as an up-to-date list of untouched defects.
   Report any additional mathematical correction before editing source papers.
3. Retain the recently restored original wording; review any new changes for
   accidental loss of hypotheses, citations, table values, or definitions.
4. Check the PDF has no unresolved `??`, citations/references, or private
   registration number, and the main PDF stays within the 150-page cap. Verify all PDF Lean URIs use the new repository and the
   intended commit/lines. `pdftotext`, `pdfinfo`, `pdftoppm`, and `mutool show` are
   sufficient; no PyMuPDF dependency is required.
5. Copy the checked build to `docs/thesis.pdf`, update the build receipt, and
   commit reviewed changes. Follow the user's current publication instructions;
   the earlier local-only checkpoint note is obsolete. Keep the proof source pin
   fixed unless a new complete proof gate validates a replacement.

Do not claim that all mathematics is formalized. That remains the independent
Lean task, whose pending work is listed in `HANDOVER_LEAN.md`.
