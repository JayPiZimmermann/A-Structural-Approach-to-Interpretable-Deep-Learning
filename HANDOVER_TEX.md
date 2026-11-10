# TeX handover for Astra — 9 November 2026

The user requested this checkpoint so the thesis can be continued on another
server. This document is sufficient to start the TeX task independently. The
mathematical continuation has a separate [Lean handover](HANDOVER_LEAN.md).

## Current local revision and verification boundary

The revision after checkpoint `afcbb42` is being completed **locally**. The user
asked for changes and execution in the local thesis and official code checkouts
first. No current repair commits have been pushed. Earlier publication approval
does not authorize silently publishing this revision.

The new source includes the generalized convex/monotone DC construction,
closed-form activation and softmax splits, an explicit arbitrary-depth
Transformer definition and splitting algorithm, and the requested review repairs.
The complete clean Lean gate passed at source commit
`1f886dd524d0c9f3b38192a55fd7cfa5a20dfe06`: **167 modules, 490 independently
reviewed exact contracts and 3,640 imported project theorem axiom audits**.
All 168 commands exited zero and the bound source snapshot remained fixed.
Evidence is in `reports/verification/commit-1f886dd/` and
`reports/verification/current/`. The 216 generated source links are checked and
pinned to that commit. The previous `0f3cfb0` gate remains archived.

The main thesis is **139 total PDF pages**, within the hard 150-page cap; its
separate technical supplement is **85 pages**. This compact presentation retains
the substantive mathematical and empirical improvements: detailed proofs and
full supporting experiments have moved to the supplement. The page-budget audit
preserves all 50 full captions and gives 48 entries shorter list titles.

There are 157 Lean annotations in the main PDF and 59 in the supplement:
216 combined occurrences covering 135 unique targets. All 80 main-to-supplement
and 72 supplement-to-main links resolve. All 176 files bound by the proof receipt
still match the verified source hashes. Both final logs have no overfull boxes
or unresolved references/citations, and both PDFs are copied to `docs/`.
`reports/evidence/page-budget/publication-checks.json` records the passed guard;
`reports/evidence/page-budget/final-editorial-audit.json` records the editorial
checks. The Lean source gate is unchanged by this editorial reorganization.

The strengthened retention checks compare against the pre-compression commit
`91d4d27`: all 804 original content blocks are accounted for, and all 314 displayed
formulas are preserved exactly. Independent mathematical and empirical reviews
found no lost substantive information. Their crosswalks are
`reports/evidence/page-budget/{text,math,evidence}-retention.json`.

Build both `tex/main.tex` and `tex/supplement.tex`. Detailed game, attention and
trajectory proofs and full experimental material live under `tex/supplement/`.
The main document retains the central definitions, results, evidence and narrative.
The original 74 HM and 72 game-paper reference keys are preserved across the
**main thesis and supplement together**; they need not all appear in the main
bibliography. Proof links are likewise distributed across both documents.
The source-reference checker and badge synchronizer now inspect both source roots.
Deliver `docs/thesis.pdf` and `docs/thesis-supplement.pdf` together so their relative
cross-document links can resolve.
After copying both compiled PDFs, run from the repository root:

```sh
python3 reports/evidence/page-budget/verify_publication.py
```

This checks the 150-page cap, both final logs, PDF/source equality, combined Lean
URIs, cross-document destinations and the unchanged proof-bound source hashes.
The final result belongs in `reports/publication-build.json` and the page-budget
evidence directory.

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
latexmk -pdf -interaction=nonstopmode -halt-on-error supplement.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error supplement.tex
```

The public cover deliberately has an empty `\mymatriculationnumber` in
`tex/preamble/meta.tex`. Do not replace it with metadata or a PDF from the old
private workspace. `docs/thesis.pdf` and `docs/thesis-supplement.pdf` are built from this public
source tree. Rebuild both after moving labels or changing cross-document references.

## User requirements that remain binding

- Merge the motivation, insights, and content of both papers. The central
  motivation is reliable inspection of vision models and shared visual grounding
  with human perception. Attribution helps assess whether predictions rely on
  intended evidence; targeted correction follows diagnosis and needs separate
  validation. Preserve original paper formulations wherever possible;
  do not paraphrase sentences merely to restate them. Avoid duplicate material.
- Keep the main document at or below 150 PDF pages; use the separate technical
  supplement for detailed proofs and full experimental material. Do not meet the
  cap by silently deleting scientific content.
- Preserve every source-paper reference, experiment, figure, table, and substantive
  point across the main document and supplement. Source corrections and a common notation are intentional exceptions to
  verbatim preservation. The reference checker assesses the combined source roots and preserves all 74
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
**216 mappings**, now distributed across the main document and technical
supplement; PDF occurrence counts must be checked for their combined outputs.
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
4. Check both PDFs have no unresolved `??`, citations/references, or private
   registration number, and the main PDF stays within the 150-page cap. Verify all PDF Lean URIs use the new repository and the
   intended commit/lines. `pdftotext`, `pdfinfo`, `pdftoppm`, and `mutool show` are
   sufficient; no PyMuPDF dependency is required.
5. Copy the checked builds to `docs/thesis.pdf` and `docs/thesis-supplement.pdf`,
   update the combined build receipt, and
   commit reviewed changes locally. Keep this revision local as requested; do not
   push based on earlier checkpoint authorization. Coordinate source commits so
   HEAD and bound files remain fixed while the clean proof gate runs.

Do not claim that all mathematics is formalized. That remains the independent
Lean task, whose pending work is listed in `HANDOVER_LEAN.md`.
