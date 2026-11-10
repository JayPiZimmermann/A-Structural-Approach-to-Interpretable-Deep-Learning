# A Structural Approach to Interpretable Deep Learning

Master's thesis by Jakob Zimmermann: **From DC Decompositions to Two-Player Games**.
This repository contains the unified thesis TeX, the two paper
sources, a shared Lean
formalization, and adapters for reproducing the thesis tables from the official code.

The thesis brings together **Hidden Monotonicity**, a [CVPR 2026 Highlight](https://cvpr.thecvf.com/virtual/2026/poster/36564), and **Playing the Network Backward**, an [arXiv preprint (v2)](https://arxiv.org/abs/2605.06212v2). Jakob Paul Zimmermann is first author of both coauthored works. The thesis integrates their theoretical and empirical results, extends the convex/monotone decomposition to smooth activations and finite Transformers, and adds a partial Lean formalization.

## Continue this checkpoint on another server

Read [HANDOVER_TEX.md](HANDOVER_TEX.md) for the independent TeX task and
[HANDOVER_LEAN.md](HANDOVER_LEAN.md) for the independent Astra proof task.
They distinguish the verified proof source, integrated thesis content, and
unfinished experiments. The single-PDF consolidation starts from `b43bc24`;
earlier editorial and citation audits remain separately recorded below.
The complete clean proof gate passed at
`1f886dd524d0c9f3b38192a55fd7cfa5a20dfe06`: 167 modules, 490 reviewed exact
contracts and 3,640 imported theorem axiom audits, with all 168 commands successful.
The 216 proof-source mappings are pinned to that revision. Of these, 194 remain
represented by canonical statements and reviewed aliases; 22 unused geometry
mappings are retired from the TeX while their verified Lean proofs remain available. The current revision integrates the detailed proofs into their chapters and the
full supporting experiments into appendices of one **147-page PDF**. Duplicate
statements and summaries are consolidated; the page target remains 150. Compact tables sit
with their discussion, and only extensive results and grids remain in appendices. See the
handovers and [publication receipt](reports/publication-build.json) for validation
and experiment details.

The earlier compression was checked by independent mathematical, empirical and
[text-retention audits](reports/evidence/page-budget/text-retention.json). The later
editorial revision deliberately removes the unused tropical/polyhedral background;
the decomposition, game, Transformer, and experimental arguments remain intact.

## Academic reviews

The [review overview and prioritized repair plan](reports/thesis-reviews/README.md)
links twelve independent agent reviews of the thesis, with emphasis on experimental
rigor, reproducibility, mathematical scope, and independent scientific contribution.
The [assessment framework](reports/thesis-reviews/assessment-criteria.md) explains
what an excellent master's thesis should demonstrate. The reviews remain historical
snapshots. The [resolution audit](reports/thesis-reviews/resolution-audit.json)
records 13 resolved findings and five partial areas: historical artifacts, AI
identifiers, timing provenance, conflicting VGG values, and further numerical
stability evidence.

The reference audit covers all 190 original bibliography entries and 405
reference-context pairs. Its [source records](reports/reference-audit/references.json)
and [coverage check](reports/reference-audit/coverage.json) accompany the
claim-by-claim corrections in `reports/reference-audit/`.
Comments beside each retained BibTeX entry identify
the primary source, downloaded version and local file under
`literature/references/`, with a checksum. Partial documents and inaccessible
full texts are explicitly distinguished from checked full papers. Downloaded
third-party texts stay local; source URLs and audit records are versioned.

A subsequent literature update adds eleven references from Samek, Müller, and
related groups, with short comparisons across the introduction, split methods,
Transformers, trajectory diagnostics, and conclusion. The
[selection report](reports/recent-literature/selection.json) explains their
placement; [metadata and source records](reports/recent-literature/metadata.json)
identify ten downloaded PDFs and the GEF paper checked through indexed primary
excerpts only. Quantus remains briefly embedded in the existing metrics paragraph.

The [prose-concision review](reports/prose-concision/integration.json) records
roughly 17% shorter prose, with chapter order, displayed equations, citation keys,
and labels preserved. Independent reviews check proof steps and scientific
qualifications. The MNIST difference models now explicitly investigate the
opposing-stream mechanisms exposed by decomposing pretrained networks.

The subsequent [single-PDF consolidation](reports/single-pdf/integration.json)
merges the former supplement into the thesis and removes repeated statements,
proof steps and table summaries. Its prose count falls a further 23.8%, with
all citation keys, figure assets and original label names retained through
canonical statements and aliases. Independent reviews check mathematical scope
and experimental qualifications; structural checks do not establish semantic
equivalence by themselves. The residual-network Routing Game claim is explicitly
restricted to its gated convention.

## Contents

- `tex/`: thesis (`main.tex`), integrated appendices, and figures.
- `docs/thesis.pdf`: the complete thesis, including proofs and extended experiments.
- `arxive/hiddenMonotonicity/`: Hidden Monotonicity paper sources, with reported mathematical corrections.
- `arxive/playingTheNetworkBackward/`: preprint revised for AISTATS, arXiv 2605.06212v2, with reported mathematical corrections and explicit routing-game tie conventions.
- `arxive/downloads/`: unchanged arXiv PDF/source download and checksums.
- `formalization/`: Lean 4/mathlib proofs for both papers, sharing the same finite MLP and gate trace.
- `code/`: pinned Git submodules of the official implementations.
- `scripts/`: thesis table and Lean source-link adapters.
- `reports/`: provenance, mathematical corrections, and validation records.

The Lean formalization is partial. Its coverage map distinguishes source theorem
variants, checked components, definitions, and statements that remain unformalized.
A link to a component is not a certificate for an entire theorem or paper.

## Clone with the official code

```sh
git clone --recurse-submodules https://github.com/JayPiZimmermann/A-Structural-Approach-to-Interpretable-Deep-Learning.git
cd A-Structural-Approach-to-Interpretable-Deep-Learning
```

For an existing checkout, run `git submodule update --init --recursive`. The Git
submodule entries pin the exact upstream revisions; ordinary `git pull` does not
silently advance them. Each upstream repository retains its own license.

| Code | Official repository | Pinned revision |
|---|---|---|
| Hidden Monotonicity | [DC-Decomposition-for-Explanability](https://github.com/JayPiZimmermann/DC-Decomposition-for-Explanability) | `43a8bce45ac1d61b28dfa5ddc7eaf32e8ad35f4f` |
| Playing the Network Backward | [Official repository](https://github.com/JayPiZimmermann/Playing_The_Network_Backward_Official_Repository) | `7b5cd387f0a690b0d3451aa60bc8d897bd442a38` |

These repair revisions are committed in the local official checkouts and have
not been pushed. Until publication, a public clone retrieves the previous published
snapshot and cannot fetch these new commits from the remotes.

Thesis-specific table adapters live here. Changes to attribution algorithms should
be developed in the relevant official repository and incorporated by updating the
submodule pin. The Lean proofs verify mathematical models; they do not certify
these Python implementations or the reported experiments.

## Convex decompositions for activations and Transformers

The thesis gives explicit convex, coordinatewise-monotone pairs for ReLU, GELU,
Swish, sigmoid and Softplus, then extends the construction to coupled softmax,
products and positive-epsilon LayerNorm. The Transformer definition includes
actual masked multihead attention, residuals, input-dependent LayerNorm, an MLP,
optional final normalization and signed affine logits at arbitrary finite depth.
The algorithm and its main endpoints are in
[TransformerCorrectness.lean](formalization/HiddenMonotonicity/TransformerCorrectness.lean).
Their exactness and structural theorems passed the integrated verification gate;
[the receipt](reports/verification/commit-1f886dd/receipt.json) binds the checked
source commit and complete imported proof closure.

Monotonicity and convexity of the complete split hold on nonnegative doubled
inputs. The positive/negative lift of raw inputs gives globally convex heads,
without a raw-input monotonicity guarantee. Exactness does not imply numerical
stability: the independent [float64 diagnostic](scripts/transformer_dc_demo.py)
retains all twenty tested cases, including fifteen with final absolute error
above `1e-8` and stream magnitudes up to `5.95e111`. See
[its evidence](reports/evidence/transformer-dc/numeric-review.json).

## Real-ViT diagnostic campaign

A separate local branch, `research/transformer-dc-stabilization`, in
`/home/jzimmermann/code/hidden-monotonicity-transformer-dc` contains the completed ViT-B/16 campaign. Model execution is pinned
to `aa2d8c2d46744d7fee8ada2ac66be4d4534dd888`; final analysis/rendering is at
`5dd534989463b3e690b900f6a2ca3021213cf79f`. The final artifact commit is
`4c02ba66c681437b03a6bd76fad1cae24f45da4e`; its clean worktree includes
reproduction commands in `reports/vit_dc_comparison/README.md`. This branch is
separate from the thesis's validated HM submodule pin.

Six fixed qualitative images at four alpha values give 24 split cases and 36
fresh baseline maps. Maximum absolute errors are `5.329e-15` for logits,
`1.353e-15` for separate-head gradient reconstruction and `6.523e-16` for
intermediate gradients. The stabilized backward produces shifted/capped
algorithmic signals, not unchanged convex-head derivatives. At alpha 0.4,
SplitCAM is only 0.0040–0.279% away from the ordinary activation-times-gradient
control in relative L2. These results establish accurate reconstruction on the
six examples, not improved attribution quality or benchmark performance.

- [Red fox in snow detail](/home/jzimmermann/code/hidden-monotonicity-transformer-dc/results/vit_dc_comparison/comparison/red_fox_snow_detail.png).
- [Six-image method comparison](/home/jzimmermann/code/hidden-monotonicity-transformer-dc/results/vit_dc_comparison/comparison/method_comparison.pdf).
- [Machine-readable numerical summary](/home/jzimmermann/code/hidden-monotonicity-transformer-dc/results/vit_dc_comparison/comparison/summary.json).

The worktree's `reports/vit_dc_comparison/campaign_receipt.json` records the
executed source, checkpoint, arrays, figures and independent audit. Results and
commits remain local; the raw unstabilized diagnostic above remains a separate
numerical limitation.

## Check the Lean proofs

Install Lean's `elan` toolchain manager, then:

```sh
cd formalization
lake exe cache get
lake build All
python3 scripts/verify.py
```

`lean-toolchain` and `lake-manifest.json` pin Lean and all dependencies.
The gate records the committed source closure, reviewed exact theorem types, complete imported theorem axiom audit, commands and hashes. Use `--diagnostic` for development files.
See [the formalization guide](formalization/README.md) for the simple network
definitions, theorem coverage, and assumptions.

The verification workflow follows the six downloaded formalization/exposition skills from the [planar-features repository](https://anonymous.4open.science/r/Removing-spurious-minima-for-planar-features-by-skip-connections-35F8/README.md). `skills/upstream-planar-features/provenance.json` records their source URLs and checksums. Independent adversarial reviews, executable counterexamples and repair evidence are retained under `reports/`.

## Build the thesis

With TeX Live, `latexmk`, and Biber installed:

```sh
cd tex
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
makeindex main.nlo -s nomencl.ist -o main.nls
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Build the single root until references settle, then copy `tex/main.pdf` to
`docs/thesis.pdf`. Run from the repository root:

```sh
python3 reports/evidence/page-budget/verify_publication.py
```

The guard checks the 150-page target, the final log, the published PDF,
internal destinations, proof links, and the unchanged verified proof source. The
current [publication checks](reports/single-pdf/publication-checks.json)
and [consolidation receipt](reports/single-pdf/integration.json)
record the single-PDF layout. Earlier page-budget and prose-concision audits
apply to their recorded revisions. The public cover omits the student registration number. It can be set privately
in `tex/preamble/meta.tex`.

## Reproduce the thesis tables

Install the dependencies documented in `code/playing_backward/README.md` in a
Python environment, then from this repository root run:

```sh
python3 scripts/generate_thesis_tables.py --python /path/to/environment/bin/python --check
python3 reports/single-pdf/build_experiment_views.py --check
```

This invokes the official CPU table writer on its shipped summaries. It runs no
model evaluations and downloads no datasets. All 13 available outputs were checked
against the thesis after its presentation adapter. Point estimates, configurations
and row order are preserved. VOC uncertainty was recomputed with image-level
cluster resampling, and full-pair Holm adjustment changes ten ImageNet comparison
markers; the corresponding prose and archived-paper tables were updated together.
The adapter itself standardizes labels and colors, removes entirely
unmeasured metric columns, and makes non-applicable configurations explicit. The single-PDF
presentation additionally merges identical selection/ablation rows and presents
validation ranks in one matrix; its generator verifies every original rank and
configuration against the canonical tables. Compact comparisons appear beside
their discussion, with extensive matrices and grids in the appendices.
The check includes the main/CI tables, validation selections, ablations, attention
rule comparison, VOC transfer, and macros for numbers in the prose.
`reports/table-reproduction.json` retains the original raw-output check;
`reports/table-adapter-verification.json` records the current adapted-output check.

The adapter first writes to a review directory and records provenance. Add
`--check --write` to synchronize only after every comparison succeeds against
the pinned, unmodified upstream checkout. A different value or row association
fails the check. To intentionally change experimental results, review those
changes and update the thesis and provenance together.

Six game-paper diagnostics require outputs absent from the public summaries.
The Hidden Monotonicity ImageNet table inputs are also absent from its official
code checkout. Their existing published TeX tables remain included; they are
not described as recomputed experiments. Six historical MNIST training
configurations are also unavailable. Current CPU fixtures and a documented example
do not recover those historical campaigns. The repaired HM runner uses a separate
training-pool validation set and reserves the test set for final evaluation.
`reports/evidence/hm-reproduction-repair/summary.json` records its 27 passing tests
and 23 subtests; `scripts/table_sources.json` identifies table sources and missing
inputs.

## Source-content and reference coverage

Separate audits compare both source papers with the merged thesis. The completed
restoration list is in [paper-merge-restorations.json](reports/paper-merge-restorations.json),
with detailed per-paper reports alongside it. Original technical text, equations,
figures and tables are retained where compatible with the shared notation and
reported mathematical corrections. The introduction connects both papers through
interpretability as a tool for improving and controlling models.

```sh
python3 scripts/check_paper_references.py --check
```

This follows the active TeX input trees, verifies explicit citation aliases, and
checks source citations across the thesis and its appendices, including
their bibliography records. The current report retains 67 of 74 Hidden Monotonicity
source labels (including appendix aliases) and all 72 game-paper labels. Six omitted
labels refer to three unused geometry-background works; a seventh accompanied an
unsupported biological-plausibility claim. The [editorial omissions](reports/paper-reference-editorial-omissions.json)
and [reviewed corrections](reports/paper-reference-reviewed-corrections.json)
record these decisions. No unexplained missing references remain.
Publication and named-method titles retain their official wording.

The trajectory chapter also compares the thesis with Xiong et al.’s
[Normalized Relevance Measure framework](https://arxiv.org/abs/2606.00557).
`reports/nrm-source-provenance.json` records the versioned source/PDF URLs and
checksums used for that comparison. The third-party source archive is available
from arXiv; it is not redistributed here.

## Stable links from TeX to Lean

Statements in the thesis use numbered `Lean_1`, `Lean_2`, … references inside their
heading brackets, via `\LeanResult{source-label}`; selected equation numbers
link directly to their declarations too. The design follows the TeX commands in arXiv:2610.01728v2, with links
pinned to a commit instead of the moving default branch.

After changing Lean sources, compile and review them, commit the reviewed sources
and configuration, and run the clean verification gate. Then generate links:

```sh
python3 scripts/generate_lean_links.py --revision HEAD
python3 scripts/generate_lean_links.py --revision HEAD --check
```

Commit the generated TeX/JSON separately. The generator resolves declaration
names to their actual source lines and rejects a working copy that differs from
the chosen commit. `formalization/tex_links.json` records the selected declaration
and coverage wording for each link.

The archived source papers preserve their authorship and license terms. This
repository does not replace the official paper repositories or their licenses.
