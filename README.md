# A Structural Approach to Interpretable Deep Learning

Master's thesis by Jakob Zimmermann: **From DC Decompositions to Two-Player Games**.
This repository contains the thesis TeX, the two paper sources, a shared Lean
formalization, and adapters for reproducing the thesis tables from the official code.

The thesis brings together **Hidden Monotonicity**, a [CVPR 2026 Highlight](https://cvpr.thecvf.com/virtual/2026/poster/36564), and **Playing the Network Backward**, an [arXiv preprint (v2)](https://arxiv.org/abs/2605.06212v2). Jakob Paul Zimmermann is first author of both coauthored works. The thesis integrates their theoretical and empirical results, extends the convex/monotone decomposition to smooth activations and finite Transformers, and adds a partial Lean formalization.

## Continue this checkpoint on another server

Read [HANDOVER_TEX.md](HANDOVER_TEX.md) for the independent TeX task and
[HANDOVER_LEAN.md](HANDOVER_LEAN.md) for the independent Astra proof task.
They distinguish the clean verified root, frozen extensions awaiting integration,
and unfinished drafts. The current repair and Transformer revision is local only;
its final integrated proof gate and thesis build are pending. The last completed
full gate is `0f3cfb0ea660556c14da510e665281f07acc471d`. Read the handovers and
receipts before treating newer leaf builds as publication verification.

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

## Contents

- `tex/`: thesis sources and figures. Build from `tex/main.tex`.
- `docs/thesis.pdf`: compiled thesis with commit-pinned links to the Lean theorems.
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
Their exactness and structural theorems compile; the final integrated verification
status is tracked in the handovers.

Monotonicity and convexity of the complete split hold on nonnegative doubled
inputs. The positive/negative lift of raw inputs gives globally convex heads,
without a raw-input monotonicity guarantee. Exactness does not imply numerical
stability: the independent [float64 diagnostic](scripts/transformer_dc_demo.py)
retains all twenty tested cases, including fifteen with final absolute error
above `1e-8` and stream magnitudes up to `5.95e111`. See
[its evidence](reports/evidence/transformer-dc/numeric-review.json).

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

The public cover omits the student registration number. It can be set privately
in `tex/preamble/meta.tex`.

## Reproduce the thesis tables

Install the dependencies documented in `code/playing_backward/README.md` in a
Python environment, then from this repository root run:

```sh
python3 scripts/generate_thesis_tables.py --python /path/to/environment/bin/python --check
```

This invokes the official CPU table writer on its shipped summaries. It runs no
model evaluations and downloads no datasets. All 13 available outputs were checked
against the thesis after its presentation adapter. Point estimates, configurations
and row order are preserved. VOC uncertainty was recomputed with image-level
cluster resampling, and full-pair Holm adjustment changes ten ImageNet comparison
markers; the corresponding prose and archived-paper tables were updated together.
The adapter itself standardizes labels and colors, removes entirely
unmeasured metric columns, and makes non-applicable configurations explicit.
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
checks that every source reference is cited in the thesis and present in its
bibliography. The current report has no missing references (74 source keys from
Hidden Monotonicity, including appendix aliases, and 72 from the revised game paper).
Publication and named-method titles retain their official wording.

The trajectory chapter also compares the thesis with Xiong et al.’s
[Normalized Relevance Measure framework](https://arxiv.org/abs/2606.00557).
`reports/nrm-source-provenance.json` records the versioned source/PDF URLs and
checksums used for that comparison. The third-party source archive is available
from arXiv; it is not redistributed here.

## Stable links from TeX to Lean

Thesis statements use numbered `Lean_1`, `Lean_2`, … references inside their
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
