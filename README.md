# A Structural Approach to Interpretable Deep Learning

Master's thesis by Jakob Zimmermann: **From DC Decompositions to Two-Player Games**.
This repository contains the thesis TeX, the two paper sources, a shared Lean
formalization, and adapters for reproducing the thesis tables from the official code.

## Contents

- `tex/`: thesis sources and figures. Build from `tex/main.tex`.
- `docs/thesis.pdf`: compiled thesis with commit-pinned links to the Lean theorems.
- `arxive/hiddenMonotonicity/`: Hidden Monotonicity paper sources, with reported mathematical corrections.
- `arxive/playingTheNetworkBackward/`: revised AISTATS paper, arXiv 2605.06212v2, with reported mathematical corrections and explicit routing-game tie conventions.
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
git clone --recurse-submodules https://github.com/JayPiZimmermann/structural-interpretability-thesis.git
cd structural-interpretability-thesis
```

For an existing checkout, run `git submodule update --init --recursive`. The Git
submodule entries pin the exact upstream revisions; ordinary `git pull` does not
silently advance them. Each upstream repository retains its own license.

| Code | Official repository | Pinned revision |
|---|---|---|
| Hidden Monotonicity | [DC-Decomposition-for-Explanability](https://github.com/JayPiZimmermann/DC-Decomposition-for-Explanability) | `31be19b460358a69516452402d41bd650845a344` |
| Playing the Network Backward | [Official repository](https://github.com/JayPiZimmermann/Playing_The_Network_Backward_Official_Repository) | `9cae01ce429c34b295aa06dd056895ddd4ef9ff7` |

Thesis-specific table adapters live here. Changes to attribution algorithms should
be developed in the relevant official repository and incorporated by updating the
submodule pin. The Lean proofs verify mathematical models; they do not certify
these Python implementations or the reported experiments.

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
against the thesis: values, row order, labels, and whitespace-normalized TeX agree.
The check includes the main/CI tables, validation selections, ablations, attention
rule comparison, VOC transfer, and macros for numbers in the prose.
`reports/table-reproduction.json` records the exact output hashes.

The adapter first writes to a review directory and records provenance. Add
`--check --write` to synchronize only after every comparison succeeds against
the pinned, unmodified upstream checkout. A different value or row association
fails the check. To intentionally change experimental results, review those
changes and update the thesis and provenance together.

Six game-paper diagnostics require outputs absent from the public summaries.
The Hidden Monotonicity ImageNet table inputs are also absent from its official
code checkout. Their existing published TeX tables remain included; they are
not described as recomputed experiments. `scripts/table_sources.json` identifies
the sources and each missing input.

## Stable links from TeX to Lean

Thesis statements use `\LeanResult{source-label}`; selected equation numbers are
linked too. The design follows the TeX commands in arXiv:2610.01728v2, with links
pinned to a commit instead of the moving default branch.

After changing Lean sources, build and audit them, commit those sources, then run:

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
