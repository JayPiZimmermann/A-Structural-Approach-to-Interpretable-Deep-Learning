# TeX handover for Astra — 9 November 2026

The user requested this checkpoint so the thesis can be continued on another
server. This document is sufficient to start the TeX task independently. The
mathematical continuation has a separate [Lean handover](HANDOVER_LEAN.md).

## Continuation and academic reviews

The 9 November continuation added thanks to Wojciech Samek for his Responsible
AI lecture and made the publication basis explicit: **Hidden Monotonicity is a
CVPR 2026 Highlight paper; Playing the Network Backward is an arXiv preprint
(v2)**. The introduction and publication-provenance appendix identify both
coauthored works and the thesis additions.

The routing-law prose has been corrected to distinguish normalized routing from
model-dependent signed discounted attribution. The regularizer/curvature remark
now assumes local absolute continuity of the gate, with a positive second
derivative of the regularizer as a sufficient condition. The corresponding
source reviews are `reports/routing-law-precision-review.json` and
`reports/regularizer-curvature-review.json`.

The rebuilt thesis has no overfull boxes or unresolved references/citations.
All 13 summary-backed game tables matched in the fresh CPU reconstruction;
`reports/evidence/tex-resumption/` records the commands and checks. This did not
rerun model evaluations. The latest public PDF and proof-link revision are
recorded in `reports/publication-build.json`.

The requested [twelve academic reviews and prioritized repair plan](reports/thesis-reviews/README.md)
follow a sourced [master's-level assessment framework](reports/thesis-reviews/assessment-criteria.md).
They identify remaining scientific and reproducibility repairs. These findings
are review recommendations, not changes silently applied to the experiments or
manuscript. Use the consolidated plan for the next revision; the current PDF is
a reviewed checkpoint, not a claim that every identified issue has been fixed.

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
private workspace. `docs/thesis.pdf` is built from this public source tree.

## User requirements that remain binding

- Merge the motivation, insights, and content of both papers. The central
  motivation is interpretability moving from post hoc analysis toward improving
  and controlling models. Preserve original paper formulations wherever possible;
  do not paraphrase sentences merely to restate them. Avoid duplicate material.
- Preserve every source-paper reference, experiment, figure, table, and substantive
  point. Source corrections and a common notation are intentional exceptions to
  verbatim preservation. The reference checker currently finds all 74 Hidden
  Monotonicity and all 72 revised game-paper source keys.
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

`arxive/playingTheNetworkBackward/` contains the revised AISTATS source,
arXiv **2605.06212v2**, not the superseded version. Unchanged downloaded inputs and
checksums are in `arxive/downloads/`. `arxive/hiddenMonotonicity/` contains the
other paper and already reported mathematical corrections. Do not replace the
merged chapters with an older source dump.

The content audits are `reports/paper-merge-restorations.json`,
`reports/hidden-paper-merge-audit.json`, `reports/ptnb-paper-merge-audit.json`,
and `reports/final-paper-content-review.json`. Fifteen identified omissions were
restored before this checkpoint. Later source-wording restoration is recorded
in `reports/terminology-source-wording-restoration.json`.

The latest added section is `sec:nrm_comparison` in
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

All measured values are retained. Entirely unmeasured MaxS/AvgS columns were
removed from the VOC table (formerly A.16); its source explicitly did not evaluate
those metrics. Elsewhere `n/r` means not reported and `n/a` means not applicable.
Do not invent numerical values to replace an unavailable result.

The split tables use score-drop AUC **PF^drop_5 / PF^drop_20, higher is better**,
112 pixels per step. The game tables use remaining-logit AUC **PF_5 / PF_20,
lower is better**, 1,568 features per step. These are not interchangeable.
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
Equation numbers link directly to declarations. The published checkpoint has
**190 mapped links** pinned to the clean verified source commit
`0f3cfb0ea660556c14da510e665281f07acc471d`.

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
2. Work through the prioritized repairs in `reports/thesis-reviews/README.md`.
   The routing-law prose precision and regularizer-curvature assumption issues
   were corrected in this continuation. The new reviews identify separate
   remaining mathematical, experimental, statistical, and reproduction issues;
   keep confirmed defects distinct from optional further research. Report any
   additional mathematical correction before editing source papers.
3. Retain the recently restored original wording; review any new changes for
   accidental loss of hypotheses, citations, table values, or definitions.
4. Check the public PDF has no unresolved `??`, citations/references, or private
   registration number. Verify all PDF Lean URIs use the new repository and the
   intended commit/lines. `pdftotext`, `pdfinfo`, `pdftoppm`, and `mutool show` are
   sufficient; no PyMuPDF dependency is required.
5. Copy the public build to `docs/thesis.pdf`, update the build receipt, commit
   reviewed changes and push. Public pushes were explicitly authorized. Coordinate
   pushes or use separate worktrees so the TeX and Lean tasks do not change a
   source commit while a clean proof gate is running.

Do not claim that all mathematics is formalized. That remains the independent
Lean task, whose pending work is listed in `HANDOVER_LEAN.md`.
