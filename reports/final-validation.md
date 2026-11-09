# Final validation — 2026-11-09

- Thesis: `latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex`
  passed in `tex/`; final PDF has 194 pages. Nomenclature was generated
  with `makeindex main.nlo -s nomencl.ist -o main.nls`.
- Corrected local Hidden Monotonicity paper: `latexmk -pdf -interaction=nonstopmode
  -halt-on-error main.tex` passed in `arxive/hiddenMonotonicity/` (36 pages).
- Active thesis inputs: 48 files; 143 citation keys all present in
  the generated Biber bibliography; 376 distinct reference targets all
  present in generated auxiliary files. Extracted PDF text contains no `??` markers.
- Imported v2 results: all 19 generated table files byte-identical to upstream.
  All 71 figure asset files byte-identical to imported upstream files.
- Original v2 source tarball and PDF SHA-256 hashes match the download metadata.
- Lean: `lake build` passed. All 126 theorem declarations were audited through
  `lake env lean Audit.lean`; only standard Lean/mathlib foundational axioms
  (`propext`, `Classical.choice`, `Quot.sound`) occur. No project placeholders,
  `sorryAx`, or custom axioms.
- Formalization coverage is partial. The source inventory records 146 explicit
  statements, including repeated paper/thesis wrappers: 21 formalized variants,
  30 partial mappings, 2 encoded definitions, and 93 not formalized. These counts
  are not a whole-paper certificate. See `formalization/VERIFICATION.md`.

The LaTeX log retains generic undefined-reference/rerun notices despite all
explicit citation and reference targets resolving, plus layout/font warnings.
Biber retains 13 legacy date/month metadata warnings in existing entries; no
missing-entry or fatal bibliography errors remain. Mathematical corrections
have not been used to infer new experimental measurements; no experiments were
rerun. The separate preserved source tar/PDF remain upstream artifacts, while
local extracted paper corrections are listed in `mathematical-corrections.md`.
