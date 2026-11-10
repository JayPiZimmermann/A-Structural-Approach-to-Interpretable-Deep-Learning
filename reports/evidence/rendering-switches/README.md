# Independent TeX rendering switches

The defaults in `tex/preamble/rendering.tex` are `\RenderTables=1` and
`\RenderQualitativeImageTables=1`. Both publication documents load this file.

`matrix.json` records full main/supplement builds for all four combinations,
including cross-document reruns, label-number comparisons, loaded-image and
generated-table checks, placeholder counts, and final log checks. Builds used
independent writable files under `/tmp/thesis-rendering-switches-20261110/`;
source and asset directories were symlinked, and existing auxiliary files were
copied rather than hardlinked. No off-mode build wrote into `tex/` or `docs/`.
The recorded local build directories contain the complete transcripts and PDFs.
Generated-table checks count actual file opens in the TeX log, because recorder
`INPUT` entries also include `\IfFileExists` probes. The shared `numbers.tex` and
`diagnostic_numbers.tex` macro definitions remain active for the surrounding
prose; they do not render tables.

Each isolated root consists of the overrides followed by an absolute source
input, for example:

```tex
\def\RenderTables{0}
\def\RenderQualitativeImageTables{1}
\input{/absolute/path/to/tex/main.tex}
```

The compilation sequence is `latexmk -pdf -interaction=nonstopmode
-halt-on-error main.tex`, then the same command for `supplement.tex`, followed
by both again to settle cross-document references. Nomenclature was regenerated
with `makeindex main.nlo -s nomencl.ist -o main.nls`. The small fixture also
checks all combinations and verifies that an invalid flag value is rejected.

`source-retention.json` checks all 21 changed content files against `7c8e3f5`.
Expanding the new wrappers restores the original source exactly apart from
whitespace and comments; captions, labels, rows, images and mathematical content
are retained. A separate read-only coverage audit confirmed all six qualitative
grids (188 image calls), all regular tables, and eight unchanged ordinary figures.
