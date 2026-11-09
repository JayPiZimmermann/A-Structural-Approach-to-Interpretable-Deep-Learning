# Paper v2 integration audit

Date: 2026-11-09

## Results

- Read the canonical files from the downloaded v2 tarball. All 19 `.tex` files under `tables/generated/` are included in the archive and have active counterparts under `tex/tables/ptnb_v2/generated/`. Every counterpart is byte-for-byte identical to its canonical source, so every numeric token matches exactly.
- The remaining active table wrapper, `tables/sanity_check.tex`, is adapted for thesis integration: `\small` became `\scriptsize`; `\citep` became `\parencite`; the section reference is namespaced; the table input path points at the copied generated table; and acronym commands use the thesis-local `ptnb` forms. Its numeric tokens are identical to the canonical wrapper; its generated input `sanity_check_tabular.tex` is byte-for-byte identical.
- The generated-table include set is complete: `ablations_resnet50_longtable`, `ablations_vgg16_longtable`, `ablations_vit_b16_longtable`, `attention_rule_vit_b16_tabular`, `diagnostic_numbers`, `double_random_tabular`, `input_baseline_tabular`, `main_vit_tabular`, `numbers`, `per_image_corr_tabular`, `pg_granularity_tabular`, `sanity_check_tabular`, `test_resnet50_ci_longtable`, `test_vgg16_ci_longtable`, `test_vit_b16_ci_longtable`, `test_voc_vit_b16_ci_longtable`, `val_selection_resnet50_tabular`, `val_selection_vgg16_tabular`, and `val_selection_vit_b16_tabular`.
- All 69 image files referenced by the v2 paper are present under `tex/figures/ptnb_v2/` and match their canonical source files byte for byte.
- Additional PDF spot-checks confirm key main-table results against the stored v2 PDF: RG localization AL 0.711, LRP-γ AL 0.644, RG+Eq TK 0.836, KernelSHAP PG 0.961, and RG anchor MaxS 0.166. The active chapter uses the v2 counts of 565 ImageNet-S test images and 2,743 VOC test samples.
- `566` occurs in the separate Hidden Monotonicity campaign description in `tex/chapters/08_experiments.tex`; that campaign legitimately has 566 test images. No `2,849`/`2849` occurrences were found in the active experiment, appendix, trajectory, or paper-v2 preamble. The v2 results describe RG's localization lead while retaining baseline wins on other metrics; no all-metrics superiority claim was found in the revised section.
- `.gitignore` has narrow exceptions for `arxive/downloads/playingTheNetworkBackward/*.pdf` and `tex/figures/ptnb_v2/**/*.pdf`. The source tarball is trackable already. No imported PDF figures currently exist.

## Verification limits

No thesis build was run as part of this audit, so it does not establish successful LaTeX or Biber compilation.

## Build verification after the integration audit

The parent agent subsequently ran `latexmk -pdf -interaction=nonstopmode
-halt-on-error main.tex` from `tex/`, generated the nomenclature with makeindex,
and obtained a complete PDF with all targets up to date. The build's bibliography
has no fatal errors; there are pre-existing metadata warnings. Further formal
verification material was added afterward, so the final PDF page count is recorded
in the final validation report. The extracted paper source has one local mathematical
clarification documented in `mathematical-corrections.md`; upstream downloads are
unchanged.

## Final bibliography normalization

The initial 40 appended exact-key records were consolidated: 26 same-title
works now use the existing canonical thesis keys, and 14 new works remain as
new records. The original 167 records are preserved. Alias resolution is recorded
in `paper-v2-citation-aliases.json`. Rendered provenance text was replaced with
actual venue metadata from the source bibliography, avoiding duplicate citations
and duplicated full references within bibliography notes.
