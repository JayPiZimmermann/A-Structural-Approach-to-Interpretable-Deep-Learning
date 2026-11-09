# Review of correspondence between results and empirical claims

The thesis contains substantial research, but its empirical summaries are less reliable than its best detailed results sections. Several readily checkable statements exaggerate an advantage or name the wrong comparator. These are correctable defects in scientific reporting, not reasons to demand a third research project. An excellent master’s thesis must make its strongest conclusions agree with its own tables. On this dimension, the current manuscript does not yet make a persuasive 1.0 case; a focused reconciliation would materially improve it.

This review applies the [master’s assessment framework](assessment-criteria.md) to the TeX sources available on 9 November 2026. It checks the bilingual abstract, contribution and conclusion summaries, the experimental chapter, split-method tables and ablations, and the revised game tables for ImageNet-S and Pascal VOC. It compares reported values and claim scope; it does not independently rerun evaluations or validate the statistical tests. Line references identify this source snapshot.

## Strengths that should be preserved

The publication basis is now clear: one CVPR 2026 Highlight and one preprint, both with the student as first author. This is strong research context, while neither publication status nor author order replaces assessment of the integrated thesis.

The revised game discussion is substantially more careful than a generic claim of better interpretability. In `tex/chapters/08_experiments.tex:112–133`, it identifies the Attribution Localization advantage, acknowledges the Pointing Game and Top-k qualifications, concedes weaker perturbation faithfulness, and reports the robustness and computational costs of sharper routing. The checked numbers support its principal AL comparisons: RG obtains 0.711 against the strongest localization-selected ViT baseline at 0.644; transferred RG obtains 0.459 against 0.413 on VOC. No incorrect best-value highlighting was found in the checked main ViT and VOC rows. The significance assertions remain dependent on the separate statistical assessment.

The distinction between score-drop Pixel Flipping in the split study and remaining-logit Pixel Flipping in the game study is explicit at `08_experiments.tex:9`. So are the different perturbation budgets, architectures, and sensitivity subsets. Preserving these distinctions is scientifically preferable to manufacturing a combined league table.

## Must correct the universal improvement claim

Both abstracts (`tex/frontmatter/abstract.tex:8,23`) say SplitCAM and SplitLRP improve the state of the art on VGG-16 and ResNet-18 across all Quantus metric categories. The reported ResNet results do not support this conclusion. Among the selected rows of `tex/tables/eval_res_main.tex`, the strongest split PF-drop-5 score is 0.168, whereas gamma-LRP reaches 0.213; the strongest split PF-drop-20 score is 1.395, whereas Guided Backprop reaches 1.757. Higher is better for both. For Maximum Sensitivity, where lower is better, the strongest selected split row is 0.219, against Grad-CAM’s 0.131 (lines 14–29).

The VGG table also has metric-specific trade-offs: LayerCAM’s PF-drop scores are 0.317 and 2.474, ahead of the split maxima 0.300 and 2.404 (`eval_vgg_main.tex:15,25`). This does not negate the split family’s Selectivity, localization, or robustness successes, nor does it by itself disprove improvement in a broad category containing multiple metrics. It does rule out language that readers could reasonably understand as blanket metric superiority.

A defensible replacement is: “The split methods achieve strong, configuration-dependent localization and Selectivity results, with trade-offs in Pixel Flipping and robustness.” Add architecture-specific detail where space permits. Completion means both abstracts, the contribution list, and the conclusion use the same metric-specific scope and do not turn different configurations’ successes into a single universally superior method.

## Must correct the ResNet comparator and disclose the omitted AL winner

The ResNet paragraph at `08_experiments.tex:40` identifies LayerCAM’s Selectivity 3.690 as the strongest baseline against SplitCAM’s 3.503. The same main table contains Guided Backprop at **3.517** and gamma-LRP at **3.550**. The actual best-baseline gap is therefore **0.014**, approximately **0.4%**, rather than 0.187, approximately 5.1%. SplitCAM still leads numerically; the present comparator substantially inflates the apparent margin. No uncertainty for this gap is supplied in that table, so it should not be called a statistically established gain.

A more consequential discrepancy concerns AL. The paragraph says the split methods edge the top localization scores, quoting SplitCAM 0.673 against LayerCAM 0.664. Yet the comprehensive ResNet appendix reports **Guided Grad-CAM at 0.742**, with another configuration at 0.717 (`tex/tables/appendix/xai_eval_res_full.tex:67–68`). Guided Grad-CAM is absent from the abridged main table. The appendix explicitly identifies the same ResNet-18 campaign and representative method configurations.

The evidence establishes an inconsistency between the broad prose and the complete reported comparison, not intentional cherry-picking. Either include the relevant baseline in the main comparison or explain a scientifically justified exclusion and restrict the statement accordingly. The minimum honest summary is that SplitCAM exceeds LayerCAM on AL in the selected comparison, while Guided Grad-CAM has the higher reported AL in the full table. Completion requires every “best” or “top” statement to specify its eligible methods and selection rule.

## Reconcile repeated configurations rather than silently changing numbers

The VGG main table’s SplitCAM row with scaling, alpha 0.4, winner-takes-it-all pooling, layer `(26,+,g)`, and absolute maps reports PF-drop-20 **1.590** and MaxS **0.456** (`eval_vgg_main.tex:16`). The alpha-ablation table describes the same configuration and reports **1.585** and **0.457** (`tex/tables/alpha_ablation_main.tex:17–20`). PG and AL coincide at 0.938 and 0.635.

These differences are small and do not establish a substantive performance reversal. They are nevertheless larger than a single shared value could produce under identical displayed rounding. Different stochastic perturbations, evaluation runs, or source revisions could explain them; the present configuration labels do not. Retaining inherited source values is appropriate until provenance settles the issue. A persuasive reproduction record should attach a run identifier, data/configuration hash and aggregation version to each row, then either explain independent runs or select a canonical result with a documented correction. Completion is a traceable explanation, not numerical agreement obtained by editing cells.

## Make the ablation conclusion match its trade-offs

At `08_experiments.tex:47`, the alpha ablation is summarized as improvement on all considered metrics below 0.5, except the distinct robustness optimum. The table supports useful intermediate settings, but not simultaneous improvement. For SplitCAM, moving from alpha 0.5 to 0.4 improves PG from 0.868 to 0.938 and AL from 0.550 to 0.635, while PF-drop-20 falls from **1.607 to 1.585**. At alpha 0.35 it falls further to 1.499. SplitGrad’s PG/AL optima occur at 0.35, but its PF-drop-20 optimum occurs at 0.4.

The conclusion should state that stabilization changes the trade-off and that different metrics prefer different alpha values. The ablation does not isolate every mechanism behind “both splitting itself and stabilization” improving explanations: that causal attribution requires a clearly defined control. A proportionate repair is narrower interpretation of the existing experiment, with an optional matched control if the stronger mechanistic claim is retained.

## Correct smaller winner summaries and automate claim traceability

The game-study sentence at `08_experiments.tex:162–163` credits VGG Pixel-Flipping leadership to LRP-epsilon. The full table instead gives **PF-5 to LRP-epsilon, 12.43**, and **PF-20 to LRP-gamma, 7.89**, against epsilon’s 8.17 (`tex/tables/ptnb_v2/generated/test_vgg16_ci_longtable.tex:20,22`). Name the winners separately.

Similarly, the VGG AL comparison 0.685 versus 0.613 is valid for localization-selected rows, but another, faithfulness-selected LRP-epsilon configuration has AL 0.639. Say “best localization-selected baseline”; do not silently broaden that comparator population. This is a scope clarification, not a reversal of the reported RG lead.

The highest-value repair is a small claim ledger: each headline empirical sentence should name its campaign, metric direction, eligible rows, selected configuration, effect size, uncertainty status, and source artifact. Reuse the game study’s generated numerical macros for split-study claims where feasible. These changes require careful scientific bookkeeping rather than new large-scale experiments. They would preserve the genuine contributions while making the thesis’s conclusions dependable enough to support an excellent assessment.
