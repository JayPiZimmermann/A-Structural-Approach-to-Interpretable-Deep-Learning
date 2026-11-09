# Statistical rigor review

The revised game campaign has substantially better statistical practice than a collection of unqualified benchmark means: validation selects configurations, test comparisons are paired, uncertainty is reported, and unfavorable trade-offs remain visible. Nevertheless, the current statistical presentation is not yet a persuasive 1.0-level account. The principal obstacle is a concrete mismatch between the sampling unit and the uncertainty calculation on Pascal VOC. Two additional interpretive claims—comparability from nonsignificance and independence from low rank correlation—are stronger than the evidence establishes. These problems warrant focused repair, not an unlimited new experimental programme.

This assessment follows the [master's thesis assessment framework](assessment-criteria.md). It recognizes that the thesis integrates a CVPR 2026 Highlight and a preprint. Publication status neither removes these obligations nor makes the preprint intrinsically weaker. The review examined the current TeX experiment and trajectory chapters, the statistical appendix, generated tables, the pinned game repository's statistical routines, and its shipped per-sample scores. No model evaluation was rerun; the statistical code received an additional independent read-only audit.

## What is already strong

The two-stage protocol separates validation selection from test evaluation and retains independent localization-selected and faithfulness-selected configurations. That is an appropriate way to expose competing objectives rather than selecting a favorable metric after looking at the test table. The test-set ablations are explicitly described as diagnostic rather than fed back into selection. These are substantive strengths, not cosmetic qualifications. See [experiment protocol](../../tex/chapters/08_experiments.tex#L75), lines 75–91 and 167–169.

The appendix specifies 10,000 percentile bootstrap resamples, paired mean-difference tests, McNemar tests for binary Pointing Game, and the scope of Holm correction. The implementation aligns method scores by sample identifier and compares paired finite observations. Sensitivity metrics use the same 200-image subset and seeded perturbations across methods. The attention-rule ablation also uses an explicit reference contrast and correction across its tested cells. See [statistical specification](../../tex/chapters/10_appendix.tex#L294), lines 294–309; [sample alignment and comparisons](../../code/playing_backward/reproduce/bootstrap_ci.py#L48), lines 48–125; and [attention ablation](../../code/playing_backward/reproduce/make_tables.py#L477), lines 477–510.

The discussion openly reports losses in faithfulness and robustness alongside localization gains. It also distinguishes the split campaign's score-drop Pixel Flipping metric from the game's remaining-logit metric. An excellent master's thesis should receive credit for these distinctions.

## Principal findings and required repairs

### 1. VOC uncertainty uses the wrong independent sampling unit

**Confirmed implementation issue; must correct.** The thesis correctly splits VOC by image, keeping all foreground classes of an image together. It then evaluates 2,743 image–class samples drawn from 2,293 images. The shipped scores confirm these counts in all 21 reported rows: 375 images contribute multiple class records, with up to five records from one image. See [VOC dataset and split](../../tex/chapters/10_appendix.tex#L448), lines 448–473.

However, the table writer treats the class-specific records as independent bootstrap observations. Its generic `ResultSet` calls `boot_indices(len(sc[metric]), ...)`, and VOC uses this same class without an image-cluster adjustment. Sample identifiers are explicitly constructed as `stem__class`. The paired tests likewise operate on the flattened records. See [table uncertainty calculation](../../code/playing_backward/reproduce/make_tables.py#L149), lines 149–165 and 708–726; [identifier construction](../../code/playing_backward/data/pascal_voc.py#L298), lines 298–310; and [comparison routine](../../code/playing_backward/reproduce/bootstrap_ci.py#L108), lines 108–125.

Sharing an image creates dependence that an ordinary record bootstrap does not represent. This does not establish validation leakage, invalidate the point estimates, or prove that any reported win will reverse. It does mean the reported intervals and significance claims lack the intended image-level sampling justification.

**Repair and completion criterion:** state whether the estimand averages image–class samples or first averages within each image. Resample image stems as clusters, retaining every class record and the same method pairing within each sampled cluster; preserve the chosen weighting. Use cluster-aware inference for Pointing Game too, rather than ordinary McNemar on dependent class records. Regenerate the VOC intervals and comparison decisions from the existing score archive and document which conclusions change. This is an aggregation repair, not a new GPU campaign.

### 2. Nonsignificance is presented as comparability

**Confirmed interpretive overreach; must correct wording.** The statistics subsection says all differences failing the corrected significance threshold are “comparable” ([appendix](../../tex/chapters/10_appendix.tex#L305), lines 305–309). The main caption is more careful: it says “not significantly different.” Those are not equivalent conclusions. Failure to reject a difference can reflect imprecision; it does not establish practical equivalence.

**Repair and completion criterion:** use “no difference detected at the stated threshold” consistently. If practical equivalence is scientifically important, define a meaningful margin and report a paired difference interval or an equivalence analysis. A master's thesis does not need equivalence tests for every table cell; accurate wording is sufficient where no equivalence claim is needed.

### 3. Comparing every row with a test-selected winner needs qualification

**Confirmed selection mechanism; inferential guarantee unresolved.** `significance_vs_best` chooses the best row using the same test means and then Holm-adjusts only comparisons with that winner ([bootstrap code](../../code/playing_backward/reproduce/bootstrap_ci.py#L138), lines 138–159). Holm correction controls a specified comparison family when its underlying tests are valid; applying it to a family chosen through the observed winner does not, by itself, justify the same guarantee for that selection procedure.

This concern applies particularly to best-row significance shading. It is distinct from the legitimate validation selection of method configurations. It also should not be indiscriminately applied to the separate, explicitly stated RG-versus-baselines contrasts, whose families must be assessed on their own terms.

**Repair and completion criterion:** designate the best-row markers as exploratory, or use an appropriate simultaneous all-pairs/selection-aware procedure. For headline claims, publish the predetermined contrasts, paired effect sizes, confidence intervals, and corrected decisions. State clearly that correction is within each specified metric family, not across every result in the thesis.

### 4. Low Spearman correlation does not establish independence

**Confirmed claim-strength mismatch; must correct.** The trajectory section is titled “Per-Image Trajectory-vs-Map Independence” and treats cross-correlations bounded by 0.19 as evidence that rankings are essentially independent and examine orthogonal structure. It reports neither correlation intervals nor a general dependence analysis. Small Spearman correlation establishes little monotone association in the observed sample; nonlinear dependence may remain. See [trajectory analysis](../../tex/chapters/11_trajectory.tex#L1115), lines 1115–1179.

Moreover, the ViT comparison explicitly uses different randomized parameter sets in its two pipelines. This disclosed mismatch weakens an attribution of the discrepancy solely to the diagnostic representation ([protocol](../../tex/chapters/11_trajectory.tex#L1125), lines 1125–1138).

**Repair and completion criterion:** rename the result as weak observed rank association, add paired-bootstrap intervals and scatterplots for the main comparisons, and mark the ViT comparison as using different interventions. A stronger independence claim would require a suitable dependence analysis and matched interventions; that is optional if the narrower claim answers the thesis question.

### 5. Separate descriptive campaign results from generalization uncertainty

**Evidence boundary needing clearer synthesis.** The older split tables show point estimates, including very small displayed advantages such as PG 0.972 versus 0.971 and AL 0.673 versus 0.664 ([results](../../tex/chapters/08_experiments.tex#L40)). They do not carry the revised game's paired uncertainty analysis. The current wording should therefore distinguish observed ordering from a reliably estimated improvement.

The game's image bootstrap is also conditional on fixed checkpoints, selected configurations, and the realized stochastic attribution evaluations. It does not quantify training-run variation or instability of selecting among the 2,021 validation configurations from 50 images. Conversely, the double-random experiment does use 500 independent rounds and explicitly says its variance mixes image and random-model variation ([trajectory protocol](../../tex/chapters/11_trajectory.tex#L1073), lines 1073–1087). That distinction should be preserved.

**Repair and completion criterion:** add a compact uncertainty-scope table for both campaigns. Report paired difference intervals for the central split comparisons if their per-image scores are available; otherwise keep them explicitly descriptive. A validation resampling analysis using existing scores would strengthen selection stability. Retraining all architectures is unnecessary for claims expressly about the chosen pretrained models.

## Judgment against an excellent master's standard

The work has enough empirical breadth and methodological substance for an excellent master's thesis. Its statistical weakness is not insufficient volume of experiments but uneven calibration of its claims. Correcting VOC dependence, replacing unsupported equivalence/independence language, clarifying comparison families, and stating uncertainty scope are proportionate requirements for a convincing 1.0 case. More datasets, architectures, or full training reruns are optional unless the author chooses substantially broader claims. The main localization advantages may survive every repair; that outcome must be established rather than presumed.
