# Review of interpretability claims and construct validity

This review assesses whether the thesis measures and proves what its interpretability language promises. It follows the [master's assessment framework](assessment-criteria.md), examining the current abstract, introduction, saliency chapter, experiments, trajectory diagnostics, conclusion, and principal split-method tables. The publication basis is a CVPR 2026 Highlight and a preprint; that is substantial research material for a master's thesis. The assessment concerns the integrated argument, rather than demanding another conference contribution. Source anchors refer to the manuscript inspected on 9 November 2026. No model evaluations were rerun for this review.

The work makes an unusually concrete contribution to understanding attribution computations. Its strongest defensible claim is that structural representations expose quantities and design choices that conventional heatmaps obscure. Its weaker point is the occasional promotion of a mathematical representation, metric advantage, or attractive visualization into a stronger claim about explanation quality. Several such claims require correction before the interpretability argument makes a persuasive 1.0 case. Most repairs are bounded and do not require a new large experimental programme.

## What the thesis already gets right

The manuscript explicitly separates numerical stability, localization, faithfulness to a specified computation, and parameter sensitivity in the [introduction, lines 11–19](../../tex/chapters/01_introduction.tex#L11). The game study selects localization and faithfulness configurations independently and reports confidence intervals and corrected paired tests. It acknowledges that localization gains can cost perturbation faithfulness and robustness ([experiments, lines 75–91 and 112–143](../../tex/chapters/08_experiments.tex#L75)). These are substantive strengths, not merely caveats appended to uniformly positive results.

The repaired trajectory discussion correctly distinguishes normalized routing from model-dependent signed discounted attribution. It explicitly says that routing changes do not rescue a map that fails the map-level sanity check ([trajectory chapter, lines 1003–1009](../../tex/chapters/11_trajectory.tex#L1003)). The conclusion also states that segmentation agreement can discard model-relevant context, that downstream task gains are untested, and that attributions are not causal guarantees ([conclusion, lines 27–45](../../tex/chapters/09_conclusion.tex#L27)). A review should credit these distinctions rather than claim that the thesis ignores them.

## Must correct the counterfactual interpretation of individual streams

The most serious issue is a false implication in the [saliency chapter, lines 274–277](../../tex/chapters/05_saliency.tex#L274), repeated in the captions at lines 323 and 370. A positive gradient of the complemented-input stream is said to indicate that adding an absent pixel increases the class logit. For the defined DICIN,

\[
f(x)=g(x)-h(1-x),\qquad \nabla f(x)=\nabla g(x)+\nabla h(1-x).
\]

The sign of one summand does not determine the sign of the sum. The stated architecture permits an unconstrained first layer ([line 251](../../tex/chapters/05_saliency.tex#L251)), so convexity does not make either stream monotone in the original pixels. A one-dimensional counterexample satisfies the relevant assumptions: take \(g(x)=\operatorname{ReLU}(4-4x)\), \(h(y)=\operatorname{ReLU}(3y)\), and \(x\in[0,1]\). At the empty pixel \(x=0\), \(h'(1)=3>0\), yet \(f(\delta)=1-\delta\) for \(0<\delta<1\): adding mass lowers the logit.

The immediate repair is to describe each visualization as a stream-local sensitivity and write the combined derivative explicitly. Calling a pixel a feature “the class would require” is stronger still: neither a positive individual nor a positive total derivative establishes necessity, a feasible finite counterfactual, or a change of predicted class. The same distinction should govern the “factual” reading of the other stream.

**Completion criterion:** the definition, captions, and summaries distinguish individual-stream sensitivity, complete-logit local sensitivity, and finite counterfactual change. If the stronger counterfactual claim is retained, check the actual complete model after specified pixel interventions and report failures. Narrowing the claim is a sufficient repair; a new counterfactual benchmark is not inherently required for an excellent master's thesis.

## Must correct the breadth of the abstract's empirical claim

Both abstracts claim improvements on VGG-16 and ResNet-18 across all Quantus metric categories ([abstract, lines 8 and 23](../../tex/frontmatter/abstract.tex#L8)). The [ResNet-18 table](../../tex/tables/eval_res_main.tex) supplies a clear counterexample to the breadth of this wording: Grad-CAM has Maximum Sensitivity 0.131, while the lowest displayed split-method value is 0.219, with lower better. The split methods therefore do not win the reported robustness metric on that architecture. Pixel Flipping also favors baselines, although Selectivity improves; losing Pixel Flipping alone would not disprove an advantage on some metric within the faithfulness category.

The stronger abstract cannot be excused by the more careful conclusion that no method dominates every metric. It is the most widely read account of the results. Replace the blanket claim with the actual pattern: selected split configurations improve localization and Selectivity, with architecture- and metric-dependent trade-offs. Preserve the distinction between a family containing different winning configurations and one configuration that performs best across criteria.

**Completion criterion:** every abstract superiority statement names its metric scope and agrees with the relevant table. No new runs are needed to make this correction.

## Must distinguish weak rank association from independence

The subsection titled “Per-Image Trajectory-vs-Map Independence” reports Spearman correlations, then calls the readouts essentially independent or orthogonal ([trajectory chapter, lines 1115–1179](../../tex/chapters/11_trajectory.tex#L1115)). Small rank correlation establishes weak monotone association in the observed sample; it does not establish statistical independence or exclude nonlinear predictability. This distinction matters because the thesis uses these results to motivate a different diagnostic object, not merely to describe a table.

The experimental comparison also needs precise scope: the protocol says the ViT attribution cascade additionally randomizes Q, K, and V projections, unlike the Hellinger cascade ([lines 1125–1131](../../tex/chapters/11_trajectory.tex#L1125)). Those readouts do not reflect identical interventions. That does not invalidate their descriptive correlations, but it limits a claim that disagreement isolates different aspects of the same changed computation.

**Completion criterion:** title, caption, main-text summary, and conclusion say “weak observed rank association” or equivalent. State the ViT intervention mismatch beside its interpretation. Matched randomization and nonlinear dependence analysis are optional strengthening if the claim is narrowed; they become necessary if independence or broad unpredictability is retained.

## Needed for a persuasive 1.0 case clarify the explanatory semantics

The thesis sometimes treats plausible visual readings as established explanatory properties. The [experiments, lines 135–143](../../tex/chapters/08_experiments.tex#L135), say that broader maps show environmental features the network used and describe a “perception-optimal” explanation. Broader mass is an observation; actual feature use and optimal human perception are additional claims. A visualization alone does not establish either. Use “visually broader context attribution” and identify any judgment of informativeness as qualitative, unless supported by a defined evaluation.

Likewise, the [saliency summary, line 474](../../tex/chapters/05_saliency.tex#L474), concludes affirmatively that constrained networks are self-interpretable, while [line 377](../../tex/chapters/05_saliency.tex#L377) properly limits the demonstrated separation to visual examples. Two correctly classified digit-3 examples and a single-stream comparison motivate a hypothesis about stream roles; ten-seed classification accuracy tests predictive performance, not explanatory semantics. The abstract's “strong self-interpretability” should be reconciled with this evidence.

**Completion criterion:** state an operational meaning for self-interpretability and identify exactly which evidence supports it. A proportionate repair is to claim qualitative, class-dependent stream sensitivities on MNIST and retain the proposed semantic interpretation as a hypothesis. If general disentanglement is central, evaluate a prespecified sample across classes and report failure cases using a declared separation measure. No human-subject study is required merely to make the narrower claim.

## Assessment and proportionate next steps

The core contribution can support an excellent thesis without demonstrating downstream model correction, clinical utility, or universal explanation quality. Those are already bounded as future work. The outstanding task is to make the strongest summaries obey the same standards as the careful technical passages.

Prioritize the incorrect stream-to-logit implication, the abstract's metric claim, and the independence language. Then add a compact claim-to-evidence table separating exact representation identities, benchmark localization, perturbation faithfulness, numerical or attribution stability, parameter sensitivity, qualitative stream interpretation, and untested downstream utility. For each row, identify a result and what it does not establish. This would turn an ambitious collection of interpretability results into a more disciplined scientific argument. The present weaknesses concern defensibility, not a lack of sufficient research breadth for a master's degree.
