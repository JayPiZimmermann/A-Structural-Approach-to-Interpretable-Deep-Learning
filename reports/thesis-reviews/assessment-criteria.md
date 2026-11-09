# Assessment framework for an excellent master's thesis

Prepared on 9 November 2026, before the substantive thesis reviews. This document
sets their assessment standard; it does not assess the current manuscript or
assign it a grade. The thesis metadata identifies an M.Sc. in Computer Science
at TU Berlin, Faculty IV.

## What a 1.0 assessment should mean

TU Berlin's general examination regulations describe the thesis as both an
examination and part of scientific training: the student must demonstrate
independent work on a disciplinary problem using scientific methods within the
allotted time. The assigned scope must be feasible in that period. The grading
scale groups 1.0 and 1.3 under *sehr gut*, defined as “eine hervorragende Leistung”;
examiners assess the thesis independently. These provisions do not supply a
separate numerical rubric distinguishing 1.0 from 1.3. [Official AllgStuPO,
§60(1), §60(4), §68(1), §68(3)](https://www.static.tu.berlin/fileadmin/www/10000000/Studiengaenge/StuPOs/AllgStuPO_deu.pdf).

The framework below is therefore a proposed scholarly assessment standard, not
an invented binding rubric from the supervisor, examination board, or university.
The agreed assignment, applicable programme regulations, and examiners' judgment
remain decisive. It does not turn conference acceptance criteria into examination
requirements.

For this review, an excellent 1.0 thesis should demonstrate unusually strong
command of its subject through a coherent, independent investigation whose main
claims survive careful scrutiny. Its research questions, methods, proofs,
experiments, and conclusions should form a traceable argument. The reader should
be able to distinguish established facts, empirical observations, interpretations,
and open questions without reconstructing that distinction from scattered
appendices. A finite, carefully justified contribution can meet this standard;
unlimited breadth cannot reasonably be required of a master's project.

This interpretation is consistent with TU Berlin numerical linear algebra thesis
guidance, which evaluates achievement of the agreed objectives, mathematical
correctness, numerical experiments where applicable, independent contributions,
critical engagement with literature, exposition, and independence. That guidance
is relevant supporting evidence, but belongs to another research group and is
not a binding rubric for this Computer Science thesis. [TU Berlin NLA thesis
guidelines, section 5](https://www.tu.berlin/fileadmin/www/10002104/NLA/files/theses_nla_group.pdf).

## The publication basis must be explicit

The thesis brings together and extends two research works co-authored by the
author:

1. Jakob Paul Zimmermann and Georg Loho, *Hidden Monotonicity: Explaining Deep
   Neural Networks via their DC Decomposition*, CVPR 2026, pp. 24107–24117,
   selected as a **Highlight**. The publication and author list are recorded in
   the [CVF proceedings](https://openaccess.thecvf.com/content/CVPR2026/html/Zimmermann_Hidden_Monotonicity_Explaining_Deep_Neural_Networks_via_their_DC_Decomposition_CVPR_2026_paper.html);
   the designation is on the [official CVPR conference page](https://cvpr.thecvf.com/virtual/2026/poster/36564).
2. Jakob Paul Zimmermann, Jim Berend, Georg Loho, Sebastian Lapuschkin, and
   Wojciech Samek, *Playing the Network Backward: A Game-Theoretic Attribution
   Framework*, **arXiv preprint 2605.06212v2**, revised 9 October 2026. The
   [versioned arXiv record](https://arxiv.org/abs/2605.06212v2) supplies no
   conference acceptance or journal reference. The local description “revised
   for AISTATS” and use of an AISTATS template do not establish acceptance.

The reviews should recognize the published component's achievement while
evaluating the integrated thesis on its own evidence. Highlight selection does
not certify every later extension, proof, experimental comparison, or repository
claim. Conversely, the preprint's status is not a defect by itself: its arguments
and evidence must be assessed directly.

The thesis should identify which chapters and results derive from each work,
what has been corrected or extended, and the student's own contributions within
the collaborations. Author order alone is insufficient to establish those roles.
This is an assessment of demonstrated independence, not a request to manufacture
a sole-authorship narrative. The DFG treats authorship as a substantive,
identifiable contribution and recognizes several forms of contribution.
[DFG Code of Conduct, Guideline 14](https://www.wissenschaftliche-integritaet.de/en/gl-14-395122).

## Proposed assessment dimensions

| Dimension | Evidence expected for an excellent thesis | Proportionate limit |
|---|---|---|
| Research question and synthesis | Clear questions, a reason the two constructions belong together, and explicit answers supported by identified results. The thesis adds an intelligible synthesis rather than leaving the reader to connect two papers. | A third publishable project is not required. |
| Independence and attribution | A concrete account of the student's conceptual, mathematical, implementation, experimental, and writing contributions; clear treatment of reused and jointly authored material. | Co-authorship is compatible with excellent independent work. |
| Mathematical rigor | Precise definitions and hypotheses, valid proofs for central claims, explicit boundary cases and distinctions between exact identities and algorithmic choices. Formal verification is credited only for the statements and models actually checked. | Complete machine formalization is not a general master's requirement. A missing Lean proof is different from a missing mathematical argument. |
| Experimental validity | Experiments answer the stated questions, comparisons are fair, evaluation metrics support the interpretation, and conclusions remain within what the design can establish. | Exhaustive architectures, datasets, and all recent competing methods are not required when a narrower claim is justified. |
| Reproducibility and auditability | A practical route from documented inputs and configurations to the central reported results, together with an honest inventory of unavailable artifacts or unexecuted checks. | A new reviewer need not rerun an entire expensive research programme to assess whether the route is credible. |
| Critical judgment and presentation | Limitations affect the conclusions; contrary outcomes receive attention; notation, citations, figures, and exposition support verification. A reader can identify the main contribution without reading every technical appendix first. | A 1.0 thesis may contain minor editorial defects and clearly delimited open questions. |

These dimensions are not assigned arbitrary percentage weights. A severe error
in a central claim cannot be compensated for mechanically by attractive writing
or publication prestige. Likewise, the absence of optional breadth must not
erase a strong, carefully delimited contribution.

## Experimental rigor and reproducibility: questions reviewers should answer

The following questions operationalize the proposed dimensions for this thesis;
they are not a list of new university rules.

- **What is the unit of evidence?** Identify datasets, inclusion and exclusion
  rules, sample identifiers, model checkpoints, and whether the result concerns
  one fixed trained model or a population of training runs. Separate per-image
  uncertainty from variation due to training, randomization, or method selection.
- **Was evaluation independent of selection?** Establish which data selected
  methods, hyperparameters, layers, shifts, normalizations, and reporting choices.
  A held-out test claim requires a test set that did not also guide these choices.
- **Are comparisons answering the same question?** Check target classes,
  preprocessing, resolution, perturbation budgets, attribution normalization,
  baseline configuration, and metric definitions. Shared names or similar-looking
  tables do not make different experimental protocols directly comparable.
- **How much does the evidence support?** Report effect sizes and appropriate
  uncertainty for central comparisons. Examine dependence between observations,
  paired comparisons where appropriate, and sensitivity to the choices that
  could plausibly reverse the conclusion. A narrow benchmark advantage must not
  silently become a universal claim about interpretability or model quality.
- **Can the claimed result be reconstructed?** Trace central tables and figures
  to evaluation code, configurations, data manifests, raw or sufficiently detailed
  intermediate results, aggregation, and presentation. Recreating a table from
  shipped summary values is useful but establishes a different claim from
  rerunning the model evaluation that produced those values.
- **What remains unverified?** Distinguish a documented reproduction path from an
  executed reproduction. Record actual commands, environment, hardware needs,
  exit status, and output checks when a rerun is claimed. Do not imply that a
  proof assistant verifies the Python implementation or the empirical results.

The NeurIPS checklist provides useful field-specific prompts: disclose selection
details and data splits; provide reproducibility instructions; explain the
variation captured by error bars and how they were calculated; and describe
required compute. It also explicitly permits justified limitations. These are
used here as methodological guidance, not as conference submission rules imposed
on the thesis. [NeurIPS Paper Checklist, items 4–8](https://neurips.cc/public/guides/PaperChecklist).

The broader documentation principle is that another researcher should be able
to inspect how a result was obtained. Contrary results and constraints on
documentation should also be recorded rather than hidden. This supports a
focused reproducibility requirement tied to the main claims, with a transparent
account of limitations. [DFG Code of Conduct, Guideline 12](https://www.wissenschaftliche-integritaet.de/en/gl-12-395172).

## How the subsequent reviews should be written

Each review should first state its perspective and which manuscript/artifacts it
examined. Every substantial criticism should identify an observable issue, its
scientific consequence, and a feasible repair with a completion criterion. It
should distinguish confirmed defects, missing documentation, unresolved
questions, and proposals for additional research.

Use three priority levels:

- **Must correct:** a false or unsupported central claim, material contradiction,
  misleading provenance, or an error that prevents the evidence from being
  interpreted correctly.
- **Needed for a persuasive 1.0 case:** a material gap in independence, rigor,
  synthesis, or auditability of the main contribution that can reasonably be
  addressed within the thesis's scope.
- **Optional strengthening:** useful further studies, broader benchmarking,
  additional formalization, or polish beyond what the stated central claims need.

The reviews should be candid about whether the submitted evidence presently
makes a convincing 1.0 case, without presenting an invented numerical score as an
examiner's decision. Recognize a genuinely strong research contribution even
when its documentation needs work. Do not lower the standard of correctness
because the work is a master's thesis, and do not replace a master's assessment
with a demand for an unlimited sequence of additional papers.

## Source-verification note

Official sources were checked on 9 November 2026. Some TU Berlin and CVPR pages
returned errors through the browsing tool; their official HTML/PDF was retrieved
directly over HTTPS for verification. The AllgStuPO PDF was reached from TU
Berlin's current examination-regulations index, rather than using the superseded
2013 PDF returned by an initial search. No final thesis grade or substantive
manuscript finding is asserted in this framework.
