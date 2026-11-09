# Review of artifact execution and documentation

The repository makes a serious attempt to preserve the work behind this master's thesis, but the two experimental components have markedly different levels of usability. The revised game preprint provides a structured reproduction pipeline and useful intermediate results. The CVPR Highlight component contains a documented quick start that fails before evaluation begins. That is a concrete release defect, not a judgment about the published method's scientific merit. An excellent thesis can reasonably have an expensive full reproduction; its first executable instructions should nevertheless work.

This review follows the [master's assessment framework](assessment-criteria.md). It examines the repository and the official code at submodule revisions `31be19b460358a69516452402d41bd650845a344` and `9cae01ce429c34b295aa06dd056895ddd4ef9ff7`. The checks were command inspection, static source inspection, and one deliberately limited CLI execution. No fresh environment installation, GPU evaluation, or dataset download was performed. The assessment concerns the artifacts inspected on 9 November 2026.

## What the release already does well

The thesis pins both official repositories rather than quietly maintaining divergent implementations. Its table adapter records the actual source revision, protects the live table directory, and requires the expected revision and an unmodified tracked checkout before writing (`scripts/generate_thesis_tables.py:172–215`). These are useful safeguards against accidental evidence drift.

The game repository specifies a tested Python version, named torchvision weight enums, data acquisition commands, validation/test construction, selected configurations, resumable evaluation, statistical aggregation, and separate runtime benchmarks (`code/playing_backward/README.md:8–106`). It also provides per-image metric values, rather than only rounded paper means (`results_summary/README.md:5–16`). This supports substantially more independent scrutiny than a conventional collection of scripts and final tables.

The root's contemporaneous table reconstruction log reports canonical matches for all thirteen available outputs. That result deserves credit, with its precise scope: it demonstrates reconstruction of those tables from shipped summaries through the official writer and thesis adapter. It does not establish that the model evaluations were rerun, that the original environment installs cleanly, or that every diagnostic artifact is available.

## The Hidden Monotonicity quick start fails

**Must correct.** The advertised first map-generation example passes `--method-configs` (`code/hidden_monotonicity/README.md:133–140`). The actual parser accepts `--methods-config-dir` (`xai/unified_xai_evaluation.py:194`). I executed the documented flag using an existing Python environment containing the script's import dependencies:

```sh
python xai/unified_xai_evaluation.py \
  --method-configs quantus_evaluation_configs/vgg_full_eval/classical_layerOptimized/
```

It exited with status 2 and `unrecognized arguments`, before model or data loading. This establishes a documentation/interface failure without making any claim about the numerical implementation. The README also advertises `--split` and `--alpha` (`README.md:297–322`); the parser instead has `--val` and no `--alpha` argument. Its Python example imports `DirectSplitModel` and `compute_split_cam` (`README.md:240–241`), identifiers absent from the inspected implementation. The timing parser additionally retains an old workstation's absolute default directory (`xai/unified_xai_evaluation.py:179–181`).

There is a second mismatch within the first example: it is headed “Generate Saliency Maps with SplitCAM,” but the referenced directory contains classical baseline configurations such as Grad-CAM, guided backpropagation, and LayerCAM. Merely renaming the flag would not make this a reliable demonstration of the advertised method.

**Repair and completion criterion:** replace the examples with commands and imports exercised against the pinned release, including an actual SplitCAM configuration. Give the correct validation switch and show how the stabilization parameter is supplied through the implemented configuration mechanism. A CPU parser/import smoke check should execute every documented entry point without fetching data; a small, separately documented example should then demonstrate the intended method. These are bounded release repairs, not a request to repeat the entire paper.

## The reported environment needs an executable contract

**Needed for a persuasive 1.0 case.** Hidden Monotonicity pins torch and torchvision, but leaves its evaluation library as `quantus>=0.5.0` and many other dependencies open-ended (`requirements.txt:13–43`). No exact environment lock was found for that component. This matters scientifically: the game repository itself explains that the Quantus 0.5-to-0.6 change alters attribution broadcasting and Pixel Flipping curve length (`code/playing_backward/requirements.txt:23–25`). A successful installation of the declared dependencies therefore does not identify the metric implementation used for the older published numbers.

The game component is considerably stronger: it supplies an exact package freeze, including torch and torchvision builds, and names Python 3.12 as the tested interpreter. Its README nevertheless promises “bit-exact reproduction” from installing the freeze (`README.md:20–25`). The inspected seed helper seeds Python, NumPy and torch and disables TF32 (`reproduce/common.py:644–656`), which are valuable controls. Those facts alone do not establish identical floating-point outputs across hardware and execution environments. This review has not tested whether the frozen requirements resolve on a fresh machine and makes no assertion that they fail.

**Repair and completion criterion:** supply the actual Hidden Monotonicity evaluation environment or explicitly document which version details can no longer be recovered. For both components, publish one tested installation receipt with interpreter, platform and hardware/runtime information, plus a small reference run and numerical acceptance tolerances. Reserve a bitwise claim for an executed comparison that establishes it; otherwise describe the reproducibility level actually tested.

## Availability claims need to agree across entry points

**Must correct the documentation.** The game README says its shipped summaries regenerate “every result table” (`README.md:91–94`), while its summary README explicitly excludes randomization, Hellinger and granularity outputs (`results_summary/README.md:23–26`). The thesis's own inventory correctly names six unavailable diagnostic outputs, and separately explains that the Hidden Monotonicity ImageNet table inputs are absent (`scripts/table_sources.json`). The root README is candid about these limits. The conflicting upstream sentence still sends a new reader toward an impossible expectation.

**Repair and completion criterion:** provide a single compact artifact index, linked from both documentation entry points, distinguishing available summary reconstruction, documented reevaluation, and unavailable source outputs. Every central table or figure should have an executable command and input location, or an explicit statement that it is retained from the publication. This is documentation and artifact curation; it need not entail redistributing licensed ImageNet images or inventing missing results.

## Provide a small route before the full campaign

**Needed for a persuasive 1.0 case.** The game README commendably estimates several hundred GPU-hours for the full evaluation and roughly 150 for VOC (`README.md:96–106`). It also offers tests and CPU table reconstruction. What a new reader still needs is a short, ordered route connecting these levels: install, run a synthetic correctness test, evaluate one named method on a tiny specified sample, inspect the output, and then run the full selected configurations. The Hidden Monotonicity quick start's interface drift makes this especially valuable.

**Completion criterion:** a concise execution guide should state each stage's inputs, expected outputs, approximate resource requirement and success condition. Include one captured successful run from a clean environment. Full-scale reevaluation remains optional for an examiner; the ability to audit a representative path should not depend on access to the author's workstation.

## Assessment

The artifact work is substantial and strengthens the thesis. The thirteen-table reconstruction and revised preprint's per-image release are meaningful achievements. The current documentation, however, does not yet support an unqualified claim that a new reader can execute both experimental components as documented. Fixing the demonstrably broken entry points, binding the older metric environment, and making availability claims consistent would materially strengthen a 1.0 case without expanding the research programme. These shortcomings should be repaired as scientific communication and reproducibility obligations, rather than excused by the CVPR Highlight or inflated into a demand for another publishable project.
