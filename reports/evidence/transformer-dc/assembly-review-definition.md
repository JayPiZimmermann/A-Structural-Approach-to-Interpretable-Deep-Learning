# Independent Transformer-definition semantic review

Reviewer: `/root/dc_lean_lead/transformer_semantic_review/definition_semantics`.

Result: no semantic defect found in the concrete finite pre-LayerNorm
Transformer definition or its compiler bridge. This is a source-semantic review;
no builds, kernel checks, production edits, or global metadata edits were
performed by this reviewer.

## Definitions checked

- `TransformerAffine` has unrestricted real weights and biases. Its evaluator
  and compiler use the same coefficients, order, and output bias.
- Each attention row evaluates the full input-dependent query/key dot product,
  multiplies by the stored real score scale, evaluates one coupled softmax over
  that row's permitted keys, and contracts the resulting probabilities with the
  actual input-dependent Values. No attention matrix or projection is detached.
- `TransformerMask` supplies a positive key count for every query and an
  injective map into the finite token set. Thus permitted keys form a fixed
  nonempty subset without duplication. `TransformerMask.full` is the full-set
  specialization. The key list and mask do not depend on input values.
- The per-head output projections are summed, with one common attention-output
  bias. This is the usual concatenation-plus-output-projection computation
  written as a sum over output-projection column blocks.
- `TransformerBlock` performs attention on the first normalized input, adds
  that result to the original block input, then performs the affine–activation–
  affine feed-forward map on a second normalization of that residual, and adds
  the second residual. Both normalizations recompute mean and population
  variance from their current inputs. Positive epsilon is stored in each
  normalization parameter object; gain and bias may be signed.
- `evalTransformerBlocks` and `compileTransformerBlocks` recurse through the
  same arbitrary finite `List`, left to right. There is no depth bound. Every
  block retains its own parameters, head list, hidden width, and activation.
- The full evaluator adds positional bias before the block stack, optionally
  performs a final actual LayerNorm, and applies an unrestricted affine readout
  over all token/feature coordinates. It introduces no output activation.
- The compiler uses actual arithmetic/activation/softmax/LayerNorm expression
  constructors; these do not contain proof certificates or assumed DC heads.
  The visible compiler equations agree operation by operation with the ordinary
  evaluator. `eval_compileTransformerBlocks` states the unrestricted finite-list
  bridge, and `Transformer.eval_syntax` connects the resulting scalar expression
  to each actual output logit.

## Boundary and scope audit

Top-level token count and residual feature width are strictly positive. Each
head's key and value widths are strictly positive. Empty block lists and empty
head lists are accepted: the former gives the input/optional-final-normalization
path, while the latter leaves the attention bias and residual. A zero FFN hidden
width leaves its output bias. A zero output count yields no logits; the same
definition also permits every positive output count. None of these extensions
weakens the statements at nondegenerate sizes.

The concrete datatype describes **pre-LayerNorm Transformers on continuous
input embeddings**. It does not itself model a discrete tokenizer or patch
embedding module, arbitrary post-LayerNorm blocks, input-dependent masks,
explicit dropout nodes, rotary positional transformations, or a separate
arbitrary additive score-bias matrix. Its pointwise activation choice is the
five-case closed-form datatype (ReLU, exact Gaussian GELU, positive-scale Swish,
sigmoid, positive-temperature Softplus). Residual width and token count are
fixed across the stack; head widths, FFN widths, and parameters may vary between
blocks. These are scope limits to record if a broader manuscript statement is
linked to the concrete theorem. The generic scalar expression language covers
a broader class of finite computations than this particular model compiler.

The score scale is an arbitrary real parameter. Standard inverse-square-root
key-width scaling is one admissible choice; the model does not silently replace
it with a fixed number. Parameter choices such as scale zero or empty head
lists are valid degenerate computations rather than inconsistent assumptions.

The source establishes an explicit mathematical expression compiler. It does
not establish a shared-DAG implementation, a bound on expression expansion, a
floating-point error bound, or a runtime guarantee. Those claims should remain
separate from exact real-arithmetic evaluation.
