# Independent semantic review of the Transformer DC assembly

**Verdict: passed; no substantive semantic defect found.** The final source
implements an actual finite pre-LayerNorm Transformer, compiles those same
parameters into scalar expressions, and evaluates their explicit DC pairs.
The headline statements concern the resulting evaluator, rather than an
existentially chosen representation or a user-supplied convexity certificate.

This review covers `TransformerPairCalculus`, `TransformerConvexInput`,
`LayerNormDC`, `TransformerExpr`, `TransformerExprProperties`,
`TransformerDefinition`, and `TransformerCorrectness`. Source hashes and the
consumer receipt are in `assembly-semantic/review.json`. A separate definition
audit is recorded in `assembly-review-definition.md`.

## Definition correspondence

- `TransformerAffine` contains arbitrary signed real weights and biases.
  Its compiler explicitly uses signed scaling, finite sums, and constant pairs.
- `TransformerHead.logits` computes the current input-dependent query and key
  projections and their scaled dot product. `TransformerHead.eval` computes
  coupled softmax over each fixed allowed-key set, multiplies its probabilities
  by the current values, and applies the head's output projection. No realized
  attention matrix is substituted or detached.
- `TransformerMask` requires a positive allowed-key count for each query and an
  injective map from those indices into the token indices. This represents a
  fixed nonempty set without duplicated keys. The full mask is an explicit
  instance. A completely masked existing query is excluded.
- `layerMean`, `layerVariance`, and `layerNorm` use the current feature vector.
  `layerNormPair` explicitly computes centered pairs, their polarized squares,
  the averaged variance, the reciprocal-square-root pair, the centered-factor
  product, and arbitrary signed learned gain and bias. The exactness proof
  establishes that the represented variance is the actual nonnegative
  population variance, so the tangent extension is evaluated in its valid
  recovery domain. Epsilon is strictly positive.
- Each block contains attention LayerNorm, its finite list of heads and output
  bias, the first residual, feed-forward LayerNorm, signed up/down projections,
  a supported activation, and the second residual. The two normalization sites
  and residuals occur in the ordinary evaluator and its compiler.
- `evalTransformerBlocks` and `compileTransformerBlocks` recurse over an
  arbitrary finite list. The induction theorem relates their ordinary
  evaluations at every depth; depth is neither ignored nor bounded by a fixed
  numeral. Blocks may have different head lists, masks, intermediate widths,
  signed parameters, activation choices, and normalization constants.
- `Transformer.eval` adds positional bias, evaluates that block list, applies
  an optional final tokenwise LayerNorm, then takes an arbitrary signed affine
  readout over all tokens and features. There is no output activation.
  `Transformer.eval_syntax` bridges the separately specified evaluator to the
  compiled expression with the same parameters.

## Proof and domain audit

`Expr` contains actual input, arithmetic, finite-sum, closed-activation, softmax,
and LayerNorm constructors. It does not store a `Regular` proof or decomposition
certificate. `Expr.splitEval` is defined recursively by the corresponding
explicit pairs. Its exactness is proved by induction and holds even for signed
independent streams.

`Regular` records convexity of both heads, monotonicity, and nonnegative values
on a specified domain. Its composition proofs use genuine nonnegativity when
applying the polarized product. The final doubled-input domain is the entire
nonnegative orthant, whose coordinate projections satisfy the invariant
directly. Thus `Transformer.dc_decomposition` concludes orthant convexity,
orthant monotonicity, orthant nonnegativity, and exact recovery without requiring
the caller to supply those properties of the Transformer.

`Transformer.raw_dc_decomposition` applies the positive/negative input lift.
Its heads are globally convex and nonnegative on ordinary real embeddings and
recover the actual logits. It correctly makes no claim of monotonicity in those
signed raw inputs. The separate convex-substitution argument does not assume
that the negative-part input map is monotone.

## Independent behavioral consumers

The handwritten `assembly-semantic/Boundary.lean` passed the isolated command
`lake env lean ../reports/evidence/transformer-dc/assembly-semantic/Boundary.lean`.
Its final log and exit marker are `boundary-03.log` and `boundary-03.exit`.

The ten consumers cover:

1. An explicit depth-zero model with positional bias, negative readout weight,
   and positive readout bias, whose actual logit is `-2*x + 1`.
2. A negative actual logit `-3`, ruling out an accidental final ReLU.
3. Direct evaluation of the recursive split to `(3,6)` for that negative logit.
4. Direct raw-input evaluation at a negative input, producing `(7,2)`.
5. Two arbitrary blocks composing in the correct order.
6. A concrete two-token head whose actual logits are `x[q,0]*x[k,0]`.
7. That head's actual softmax-weighted sum of both current value routes.
8. Exclusion of a zero-key mask for an existing query.
9. The final exactness identity without stream-sign assumptions.
10. Global convexity of a raw-input head without a raw-input monotonicity premise.

Four printed axiom audits, including both final headline theorems, the compiler
bridge, and actual LayerNorm exactness, contain only `propext`,
`Classical.choice`, and `Quot.sound`. This review did not replace the separately
owned full expected-type/defining-module/universe audit or the parent's final
committed-closure gate. The first two consumer runs failed only while reducing
dependent finite index sizes in the review fixture; no production source was
changed to make a consumer pass.

## Limits that must remain visible

The concrete `Transformer` datatype is a pre-LayerNorm architecture on
continuous token embeddings. It supports the five closed activation families,
fixed nonempty masks, optional final LayerNorm, and signed affine logits.
There are no dedicated tokenizer, patch-embedding, dropout, rotary-encoding,
arbitrary attention-score-bias, or post-LayerNorm fields. The generic expression
language supports further finite combinations, including fixed scalar masks,
but the concrete architecture bridge should not be advertised as covering every
named Transformer variant without a corresponding compilation bridge.

Zero blocks and empty head lists are admitted and have explicit meaningful
semantics. Top-level token count and residual width are positive; query/key and
value head widths are positive. A zero feed-forward hidden width is harmless,
giving its affine bias-only case. A zero output width makes output statements
vacuous, while the scalar-output consumers above establish nonvacuity.

The compiler produces finite expression syntax, which may duplicate shared
intermediates. Neither a size/runtime bound nor floating-point stability is
proved. Large common stream values and cancellation do not contradict the
real-arithmetic exactness theorem. The current Chapter 7 wording distinguishes
these facts and distinguishes its separate post-normalization numerical
diagnostic from this pre-normalization formal model.
