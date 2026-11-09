# Mathematical audit and local corrections

The findings below were reported in the conversation before the corresponding
local TeX corrections. The downloaded arXiv v2 source tarball and PDF remain
unchanged. These edits do not update an arXiv submission or published paper.

## Hidden Monotonicity: backward invariant

In `sections/method.tex`, equation `eq:backward_invariant`, insert a factor 1/2
in front of the difference of the four split partial derivatives. The symmetric
input lift is `(a/2,-a/2)`, so the chain rule gives

    Df = ((δ+g - δ−g) - (δ+h - δ−h))/2.

For `g(p,n)=max(p,n)`, `h(p,n)=n`, at `p>n`, the four partials are `(1,0,0,1)`.
The old left-hand side was 2, whereas the original active identity layer has
derivative 1. Corrected in the local paper and thesis Chapter 3.

## Hidden Monotonicity: stabilization coefficient and recurrence

In `appendix/proofs.tex`, theorem `thm:closed_formula_shift`, the coefficient
of the summand associated with gate `j+1` is

    product over i=j+1,...,L of (1-2 α^i).

The local shift at layer j cancels from the difference of the two sensitivities.
It must not appear in that summand. The sum-of-sensitivities product over
`i=l,...,L` is a different quantity and remains unchanged. The thesis already
used the correct coefficient `overline α_(j+1)`, with its definition starting at
j, and that convention has been preserved.

Counterexample to the old formula: scalar inactive layer of weight 1, terminal
shift α^1=0 and local shift α^0=1/4. Pulling back the positive head gives `(0,1)`;
shifting gives `(-1/4,3/4)` and symmetric sensitivity `-1/2`. The old coefficient
predicts `-1/4`.

The displayed recurrence `eq:delta_g_shif_recursion` also needs right
multiplication of its first term by `W^(l+1,x)`. This is required by both the
preceding chain-rule equation and matrix dimensions. The induction statements
now label the quantities as shifted sensitivities.

## Derivative qualifications and proof notation

Classical derivatives are asserted away from gate ties. A branch chosen at a
ReLU or Maxout tie is a backpropagation convention, not a proof of classical
differentiability. Added this qualification to the paper proof and thesis.
The difference quotient in the sensitivity-complementarity proof omitted the
base value in its numerators; restored it. The gated matrix product in
`eq:general_derivative_product` differentiates the activation `a`, not the
preactivation `z`; corrected the left-hand side.

A fixed common forward shift leaves the head Jacobian at translated coordinates
unchanged. An input-dependent shift c(x), when differentiated, adds the common
term `W_abs Dc` to both heads. Thus re-centering must be detached to preserve the
head sensitivities of the specified backward algorithm. For instance,
`g(x,0)=x`, `h(x,0)=0` for x>0, but shifting both inputs by c(x)=x gives heads
`2x,x`, with derivatives `2,1`. The difference still has derivative 1. Clarified
in the local paper and thesis; no numerical implementation has been changed.

## Multiplicative splitting does not preserve ordinary convexity

The positive monomial xy is monotone on the non-negative orthant but not convex:
its values at `(1,3)` and `(3,1)` are 3, while at their midpoint `(2,2)` it is 4.
Therefore maxima of positive-coefficient polynomials are not generally convex,
and the constructed product split does not prove a DC decomposition in the
original inputs. Corrected the main multiplicative statement and appendix proof
in the local hidden-monotonicity source and the corresponding thesis discussion.
The exact difference identity and monotonicity in non-negative split inputs
remain valid. The maximum-of-polynomials closure proof is restricted to that
orthant, where products distribute over maxima of non-negative functions.

The construction's input split uses ReLU and therefore requires rank at least
two: the general rank bound is max(k,2). Its expanded multiplication node has
`product_u (w_uv+1)` summands. Linear size for that construction requires fixed
rank and bounded total multiplication degree, with arcs counted as part of graph
size; bounded distinct input count alone is insufficient. Corrected these bounds.

## Playing the Network Backward v2: endpoint probabilities versus attribution

The paragraph following `thm:rand-routing` described the undiscounted input
marginal m as recovering gradients and alpha-beta LRP. The representation
results use discounted occupation measures instead. For a one-edge graph of
positive weight 2, the normalized transition probability is 1 whereas the
network derivative is 2; its discount supplies the missing factor. Corrected
this paragraph in the extracted local paper source and thesis. The original
source tarball and PDF retain the upstream text and hashes.

## Auxiliary Q-network tail

The original interpretation as a network with minimum activations at every tail
layer gives the displayed ungated absolute-weight derivative in a bias-free tail.
Arbitrary inherited tail biases can invalidate the sign argument. Defined Q[l]
explicitly as `W_abs^[l,→] min(z^l(x),0)`: the original prefix, followed by linear
absolute-weight maps with no tail biases or activation gates. This makes its
stated derivative precise. Applied in the local hidden-monotonicity paper and
thesis; it does not complete the remaining Lean identification of the Q-network
with the abstract matrix source terms.

## Scope and remaining verification

See `formalization/README.md`, its coverage inventory, and the Lean declarations
for the precise hypotheses and checked results. A checked algebraic recurrence
is not, by itself, a verification of every analytic, probabilistic, geometric,
or empirical statement in either paper. No experiment was rerun, and no changes
to reported experimental numbers were inferred from these mathematical fixes.
In particular, the sensitivity normalization and shift-index corrections need
to be checked against the experimental implementation before concluding that
its correction routines and reported numerical results are unaffected.

## Combined split gradients can both vanish

Reported before correction on 2026-11-09. The saliency chapter inferred nonzero
combined head gradients from the nonzero sum of their partial sensitivities.
That inference is false. Let f(x) = ReLU(ReLU(x) + ReLU(-x) - 10), and use the
balanced input pair (x/2, -x/2). Near x=1 the first split layer has positive head
(x/2, x/2) and negative head (-x/2, x/2); the output has both heads equal to 10.
Their derivatives both vanish, although the input is connected to the output.
The exact partial-sensitivity mass identity remains valid. The text now
distinguishes that mass from differences of partials and from attribution scores.
The example in the following remark is likewise stated as an example for its
specified baseline, not a proof of the sensitivity axiom for all baselines.

## Sign of the common probe correction in the saliency discussion

Reported before correction on 2026-11-09. The closed formulas read
g = (delta - C)/2 and h = (-delta - C)/2 for the combined head gradients.
The saliency prose incorrectly said the probe correction C has opposite signs.
It has the same sign in both heads; the original-gradient terms have opposite
signs. The prose now agrees with the displayed and formally checked formulas.

## Re-centering is not a monotonicity-preserving map

Reported before correction on 2026-11-09. The CNN split theorem allowed optional
input-dependent min re-centering while asserting convexity and coordinatewise
monotonicity whenever WTA pooling was absent. The proof already omitted
re-centering for its convexity argument; the statement needed that restriction
too. Re-centering (max(p,n), n) gives (ReLU(p-n), 0). At p=2, increasing n from
0 to 1 decreases the first output from 2 to 1. The theorem now requires no
input-dependent re-centering for its convexity/monotonicity part, while retaining
difference recovery and nonnegativity. The hidden paper's stabilization text
likewise distinguishes the unshifted mathematical heads from re-centered values.

## Nonnegative routing contraction factor

Reported before correction on 2026-11-09. The routing randomization theorem
required only bbar<1, with a row-mass condition on states alive in both models.
If that set is empty, the condition is vacuous and allows bbar=-1; at one layer
the claimed nonnegative overlap bound by bbar is false. The paper and thesis now
state 0<=bbar<1 explicitly. The downloaded arXiv PDF and source archive remain
unchanged provenance copies; only the extracted working paper source is corrected.

## Empty routing streams and absorption histories

Reported before correction on 2026-11-09. At epsilon=0 an alive RG neuron can
have an empty sign stream. Its half-branch probability must be absorbed, contrary
to the printed assertion that the cemetery row is only the dead-neuron indicator.
The act-only marginal now has a residual cemetery row and an explicit empty-stream
convention. The positive-epsilon cemetery contribution is weighted by the half
branch and the gate continuation probability. The alive-mismatch lemma now
distinguishes zero ordinary overlap from zero full overlap (the latter requires
no cemetery leakage from the alive row).

This also invalidates the unrestricted claim that deleting routing states is a
trajectory bijection preserving full Bhattacharyya/Hellinger distances. With x=1,
W=1, model A bias0 and model B bias-2, A can absorb at an empty negative branch
and B stops earlier at its gate. The refined histories are disjoint (BC=0),
whereas the collapsed act-only histories have cemetery overlap 1/sqrt(2).
The corrected text retains the refined gate/branch/routing histories for full
diagnostics and states the coarsening inequality. Equality still holds for
ordinary surviving paths, hence for survival-conditioned laws.

The pinned official implementation already applies gate and empty-branch
absorption separately (`bwgame/xai/methods/hellinger.py`, commit
9cae01ce429c34b295aa06dd056895ddd4ef9ff7, gate lines543--584,
branch lines507--516 and813--831). The code and reported experimental values
were not modified by this correction.

## Name of the multiplicative representation class

Reported before correction on 2026-11-09. The simplified multiplicative theorem
called its exact outputs ordinary Maxout networks. Such networks are piecewise
linear and cannot represent xy exactly. The statement now says Maxout
multiplication networks, matching the architecture defined in the appendix.

## Adversarial review corrections (2026-11-09)

- Routing activation ties: at the author’s explicit request, retain log-space preferences and select stopping for every log-space tie. Ties occur for all nonpositive signed continuation masses. Updated both source copies, the defining policy/value equations and the uniqueness discussion. The selected policy and forward routing formulas are unchanged. The global network interpretation assumes nonnegative activations; GeLU arguments remain local to frozen forward gates.
- Shifted intermediate sensitivity bulk includes the product of subsequent factors `(1 - 2 alpha)`, already present in the checked recurrence.
- Backward induction determines a unique value, while tied actions can give distinct optimal policies.
- Support-function domains require nonempty finite generators; the halfspace characterization of polytopes requires boundedness. Polytopes in R^d may have dimension below d.
- Homogenization preserves evaluation on the affine slice but does not make every lifted vertex attainable there. Retain only slice-visible vertices and project their gradients. The retained audit proves a triangle counterexample.
- The eta-zero example now uses canonical sign parts (W=1, b=1); later eta-zero streams need not be convex or concave.
- Regularizer maximizer choices preserve the reconstructed difference, but may change the two components; the selection is part of the definition.
- Continuous weight randomization alone does not guarantee distinct normalized RG rows. The strict conditional overlap bound remains an explicit theorem hypothesis.

Independent audit snapshots and executable evidence are in `reports/adversarial-*.json` and `reports/evidence/`; these are retained as records of the reviewed pre-repair sources.

The affine-output convention is now explicit in the foundational tropical recursion, all thesis decomposition families, the saliency masks and the Hidden Monotonicity source: hidden layers use the pair activation; the last layer copies the affine preactivation pair. Uniform backward notation uses M_L^+=I and M_L^-=0, so the final auxiliary Q term is zero. New checked readout wrappers include actual biases and terminal partial seeds.

The activation–occupation theorem distinguishes actual derivatives on strict open cells from selected backward computations at ties. A fixed ReLU backward value at zero does not create a classical derivative of a discontinuous stopping head. The SG diagnostic now absorbs zero-fan-in rows. The RG diagnostic is explicitly separated from the bias-inclusive game because dropping and renormalizing bias routes changes the kernel. Alpha–beta conservation accounts for nonempty participating streams and absorption.

The pinned PTNB implementation uses strict positive ReLU gates in Routing Game and Hellinger (`routing_game.py` and `hellinger.py`), matching the author-selected log-space stop-at-tie policy. Its separate SG/DC hard backward masks in `operations/relu.py` and `alignment_cache.py` use greater-than-or-equal at zero. The source now identifies these separate conventions explicitly; no upstream algorithm or published table was silently changed.


### Alternative activations represented by ReLU subnetworks

Reported during the source-to-thesis omission audit: the Hidden Monotonicity implementation paragraph claimed that ELU and Swish could be handled by replacement with small ReLU subnetworks without an approximation qualification. Finite ReLU networks are continuous piecewise affine; ELU and Swish are not piecewise affine, so exact global replacement is impossible. The source paragraph and thesis now state that this route approximates the original activation and preserves the approximating network. The thesis's curvature construction remains a separate exact decomposition under its stated hypotheses.


### Global routing-game strategy and zero-support conventions

The all-profile Lean proof uses the original extended-log utilities with pure activation choices and stochastic routing. Both source and thesis now state off-equilibrium evaluation and the zero-probability-times-minus-infinity convention explicitly. The outside score is ell(epsilon), including epsilon=0. Gibbs uniqueness applies on the nonempty finite-score face; when every score is minus infinity, all routing distributions are optimal and the canonical policy selects absorption. Activation log ties explicitly select stopping, as requested. The stopping parity proof now includes zero-weight paths explicitly (their product is zero).


### Floating-point invariant versus exact algebra

The source-to-thesis merge audit distinguished the original paper's reported float64 setup from the pinned code's configurable precision (float32 default). The thesis no longer claims that cache assimilation enforces the real-arithmetic recovery identity exactly in floating-point arithmetic: it targets that identity, while roundoff remains possible. The numerical setup and the independently checked exact mathematical invariant are both retained.

The short gradient and routing theorem statements are now aligned with the detailed proofs: strict-cell classical derivatives are distinguished from selected backward quantities at ties, and the general-temperature routing stop policy uses game continuation values. The anchor gate is 1[z>0]. The former headline uniqueness qualifier limited to zero activations has been replaced by the explicit log-tie and empty-stream selection already used by the detailed theorem.
