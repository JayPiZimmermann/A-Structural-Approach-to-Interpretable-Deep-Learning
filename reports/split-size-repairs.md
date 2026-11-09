# Shared multiplicative split size theorem

New leaves `HiddenMonotonicity.SplitDAGSize` and
`HiddenMonotonicity.MaxoutProductSize` prove the previously missing linear-size
clause. No frozen source module or root configuration was changed.

The source datatype `MaxoutProductDAG` is an actual topologically ordered graph.
Its Maxout gates carry a finite list of predecessor references and a vector of
signed weights on each incoming arc; their evaluator is the finite maximum of
these affine forms. Its multiplication gates evaluate the product of predecessor
values raised to natural powers. Parents may be any earlier node, including
shared and residual references. Biases are allowed directly. The source
`graphSize` counts input/internal neurons plus incoming arcs; each vector-weight
Maxout arc is counted once, independently of the rank.

`MaxoutProductGate.toExpr_eval` and `MaxoutProductDAG.toCircuit_eval` prove the
bridge to the existing signed-expression/Circuit evaluator. Powers use actual
repeated-parent lists, with a proved product identity and exact degree/length
relation. The primitive source definitions do not contain split correctness,
monotonicity, a size bound or a pre-existing expression-representation premise.

The constructed `SplitDAG` stores two positive expression trees at each original
node, with leaves referencing the earlier shared pair table. Its evaluator is
proved equal to the existing `Circuit.split false` pass. Each expression
constructor is a vertex; binary gates have two child arcs, unary scales have one,
and a reference leaf is represented conservatively as a one-edge identity-copy
vertex. Constants have no incoming arcs. The graph-size recurrence counts all
these local vertices and arcs. It does not count an arbitrary compound original
operation as one split node, and it does not inline earlier original nodes into
every consumer. The same positive graph can be read at either output stream.

The output grammar uses nonnegative coefficients and only binary maxima; its
proved maximum Maxout arity is two. Multiplication gates are ordinary binary
monomials. No ordinary convexity claim is made for products.

The source-facing headline
`HiddenMonotonicity.MaxoutProductDAG.split_linear_size` assumes only actual gate
rank at most `K` and total multiplication degree at most `D`. It constructs a
positive shared DAG with all of the following:

- maximum Maxout arity at most two;
- size at most `24 * 2^(max K D) * (4*K + 2*D + 1)` times source neurons-plus-arcs;
- exact recovery of every recorded source node for arbitrary split pairs;
- nonnegative outputs and monotonicity on nonnegative split inputs;
- finite maxima of nonnegative-coefficient polynomial expressions for both streams.

`compile_canonical_recovery` gives the literal identity on the canonical
`x⁺ = max(x,0), x⁻ = max(-x,0)` input split.

The chapter-7 headline `split_linear_size_expansion` instead assumes fixed rank
and a uniform bound `B` on the actual binomial expansion count
`product(power+1)` at multiplication nodes. The proof establishes
`sum(power)+1 ≤ product(power+1)` and derives the degree bound; compiled size is
not assumed. Its explicit linear constant is the preceding one with `D = B`.
No bound on the number of distinct inputs is substituted for a degree bound.

The intermediate bounded-duplication-depth theorem is used only inside the
compiler proof. Maxout rank and total product degree are shown to imply that
bound, and gate syntax size is independently bounded by original fan-in. These
bridges are what connect the generic expression compiler to the source claim.

Eight independent complete type contracts are in
`reports/split-size-expected-types.json`, including both source headlines and the
gate/graph/evaluator bridges. Focused sequential production compiles, explicit
contract examples and axiom checks are under `reports/evidence/split-size/`.
Only `propext`, `Classical.choice`, and `Quot.sound` are used; no custom axioms,
sorry or native_decide were added. `completed-frontier.json` records hashes.
Root retains responsibility for imports, mappings, publication and whole-import
clean-closure verification.
