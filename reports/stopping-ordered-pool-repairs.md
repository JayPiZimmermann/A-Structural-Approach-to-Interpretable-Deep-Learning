# Source maxpool tie convention adapter

Independent review correctly identified a source-mapping gap: the frozen generic binary `stoppingExpr` / `expressionKernel` maximum chooses its RIGHT operand at equality, whereas PTNB `main.tex:1379` specifies the smallest maximizing operand index. Generic selected-operator identities are mathematically valid for their own convention, but cannot be promoted directly as that source convention for a naïve left-to-right pool encoding. Strict classical derivative statements are unaffected.

The NEW leaf `Thesis.StoppingOrderedPool` repairs the mapping without editing any frozen generic definition or theorem. `orderedPool` encodes a nonempty ordered finite pool into the existing binary syntax, placing earlier source operands on RIGHT branches. `earliestWinner_spec` proves that the selected index maximizes the represented value and is the least original operand index among ties, for every finite nonempty arity. This is an analytic proof over arbitrary real values, not a numerical sample or a modified source assumption.

`orderedInputPool_source` proves the exact chosen stopping pair and exact unit selected kernel in addition to the maximality/minimality clauses. It therefore handles tied represented scores with unequal stopping pairs, the reviewer's counterexample regime. `orderedInputPool_minimum_graph_index` additionally proves minimum graph-node index under the explicit source condition that the predecessor enumeration is sorted (`Monotone inputs`); arbitrary unsorted enumerations only claim minimum operand position. Repeated predecessors are allowed.

`orderedInputPool_dag_row` proves that the actual shared-DAG selected Jacobian rows at the newly appended pool node equal the positive/negative rows of the earliest maximizing predecessor at the actual graph forward state. Thus the already proved full-occupation selected-operator theorems apply with the source convention whenever source pools use `orderedInputPool`. This is the source-facing adapter to use for tie promotion; the old generic `.maximum (.input i) (.input j)` is still a right-tie primitive and should not be relabelled as a source-ordered pool.

`orderedPool_regular` proves the additional strict-cell adapter: a unique maximizing operand and regularity only of that winning operand imply regularity of the compiled pool. `orderedInputPool_regular` specializes it to actual graph inputs. In particular, tied values strictly below a unique maximum impose no hidden nested-tail regularity requirement.

Validation: the new module compiled sequentially. `reports/stopping-ordered-pool-expected-types.json` contains six independent full-forall source contracts. All six `example : EXPECTED := @DECLARATION` kernel checks passed, process exit 0. All six `#print axioms` closures are exactly `propext`, `Classical.choice`, `Quot.sound`. No sorry/admit/new axiom/native_decide. Root still owns independent review, source mappings, imports, and clean-closure publication checks.

Freeze SHA-256:

- Module: `69e40425e37c030c35086a464dfead11cd39e558dbe08d0ed61f4edc9615a91f`
- Contract manifest: `c3fb27ac0a3f04bd864a157ef06b7427779fe12a99dd2e540fffbd68d043e73e`
