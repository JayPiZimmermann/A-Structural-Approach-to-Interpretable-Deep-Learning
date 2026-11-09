# Conditioned survival with zero support

`Thesis.ConditionedSurvival` removes the global nonzero-potential premise from
the earlier `Games.doob_survival_path` result. It works on the existing actual
`Games.Paths`, `pathLaw`, `endpoint`, and `backwardDP` definitions. No existing
production module was changed.

The frozen source is `formalization/Thesis/ConditionedSurvival.lean`, SHA256
`1e7539c0f323f6bab04d66c673b7b8fe64fe71eba42ed20e104df3bf6456a756`.

The ordinary-state kernel `K` is nonnegative and has row sums at most one.
Missing row mass represents failure to survive. The horizon is `N`; index zero
is the starting layer and index `N` is the terminal ordinary layer. The actual
survival potential is computed by `backwardDP (N-i)` with terminal payoff one
and the shifted original kernel. Its terminal condition, recurrence,
nonnegativity, upper bound one, and equality with the total original surviving
path mass are all derived.

The conditioned kernel explicitly divides only when the current potential is
strictly positive and otherwise returns zero. Positive rows sum to one; dead
rows sum to zero, and transitions to a zero-potential target vanish. This is a
kernel on the original finite ambient state space with explicit zero support,
not a globally stochastic extension invented at dead states.

The central `weighted_path_identity` proves

```
pathLaw n (kernel K h) s path * h 0 s
  = pathLaw n K s path * h n (endpoint n s path).
```

It assumes nonnegative `K` and `h` and the finite-horizon recurrence, but does
not assume any strictly positive potential. The zero-start induction case uses
the fact that each summand of a zero nonnegative recurrence row is zero.
Consequently the proof does not cancel a zero intermediate denominator.

`stateAt` reads the actual state after a specified number of transitions on an
existing `Games.Paths` trajectory. `path_support_positive` proves that every
visited state of a nonzero conditioned path has positive potential, provided
only that the initial potential is positive. Its contrapositive is the explicit
pruning bridge `path_zero_at_zero_potential`. This support proof needs neither
a recurrence hypothesis nor nonnegativity of `K`, and its theorem type has no
unneeded `Fintype` instance.

For the computed survival potentials, `survival_conditioned_path` gives the
original surviving path sublaw divided by its positive initial total mass.
Summing that exact identity proves `survival_conditioned_normalized` despite
the dead rows. `survival_zero_path` separately proves that zero initial survival
forces every original full surviving path mass to be zero; no conditional law
at an event of probability zero is asserted.

The source-facing combined theorem is
`Thesis.ConditionedSurvival.conditioned_survival`. It collects the computed
potential bounds, boundary and recurrence, total mass, row normalization,
zero-target support, normalized full path identity, and actual path pruning.
Its only strict positivity premise concerns the initial survival probability.
Zero-length paths and zero-survival intermediate states are included. An initial
state is explicitly supplied, so an empty state space introduces no spurious
existence claim.

This closes the zero-support omission in the survival recursion and path-law
parts of `ptnb:thm:conditioned-survival`. The leaf does **not** on its own state
the theorem's conditioned layer-marginal identity, geometric-kernel identity,
or Bhattacharyya/Hellinger formulas. The existing `Games` overlap lemmas are
separate results; they are not silently treated as composed source clauses
here. The model uses the existing fixed finite ordinary-state ambient space,
rather than a new theorem about a framework's cemetery or graph converter.

Six independently specified exact theorem contracts are in
`reports/conditioned-survival-expected-types.json`. Their literal authoring
source is `reports/evidence/conditioned-survival/expected_types.py`; the types
were not extracted from Lean declarations. Production compilation and all six
direct type/module/universe checks passed. The imported environment audit
checked 109 project theorems against only `propext`, `Classical.choice`, and
`Quot.sound`.

The adversarial consumer in `reports/evidence/conditioned-survival/Adversarial.lean`
uses two states and two transitions. Half the original first-step probability
enters a state with zero future survival. It checks the derived initial
survival value one half, both intermediate survival values, the ordinary
positive dead-state prefix mass, the zero conditioned dead transition, the
normalized surviving trajectory, and both entries of the dead transformed row.
Final test status and hashes are recorded in that directory's receipt.

Reproduce from `formalization` with sequential commands:

```
lake env lean -o .lake/build/lib/lean/Thesis/ConditionedSurvival.olean Thesis/ConditionedSurvival.lean
lake env lean ../reports/evidence/conditioned-survival/ExactTypes.lean
lake env lean ../reports/evidence/conditioned-survival/Adversarial.lean
```

These are focused development and review receipts. The root agent owns the
public-import integration and clean committed-closure certification.
