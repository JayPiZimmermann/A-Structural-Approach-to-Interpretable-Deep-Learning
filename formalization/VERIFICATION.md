# Verification record

Public snapshot checked locally on 2026-11-09 with Lean/mathlib v4.35.0.

- All 31 exported project modules built in dependency order.
- Final `lake build` passed (3409 jobs in the dependency closure).
- `lake env lean Audit.lean` passed.
- All 289 project theorems were checked with `#print axioms`; every mapped
  Lean identifier resolved. The only transitive foundational axioms are
  `propext`, `Classical.choice`, and `Quot.sound`.
- No project `sorry`, `admit`, custom axiom, or `sorryAx` was found.

This is a partial formalization. The theorem count counts Lean declarations,
including helper lemmas, not independent complete paper theorems.
`claim_inventory.json` records 146 explicit source statements with statuses:

- formalized_variant: 32
- not_formalized: 85
- partial: 27
- encoded_definition: 2

The source inventory counts repeated paper/thesis statements separately.
Its coverage statements and the theorem hypotheses define the checked scope.
Run `python3 scripts/audit.py` then `lake env lean Audit.lean` to regenerate
the exhaustive assumption checks.
