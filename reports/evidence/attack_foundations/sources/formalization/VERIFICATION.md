# Verification record

Checked locally on 2026-11-09 with Lean/mathlib v4.35.0.

- `lake build`: passed (3391 jobs in the complete dependency closure).
- `lake env lean Audit.lean`: passed; all mapped Lean identifiers resolve.
- `#print axioms`: 126 theorem declarations checked. The transitive trusted
  axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`.
- No `sorryAx` appears in the transitive audits. No project `sorry`, `admit`, or
  custom `axiom` declarations occur in the Lean source files.
- `python3 scripts/inventory.py`: 146 explicit source statements inventoried;
  21 formalized variants, 30 partially covered, 2 encoded definitions, 93 not formalized.
  Repeated source/thesis wrappers are counted separately. This is not a count
  of independent verified theorems and is not a whole-paper certificate.

Regenerate the checks with `python3 scripts/audit.py`, then `lake env lean Audit.lean`.
`build.log` and `audit.log` are local generated outputs and are ignored by git.

Important limits are documented in README.md and individually in coverage_map.json.
