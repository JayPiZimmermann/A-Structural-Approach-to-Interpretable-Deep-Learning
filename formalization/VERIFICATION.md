# Verification evidence

The previous 126-theorem receipt described an older snapshot and is superseded by the current verification workflow. No whole-thesis completeness claim follows from a build or an axiom count.

Run `python3 scripts/verify.py` from this directory for the publication gate. It requires a committed clean source closure, builds every production module reachable from `All`, rejects omitted modules, checks independently reviewed expected theorem types and universe arities, and audits the axioms of every project theorem in the imported Lean environment (including generated declarations). It checks that sources did not change during the run.

The output directory contains the exact generated Lean driver, command logs and exit codes, imported theorem types, source and artifact SHA-256 hashes, and the Git commit. `--diagnostic` explicitly labels a run on development files; it is not a clean publication certificate.

The reviewed expected types are maintained in `verification.json`. Mathematical source scope and remaining proof obligations are maintained in `coverage_map.json`, with the generated source statement inventory in `claim_inventory.json`. `Audit.lean` remains a convenient readable secondary audit, not the authority for import completeness.

Independent adversarial reports and executable counterexamples are preserved in `../reports/adversarial-*.json` and `../reports/evidence/`. Those reports describe their hashed pre-repair snapshots; repair reports and newer receipts record what changed.
