# Verification evidence

The clean committed gate passed at source commit `0f3cfb0ea660556c14da510e665281f07acc471d`: 139 imported modules, 370 independently reviewed exact declaration contracts, and 3,048 imported project theorem constants audited for axioms. All 140 commands exited zero, and the source/configuration snapshot remained unchanged. Accepted axioms are `propext`, `Classical.choice`, and `Quot.sound`. No whole-thesis completeness claim follows from these counts.

The receipt and its referenced logs/artifacts are in `../reports/verification/current/` and archived in `../reports/verification/commit-0f3cfb0/`. The older verified receipt and referenced evidence remain archived under `commit-7c3c9c2`. Use the current receipt's command list and hashes; the working `current` directory may also retain unreferenced older logs.

The Softplus Circuit and conditioned-trajectory batches are included in this verified root. The independently reviewed six-module routing extension remains outside it; see `../reports/routing-bridge-handover.md`. Its focused review does not replace the clean gate required after production promotion. `../reports/lean-resumption.json` summarizes bootstrap, integration, verification, and outstanding scope.

Run `python3 scripts/verify.py` from this directory for the publication gate. It requires a committed clean source closure, builds every production module reachable from `All`, rejects omitted modules, checks independently reviewed expected theorem types and universe arities, and audits the axioms of every project theorem in the imported Lean environment (including generated declarations). It checks that sources did not change during the run.

The output directory contains the exact generated Lean driver, command logs and exit codes, imported theorem types, source and artifact SHA-256 hashes, and the Git commit. `--diagnostic` explicitly labels a run on development files; it is not a clean publication certificate.

The reviewed expected types are maintained in `verification.json`. Mathematical source scope and remaining proof obligations are maintained in `coverage_map.json`, with the generated source statement inventory in `claim_inventory.json`. `Audit.lean` remains a convenient readable secondary audit, not the authority for import completeness.

Independent adversarial reports and executable counterexamples are preserved in `../reports/adversarial-*.json` and `../reports/evidence/`. Those reports describe their hashed pre-repair snapshots; repair reports and newer receipts record what changed.
