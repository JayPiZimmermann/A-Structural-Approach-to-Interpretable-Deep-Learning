# Verification runs

Receipts record their own status and source hashes; a diagnostic or failed run is not a publication certificate. The publication gate uses a clean committed import closure, with expected propositions elaborated independently before importing their proofs.

The first complete 80-module publication build at commit `0c138a9` passed. Its generated exact-type driver failed on universe-polymorphic contracts because it instantiated the expected-type constant without its explicit universe arguments. No source theorem or expected statement was changed to repair this driver bug. The generator now supplies the same reviewed universe arguments on both the expected type and the actual declaration. `universe-regression/` preserves the passing focused generic-pooling check. The failed driver and its `sorryAx` diagnostics belong to this archived checker failure, not to production proof declarations.
