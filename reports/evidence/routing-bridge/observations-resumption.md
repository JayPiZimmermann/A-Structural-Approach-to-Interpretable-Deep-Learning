# Complete-history routing observations

Status: draft module freshly compiled (exit 0, empty log); six manually authored exact type/module/universe contracts and all 813 imported project theorem axiom closures passed. Independent semantic review and production promotion remain pending.

`draft/Thesis/RoutingObservations.lean` attaches scalar observations to the actual `RoutingProfiles.Tree` used by `RoutingNetwork`. Ordinary child histories retain their observations; activation stopping, bias, and outside histories remain distinct complete histories and carry zero ordinary-neuron observation. The integral uses the existing full-history probability and cumulative entered-state discounts from `RoutingHistory`.

The intended endpoint theorem identifies this actual full-history occupation with the independently defined `RoutingBackward.rgOccupation`, using total sign parity `Bool.xor` of starting and ending ownership. The proof route first derives route and layer integrals, then the recursive full-network observable, then identifies it with the pre-existing parity kernels. Alpha-beta coefficients may be arbitrary real numbers in the algebraic identity; a separate nonnegativity result assumes both coefficients nonnegative. Stabilizer zero and signed raw inputs are included.

For intermediate states, the observation marks the root of each actual prefix subtree while still sampling that entire lower history. `integral_root` integrates it to its mark. The exact append/propagate tree identity for a nonempty prefix identifies the complete history space with the original appended network game. This avoids defining intermediate occupation solely as an independent suffix recurrence.

Six full-forall contracts were manually written before compilation in `observations-expected-types.json`. The exact-type, module and axiom checks passed; independent semantic checks remain pending. `observations-check/receipt.json` binds the evidence to source hashes. Production files, imports and verification receipts remain unchanged by this draft.
