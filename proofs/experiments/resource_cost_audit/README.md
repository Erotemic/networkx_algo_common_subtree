# Resource backend experiments

The subsequent [G1 decision](../../../docs/planning/lean-complexity-campaign/evidence/g1-backend-decision.md)
now checks all three candidates and selects this native route at C2. It retains
the source/RAM/IR and W06-C3 gaps explicitly. All final function signatures and
axiom closures are printed by `LookupSourceWP.lean`; comparison's result is stated
as independent word equality.

This directory contains the bounded G0 Std.WP signature check. It is deliberately
outside the main Lean library and introduces no dependency. From `proofs/`:

```bash
lake env lean experiments/resource_cost_audit/StdWPWorksheet.lean
lake env lean experiments/resource_cost_audit/LookupSourceWP.lean
```

The worksheet uses the existing Rust memo types and independent first-hit result
specification. It demonstrates how the installed `EStateM` interpretation states
a result/counter contract. It supplies neither a timed implementation nor a
source-to-cost theorem. The executed upstream checks and source operation
inventory are in [the campaign evidence](../../../docs/planning/lean-complexity-campaign/evidence/executed-g0-w02.md).

`LookupSourceWP.lean` is the bounded native-Std.WP leg of W03. It executes
the existing reified source interpreter, threads its complete `Cost` through
`EStateM`, and proves that successful WP contracts are equivalent to successful
operational runs with the same result and accumulated work. Lookup, structural
comparison, word copy and result copy have contracts; sequential composition
preserves the first call's work. An existing compiled Rust extra-comparison
mutation violates the old zero-comparison WP contract.

This is an adapter to the established operational C2 model, not another source
interpreter or a new proof of Rust/heap adequacy. Error-path work is unspecified;
the four contracts prove successful execution under their explicit sufficient
fuel hypotheses. The reifier and immutable-reference interpretation remain
trusted. Competing backend pilots and G1 route selection remain open. See
[the native WP evidence](../../../docs/planning/lean-complexity-campaign/evidence/lookup-native-wp.md).
