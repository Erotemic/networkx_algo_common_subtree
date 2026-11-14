# Resource backend API worksheet

This directory contains the bounded G0 Std.WP signature check. It is deliberately
outside the main Lean library and introduces no dependency. From `proofs/`:

```bash
lake env lean experiments/resource_cost_audit/StdWPWorksheet.lean
```

The worksheet uses the existing Rust memo types and independent first-hit result
specification. It demonstrates how the installed `EStateM` interpretation states
a result/counter contract. It supplies neither a timed implementation nor a
source-to-cost theorem. The executed upstream checks and source operation
inventory are in [the campaign evidence](../../../docs/planning/lean-complexity-campaign/evidence/executed-g0-w02.md).
