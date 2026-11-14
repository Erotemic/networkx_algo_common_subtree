# Exact assignment core

`min_cost_assignment` solves square signed `i64` assignment instances using
Hungarian potentials. It returns a zero-based permutation, `i128` row/column
potentials and an `i128` total. Malformed matrices and checked-arithmetic
failures return explicit errors. Helpers separate column scanning, potential
updates, augmenting-path reconstruction and final decoding for extraction.

Current assurance is deliberately narrower than the crate's eventual target:

- Tests compare 320 signed matrices through dimension seven with an independent
  permutation enumerator. They also check dual feasibility, selected-edge
  tightness, bijectivity, extreme costs, empty inputs, malformed inputs and ties.
- Pinned Charon/Aeneas exports the actual source into
  `proofs/SubtreeProofs/Rust/Generated/VerifiedAssignmentCore.lean`.
- `Rust.AssignmentInitialization` proves safe terminating execution and exact
  contents of all four actual initialization loops.
- `Shared.AssignmentDuality` proves the independent feasible/tight optimality
  criterion over ordered rings. The signed partial-assignment reduction and
  negative-infinity edge removal are proved independently.

The Hungarian phase invariants, arithmetic bounds, entry-point total
correctness, partial-matching adapter and complexity refinement remain open.
This crate is not yet a verified replacement for the graph crate's floating
matching API.

```bash
cargo test --locked --manifest-path rust/crates/verified_assignment_core/Cargo.toml
dev/regenerate_rust_lean.sh --check
(cd proofs && lake build SubtreeProofs.Rust.AssignmentInitialization)
```
