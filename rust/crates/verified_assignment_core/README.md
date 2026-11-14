# Exact assignment core

`min_cost_assignment` solves square signed `i64` assignment instances with
Hungarian potentials. It returns a zero-based permutation, `i128` row/column
potentials and an `i128` total. Row minima initialize feasible potentials for
signed costs; absent slacks use `Option`, with no finite infinity sentinel.

The actual public API has a compiled end-to-end total-correctness proof:
`Rust.AssignmentEntrypoint.min_cost_assignment_total_spec`. It checks the
pinned Charon/Aeneas translation against an independent finite-permutation
specification. Every represented input terminates with either:

- An independently minimum-cost assignment, for square matrices of dimension
  at most `u32::MAX` with a representable reserved extent `n+1`.
- `TooLarge` for excluded size/extent, or `NonSquare` for malformed shape
  after size validation.

The success specification covers the actual returned permutation and exact
cost, potential vector lengths, all dual inequalities, selected-edge tightness
and primal/dual equality. It includes empty input and both extreme signed i64
values. Arithmetic and invariant errors are ruled out on admitted input;
all checked ranges and termination bounds are derived within the proof.
`min_cost_assignment_spec` states the admitted-input success contract directly.

The proof chain verifies actual row-minimum initialization, column scanning,
potential adjustment, discovery ranks, augmenting paths, the full outer driver
and final decoding. It assumes no supplied optimum, path or result certificate.
Pins, reproduction and the translation/operation/allocation model boundary
are documented in [VERIFICATION.md](../../../proofs/VERIFICATION.md). The final
opt-in endpoint dependency review is separate from routine compilation.

Independent Rust tests compare 320 signed matrices through dimension seven
against permutation enumeration and check bijectivity, dual feasibility,
tightness, extreme costs, empty inputs, malformed inputs and ties.

`matching::max_weight_partial_matching` adds a rectangular signed-i64 adapter
with forbidden edges and unmatched vertices. Two independent-injection tests
cover 588 generated cases and explicit edge cases. Its actual cost cell, row
and matrix construction are proved safe and exact against the mathematical
dummy reduction. Actual rectangular validation and both pair-decoding helpers
are proved safe, with exact indexed membership and no duplicate list entries.
The abstract reindexing bridge preserves maximum matching and negated-cost
weight; its concrete decoder/score connection and the public partial-matching
optimum refinement remain open.

Graph/Python integration, rectangular and reused matching optimizations, and
implementation complexity proofs remain open.
The graph crate's floating matching API is separate from this exact core.

```bash
cargo test --locked --manifest-path rust/crates/verified_assignment_core/Cargo.toml
AENEAS_BIN_DIR=/path/to/pinned/tools dev/regenerate_rust_lean.sh --check
(cd proofs && lake build SubtreeProofs.Rust.AssignmentEntrypoint)
```
