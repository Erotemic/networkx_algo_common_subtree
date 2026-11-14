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

`matching::max_weight_partial_matching` solves rectangular optional signed-i64
weights with forbidden edges and unmatched vertices. Its public total-correctness
theorem, `Rust.MatchingEntrypoint.max_weight_partial_matching_total_spec`, proves
an independently maximum matching with exact input-index pairs, no duplicate
list entries and exact i128 weight. It covers empty sides, nonpositive weights,
ties and extreme signed weights. Shape is checked before size; malformed shape
returns `NonRectangular`, and excluded dimension sums return `TooLarge`.
Admitted inputs have dimension sum at most `u32::MAX` and strictly below
`usize::MAX`; assignment and arithmetic errors are ruled out for these inputs.
The proof verifies actual dummy cost construction, assignment, decoding and
checked weight conversion. Two independent-injection tests cover 588 generated
rectangular cases and explicit edge cases.

`deletion::max_weight_matching_deletions` adds the original matching and every
right-vertex-deleted instance, preserving original indices. It copies the
original result for unmatched deletions and fully recomputes matched deletions.
Independent injection tests cover 392 generated matrices and edge cases.
Unmatched reuse and its affected-vertex count are proved mathematically; actual
endpoint detection, result copying and both matrix mask loops are verified.
The complete Rust family wrapper is still awaiting its refinement proof.
This reference API does not implement the paper's one-augmentation repair.

Graph/Python integration, rectangular and reused matching optimizations, and
implementation complexity proofs remain open.
The graph crate's floating matching API is separate from this exact core.

```bash
cargo test --locked --manifest-path rust/crates/verified_assignment_core/Cargo.toml
AENEAS_BIN_DIR=/path/to/pinned/tools dev/regenerate_rust_lean.sh --check
(cd proofs && lake build SubtreeProofs.Rust.AssignmentEntrypoint)
```
