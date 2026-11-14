# Exact assignment core

`min_cost_assignment` solves square signed `i64` assignment instances using
Hungarian potentials. It returns a zero-based permutation, `i128` row/column
potentials and an `i128` total. Malformed matrices and checked-arithmetic
failures return explicit errors. Helpers separate column scanning, potential
updates, augmenting-path reconstruction and final decoding for extraction.
Row minima initialize feasible dual potentials for signed costs.

Current assurance is deliberately narrower than the crate's eventual target:

- Tests compare 320 signed matrices through dimension seven with an independent
  permutation enumerator. They also check dual feasibility, selected-edge
  tightness, bijectivity, extreme costs, empty inputs, malformed inputs and ties.
- Pinned Charon/Aeneas exports the actual source into
  `proofs/SubtreeProofs/Rust/Generated/VerifiedAssignmentCore.lean`.
- `Rust.AssignmentInitialization` proves safe terminating execution and exact
  contents of all four actual constant-fill initialization loops.
  `Rust.AssignmentRowMinimum` proves the actual row scan terminates and returns
  exactly the independent finite minimum, including membership and lower bounds
  for nonempty rows. `Rust.AssignmentPotentialInitialization` proves the actual
  vector initializer safely returns exact row minima and a feasible dual state
  for represented square matrices. `Rust.AssignmentColumnScan` proves exact
  slack relaxation and strict predecessor updates, including ties and absent
  slacks. `Rust.AssignmentScanInvariant` proves the complete scan terminates
  with exact table updates and an attaining global minimum among unused columns,
  under explicit representation and arithmetic bounds.
  `Rust.AssignmentAdjustmentLoop` proves the complete actual adjustment loop
  safely terminates with exact row, column and slack updates, using injectivity
  of used column pointers. `Rust.AssignmentAdjustmentFeasibility` connects those
  actual returned potentials to independent feasibility and tightness proofs.
  `Rust.AssignmentAdjustmentProgress` derives the cut cardinality, exact dual
  progress and reserved-column accumulator update.
- `Rust.AssignmentAugmentation` proves the complete actual path walk safely
  terminates with exact simultaneous pointer shifts. Discovery-rank forest
  conditions construct the required simple path. The independent `PartialRows`
  specification and actual `augment_matching_ranked_tight_spec` show that
  augmentation adds the fresh row, preserves unique earlier-row coverage,
  and retains tightness from tight predecessor edges.
- `Rust.AssignmentReconstruction` proves the actual complete decoder returns
  the inverse permutation, exact cost and copied potentials. Both source loops
  are verified; selected-cost sum safety follows from i64 values and the accepted
  dimension. `reconstruct_assignment_minimum_spec` proves the actual result is
  globally optimal from independent complete matching, feasible potentials and
  tight matched edges. The search and driver must still establish those premises.
- The search-capacity proofs derive unused free columns and the visit guard
  from partial matching. `Rust.AssignmentScanCut` proves the actual scan
  extends an independently attained cut minimum, including its physical
  predecessor; `AssignmentAdjustmentCut` proves the actual adjustment preserves
  it. Feasibility supplies nonnegative adjustment and the required cut bounds,
  while pointer injectivity supplies matching endpoint lockstep.
- `Shared.AssignmentDuality` proves the independent feasible/tight optimality
  criterion over ordered rings. The signed partial-assignment reduction and
  negative-infinity edge removal are proved independently.

- `Rust.AssignmentSearchArithmetic.adjust_potentials_from_search_spec` derives
  every actual adjustment arithmetic range from the independent search state
  and preserves feasibility, component envelopes, objective accounting and
  attained slack minima. Its reserved column value is the cumulative
  accumulator. The scan's checked ranges also follow from those envelopes.
  `AssignmentSearchInitialization` establishes the initial numeric and cut
  invariants from actual initialized contents and independent input row minima.

- Discovery-rank proofs connect visited columns to a finite acyclic predecessor
  forest. The actual scan preserves visited links; actual adjustment preserves
  all old matching edges and visited tight predecessor edges and makes the
  selected attaining predecessor edge tight. Boolean marking preserves the
  candidate and visit-count invariants.

- `Rust.AssignmentSearchLoop.find_augmenting_column_spec` proves the entire
  actual augmenting-column search safely terminates, including local vector
  initialization, every source guard and derived arithmetic safety. It returns
  a positive free column, preserves numeric and old matching tightness
  invariants, and constructs the ranked tight forest required by augmentation.

The full Hungarian driver, entry-point total
correctness, partial-matching adapter and complexity refinement remain open.
This crate is not yet a verified replacement for the graph crate's floating
matching API.

```bash
cargo test --locked --manifest-path rust/crates/verified_assignment_core/Cargo.toml
dev/regenerate_rust_lean.sh --check
(cd proofs && lake build SubtreeProofs.Rust.AssignmentInitialization)
```
