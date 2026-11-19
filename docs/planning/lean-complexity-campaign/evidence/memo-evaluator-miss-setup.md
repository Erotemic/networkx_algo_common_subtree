# Constructed evaluator miss setup and native word routing

Date: 2026-11-18. Baseline: `480d2cd` on `Droschinsky-algos`.
Eleven new proof modules provide 40 public checked theorems. The actual parsed
native evaluator entry, common lookup prefix, all eleven cache-miss setup
instructions and both actual word inspections are now constructed from independent
readable native packets and complete ownership. The copied query tuple retains
only original query loans, including repeated table-owned aliases.

The endpoint is
`SubtreeProofs.Rust.SourceEval.Evaluator.entry_miss_setup_complete` in
[`SourceCacheMissEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourceCacheMissEntry.lean).
It reaches the initialized empty/recursive branch boundary; it does not assume
or prove successful execution of the following branch body. Empty-query insertion
and return, pair/pair recursion/overflow/failure, public maximum and full SRC-01/C3
remain open. The preceding complete cache-hit theorem remains checked.

## Exact inputs, scope and stable prefix conclusion

Inputs are the existing well-formed world, valid actual suspended callers and
their resource scan, readable native shared query packets and an owned native
table packet. Independent `FieldsFootprint`, `OwnerFrame` and `BoxCoverage`
cover all input/caller/external owners. Native
`MemoizedOrderedSolver.findResult table left right = none` selects the miss.
There is no cache-soundness, expected physical result, successful parent run or
all-owner/all-loan separation hypothesis.

The theorem constructs parsed entry, fixed sufficient helper fuel/readback
thresholds, the world/activation after the common lookup prefix and the
world/activation after miss setup. At every larger pair of bounds, actual
`Calling.Prefix` derivations retain these same worlds and activations for the
common prefix and miss setup with their real continuations.

The resulting `MissScope` retains native input locals, the exact query tuple in
13, a bound tuple root, fresh empty return storage 0, the original local count,
and all other roots equal to parsed-entry roots. Reference temporaries 14/15 and
the earlier result/view/lookup roots have been retired. Only locals 1/2/13 can
contain references. Every query loan, including loans inside tuple 13, lies below
the pre-entry world's memory length; its fresh tuple root is a local read rather
than a shared loan. Complete ownership and protected original caller reads are
preserved by the native machine.

Actual addressed inspection of tuple fields 0/1 gives the independent native
left/right word keys. The unchanged selectors route an empty left word to
`emptyLeft`, a nonempty left word to `rightCases`, and the right selector to its
empty/pair alternative. `emptyRight_eq_emptyLeft` checks that the two pinned empty
branches have identical instructions. Branch selection alone is not branch-body
totality or a whole-miss cost theorem.

## Structural word loans and exact packet assignments

`SourceWordLoanCells` proves `WordOpaque.fields`, `Graph.word_not_opaque`,
`Graph.word_reads_not_opaque` and `Graph.shared_word_reads` from the actual word
encoding and physical field projections. Tables whose inline fields are owned
pointers, shared-pointer cells, and reference-only tuples are word-opaque.
This does not forbid a query from borrowing an inline word inside a table-owned
entry Box. `WordLoans`/`WordLoanFields` and their resource-inventory theorems
identify actual loans from native word references, including nested tuples.

`SourceWordLoanPermissions` derives `WordLoanState` preservation and selected
root/move permissions from word-opaque cells, current word loans and the original
callers' preserved read bound. These supply reusable permissions for subsequent
table transfer. They do not replace the existing general move/loan checks or
assert that every native cell is word-opaque.

`SourcePacketAssignment.LoanSafeMachine.assign_packet_empty` constructs scanning,
retained inventories, ownership, guarded storage and the native machine for an
explicitly constructed physical RHS packet. `copy_shared_packet`,
`move_local_packet` and `aggregate_two_packets` construct the existing primitive
operand/expression runs from actual roots, raw cells, source masks and selected
permissions. These helpers retain raw shared-pointer identity, rather than
inferring pointer identity from equal snapshot values.

`SourceReferenceCopy.copy_reference_complete` constructs storage-live and reference
copy together, preserving the exact original pointer, native machine, untouched
root cells, closed outside-exception masks and original query-loan origins.
`SourceTupleLoanOrigins.LoanOrigin.tuple_shared` uses the two actual copied
pointers and canonical shared graph footprints to derive the tuple's loan bound.
Repeated pointers and overlapping query graphs remain permitted.

## All eleven actual miss instructions

`SourceCacheMissProgram.cacheMiss_actions` checks the unchanged branch identity.
`miss_observes_queries` checks original query observations throughout its setup.
The source-local tuple inspections are proved separately from physical inspection.

`SourceCacheMissRetirement.miss_retire_complete` constructs the first three
instructions: drop absent result 4 and retire ended table-view root 6 and result
root 4. It retains both native queries, the owned table and return storage.
`SourceCacheMissCopies.miss_copies_complete` constructs opening of tuple storage
13 and the two storage-live/reference-copy pairs for 14/15, retaining exact
query pointer cells and original query origins.

`SourceCacheMissAggregate.miss_aggregate_complete` constructs tuple assignment
13 and both storage-dead instructions 15/14. Its physical aggregate moves are
justified by the actual native reference-local permissions. The tuple's original
loan origins follow from the copied pointer graphs; they are not an input
permission assumption. Closed outside-exception masks and `WordLoanState` are
derived from actual source masks and valid unbound roots.

`SourceCacheMissScope.miss_setup_complete` composes all eleven steps and produces
`MissScope`. `miss_switch_native` constructs both actual word inspections and
checks their native routing. `entry_miss_setup_complete` composes the parsed
113-local native entry and common prefix with the constructed miss setup, using
the independent native miss answer and stable sufficient helper bounds.

No generated extraction, Rust/Python implementation, dependency pin, source
semantics, reference-ending algorithm or physical guard changed. All declared
instruction/destructor/call currencies remain in the existing executor. A whole
miss result/full-cost claim still requires insertion and the selected return or
recursive body. Compiler/reifier, dynamic parsed regions/destructor instances,
runtime and allocator adequacy remain explicit source-boundary obligations.

## Validation and adversarial consumer

All commands below terminate successfully:

- Full maintained library: 4,072 jobs; replayed warnings are in older modules.
- Six affected Lean suites: new `SourceCacheMissSetup`, plus
  `SourceAddressedExpressions`, `SourceAddressedControl`, `SourceHelperCalls`,
  `SourceOwnerLifecycle`, `SourceRecursiveExecution`.
- All eight recursive runtime cases retain complete values/full costs, protected
  caller bytes, live Box ownership/coverage and cleanup checks.
- `Tests/SourceCacheMissSetup.lean` independently builds a four-Box native table
  whose left key is empty and right key is nonempty. Both empty query pointers
  alias the same inline left-key word in the table-owned entry Box. Independent
  lookup therefore misses. The consumer obtains actual parsed entry and both
  stable prefixes, initialized tuple 13, original tuple-loan bound, complete
  native machine and successful actual left/right empty-word inspections. The
  new suite is included in the maintained verification workflow.
- `BaselineAudit.lean`: 1,599 distinct endpoints, including all 40 new theorems;
  only `propext`, `Classical.choice`, `Quot.sound`.
- Ten selected `leanq statement` seeds: 1,109 unique elaborated declarations,
  zero unknown references.
- Thirteen ordered Rust tests, including independent contraction/isomorphism
  oracles, choice materialization and token/index input behavior.
- Nine standalone Python frontend/reifier regressions.

Broader 47-suite/native-WP evidence remains at `d49f638`, not a fresh full-suite
run of this increment.

Reproduction from the repository root:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-miss-setup-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_miss_setup_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.miss_switch_native \
  SubtreeProofs.Rust.SourceEval.Evaluator.miss_setup_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.miss_aggregate_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.miss_copies_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.copy_reference_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.LoanOrigin.tuple_shared \
  SubtreeProofs.Rust.SourceEval.Addressed.LoanSafeMachine.assign_packet_empty \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.RootLoansAllowed.of_word_preserved \
  SubtreeProofs.Rust.SourceEval.Addressed.allowed_inline_word_opaque
```

All seven caches are guest-ext4 bind mounts. All Lake/Lean commands run from
`proofs`. Cargo metadata selects the mounted standalone-crate target; Cargo and
Rustup homes are ext4. Machine-local logs:
`/var/tmp/subtree-miss-setup-{build,consumer,expressions,control,helpers,lifecycle,
runtime,axioms,statements,rust,python}.log` and `subtree-miss-setup-statements.json`.

## Next work

Construct the actual empty-witness locals, table transfer, insertion reference
views, helper insertion call, post-call retirement and native output/return from
`MissScope`. Preserve the original tuple-loan bound while temporary embedding
views are live; derive each selected permission rather than excluding legal
query/table/caller aliases. Then finish all pair/pair recursive/overflow/failure
paths and stable budget composition, dynamic regions/destructors, public
maximum/cold-table teardown, wrappers/input policy/resources/G3 and every other
planning target. The full goal remains active.
