# Constructed native evaluator entry and lookup prefix

Date: 2026-11-18. Baseline: `05b2519` on `Droschinsky-algos`.
Thirteen proof modules add 64 public checked theorems. The actual parsed
113-local evaluator entry and its first eleven instructions, through the lookup
call and checked result store, now execute from independent native readable
packets and complete ownership. Every selected move/write permission in this
prefix is derived. No successful evaluator/callee run, expected output, supplied
post-argument ledger or post-callee frame is an input to the totality endpoints.

This is a common-prefix result. The three following storage-dead operations,
switch and cache-hit/empty-query/pair-pair branches, recursive budget composition,
return/closure, public maximum and the remaining planning targets are still open.
There is no W06-C3/SRC-01, full evaluator or full-goal closure.

## Native shared referents and actual loan permissions

`SourceNativeLoanCells.lean` introduces independent structural `NativeData` and
partial-mask `LoanSafe` predicates. Native words, embeddings and tables contain
no references or empty unit tuples. A `LoanSafe` mask can contain shared views
of these native values, owned children, ordinary data and holes. It does not
require disjoint shared graphs or prohibit query/table aliases.

`Graph.{native_cell,native_reads,shared_native_reads}`, `read_native_root`,
`BorrowFootprint.safe_cells` and the corresponding fields/local/inventory lemmas
prove that a shared loan under this invariant cannot include a stored cell that
is an uninitialized empty-tuple sentinel or another shared-pointer cell. Inline
pointer paths are included: `fields_invalid_cell` rules out descending through
those nullary cells. This uses the full existing graph/loan relations rather
than a source scan or pointer-root-only approximation.

`SourceNativeLoanPermissions.lean` proves native encodings satisfy the structural
predicates, and preserves `LoanSafeState` through initialization, updates and the
existing reference-ending operation. `RootLoansAllowed.of_safe_preserved`
discharges a destination's actual current loans from its sentinel cell, and old
caller loans from their preserved complete read bound and the callee root's
fresh address. `PacketLoansAvoid.of_safe` and `ExpressionLoansAvoid.of_safe`
discharge the corresponding payload loan checks.

`allowed_shared_local` derives the actual permission to move a reference local.
Its raw stack cell contains a shared pointer, which native shared referents
cannot read. Preserved older caller reads remain below every fresh callee root.
The existing physical move theorem then handles complete read/owner guards.
This neither bans all active-owner/shared-loan intersections nor asserts that
arbitrary reference-containing/unit referents satisfy the new invariant. The
older general loan contracts remain available for those values.

## Forward native machines and faithful prefix composition

`SourceLoanSafeMachine.lean` retains valid active/actual-caller/world storage,
separate active/caller roots, fresh-root bounds, native shared safety, protected
old caller bytes, complete owner-frame and live-Box coverage. Its `prepare`,
`storageLive`, `assign_empty` and `move_reference` rules construct existing
operations and their guards. It has no blanket owner/loan-disjointness field.
`SourceLoanSafeCalls.lean` preserves the invariant across whole existing calls
with closed output types, using source typing and the existing complete actual
call preservation/ownership contracts.

`Calling.Prefix` in `SourceCallingPrefixes.lean` records successful instructions
of the existing executor while retaining their actual continuation for
`forgetRefs`. `Prefix.{append,exec}` compose those steps and any later successful
suffix back into the unchanged calling executor and its real costs.
`Prefix.noncall_callee` transfers the constructed non-call steps to any backend,
even though their actual continuation contains calls. It excludes calls only in
the recorded prefix itself. This is a trace relation, not a replacement source
interpreter or altered reference-ending algorithm.

`SourceEvaluatorBorrowProgram.lean` splits the pinned evaluator into its first
ten storage/reference actions and the real lookup continuation. The kernel
checks each input local remains observed at the relevant program points.
`storage_prefix_complete`, `table_views_complete`, `query_view_complete` and
`borrow_prefix_complete` construct those ten actions, with fresh empty result
storage and the table/left/right lookup views in locals 5, 7 and 8. Existing
last-use preparation is applied before every instruction with the real suffix.

## Actual lookup and parsed entry

`SourceEvaluatorLookupPrefix.lean` proves `body_lookup_prefix` and
`actual_body_lookup_prefix`: the eleven-action prefix followed by `afterLookup`
is exactly the existing body and actual pinned source body.
`lookup_arguments` derives the local source operand step. `lookup_call_complete`
derives selected reference moves, post-argument native safety and destination
loan permission, then applies constructed recursive helper totality to the
actual lookup call and store. It supplies fixed sufficient fuel/readback
thresholds, one final world/activation/full call cost and exact source-action
agreement for all larger pairs of bounds. The lookup answer is not an input.

`lookup_call_machine` and `lookup_prefix_complete` retain the native machine
invariant, protected original caller reads and complete ownership/coverage after
the call. The latter composes all eleven real instructions at the stable bounds.
The prefix relation retains existing instruction costs; a complete evaluator
result/cost theorem still requires constructing the remaining suffix.

`SourceEvaluatorEntryCertificate.lean` accesses the actual typed parser's
evaluator declaration, with checked function, local count 113 and whole-body
identity (`CallingCertificate.{originalEvaluator_spec,evaluator_lookup}`).
`SourceEvaluatorEntryPrefix.lean` proves `entry_lookup_complete` for arbitrary
native left/right words and warm table, arbitrary readable physical packets,
actual callers and complete initial owner resources. It constructs the real
entry, all eleven instructions and the returned machine invariant. Its bounds
need no supplied native height or successful parent/callee execution. Query,
table and caller read aliases remain allowed; cache soundness is unnecessary.

## Consumer and boundary checks

`Tests/SourceAddressedControl.lean` applies the new entry endpoint where both
query pointers select inline words inside the same entry Box owned by the input
table. Independent graph/readability, table ownership, uniqueness/classification
and complete live-Box coverage are proved for that fixture. The theorem
constructs the actual parsed entry/common prefix and final native machine
invariant at every larger sufficient fuel/readback pair. This exercises an
owner/loan intersection that a blanket separation premise would reject.
Negative kernel examples establish that unit and reference-containing referents
are outside `NativeData`.

The new proof modules contain no admissions or added axioms. Generated Rust/Lean,
maintained Rust/Python, source semantics, source snapshots and dependency pins
are unchanged. The statements' independent storage/readability/complete-owner
premises are not a universal physical-success claim for the unfinished suffix.

## Validation

- Full maintained library: 4,035 jobs pass; replayed warnings are in older modules.
- `SourceAddressedExpressions`, `SourceAddressedControl`, `SourceHelperCalls`
  and `SourceOwnerLifecycle` pass.
- `BaselineAudit.lean`: 1,465 distinct endpoints, including all 64 new public
  theorems; only `propext`, `Classical.choice`, `Quot.sound`.
- Ten selected `leanq statement` seeds: 1,097 unique elaborated records and
  zero unknown references.
- `SourceRecursiveExecution` passes all eight cold/nonempty/cache-hit/overflow/
  failure runtime cases with complete source values/full costs, caller bytes,
  unique live Box ownership/coverage and cleanup checks.
- Broader 47-suite/native-WP/nine-Python evidence remains at `d49f638`;
  thirteen ordered Rust tests remain evidence at `823df34`. These are not fresh
  runs of this increment; Rust/runtime source did not change.

Reproduction from the repository root:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-native-prefix-statements.json \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Graph.native_reads \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.BorrowFootprint.safe_cells \
  SubtreeProofs.Rust.SourceEval.Addressed.allowed_shared_local \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.RootLoansAllowed.of_safe_preserved \
  SubtreeProofs.Rust.SourceEval.Addressed.LoanSafeMachine.advance_call \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.exec \
  SubtreeProofs.Rust.SourceEval.Evaluator.actual_body_lookup_prefix \
  SubtreeProofs.Rust.SourceEval.Evaluator.borrow_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.lookup_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_lookup_complete
```

All seven listed caches are guest-ext4 bind mounts. Lake/Lean commands run from
`proofs` to use its pinned toolchain. Machine-local logs are
`/var/tmp/subtree-native-prefix-{build,control,expressions,helpers,lifecycle,
runtime,axioms,statements}.log` and `subtree-native-prefix-statements.json`.

## Next work

Construct retirement of lookup temporaries and the cache-hit branch, retaining
the actual end of local 6's reference view before moving table local 3. Then
construct empty-query insertion/return and all pair/pair recursive, overflow and
failure paths. Derive each source-point scope/mask/move/destination/transfer
permission and sufficient stable budgets, preserving allowed native aliases.
Interpret dynamic parsed regions and destructor instances, finish public
maximum/cold-table teardown, wrappers/input policy/global resources/G3, and every
other target in `docs/planning`. The full goal stays active.
