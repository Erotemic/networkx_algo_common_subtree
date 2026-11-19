# Typed helper totality and sufficient budgets

Baseline: `d49f638` on `Droschinsky-algos`. Four proof modules add 27 checked
public theorems. All eight existing helpers/intrinsics now execute on independently
typed readable actual arguments at some sufficient call fuel and ghost readback
budget. Source success, expected helper output, native height and cache soundness
are not input assumptions. The interpreted choice/evaluator/maximum still require
universal physical success; W06-C3/SRC-01 and the full planning goal remain open.

## Checked declarations

- `SourceReadbackBudget.lean`: `Partial.Addressed.{snapshot_depth,
  snapshotFields_depth,snapshot_enlarge,snapshotFields_enlarge}` and
  `Storage.{readPacket_depth,readPacket_enlarge}`. Successful readback supplies
  its finite depth bound. Larger ghost budgets preserve the exact value and
  complete read list/packet, including repeated read aliases.
- `SourceHelperNativeInputs.lean`: `Heap.SnapshotTyped.{shared_value,
  owned_value,native_word,native_result,native_entry,native_table}`. The existing
  independent snapshot types recover finite native words/results/entries/tables.
  Scores retain the original `u32` bound and reconstruct the exact scalar value.
  These shape lemmas assume neither an expected execution nor a sound cache.
- `SourceHelperReadiness.lean`: actual packet/type list inversion, readable
  shared/word/result/table/number packet bridges, `Helpers.Ready.enlarge` and
  `Helpers.typed_ready_exists`. Actual raw cells and snapshot metadata agree;
  the existing native helper depth bounds can be chosen from these inputs.
  `Recursive.interpreted function = false` selects exactly the six ordinary
  helpers and two intrinsics, excluding the three interpreted functions.
- `SourceHelperTotality.lean`: `Helpers.{finish_budget_enlarge,
  execute_budget_enlarge,Ready.executes,typed_total,typed_owned_total,
  typed_sufficient_fuel}`. The existing actual helper totality proofs provide
  concrete execution; increasing the ghost budget retains the identical world,
  packet and full cost. For every sufficiently large call fuel, some readback
  threshold works at every larger budget. The budget threshold may depend on
  the chosen call fuel; no global whole-program threshold is claimed.

`typed_total` assumes a well-formed symbolic world, readable independently typed
arguments, valid actual suspended callers and live protected addresses. It
constructs actual helper success and the matching pinned source execution with
exact cost, readable output, final world validity and protected-byte preservation.
`typed_owned_total` additionally assumes complete input footprints, a global
unique/classified/live owner frame and coverage of every live Box. It constructs
a complete output footprint and final output/actual-caller/external owner frame
and coverage. These initial owner resources remain explicit. Shared query and
insertion references can alias owned graphs. No parent success or supplied final
frame is used to establish helper existence.

All readback traversals and budgets are ghost observations, not production work
or allocator-time bounds. No Rust, generated Charon/Aeneas files, source/native
specification, interpreter, source hypothesis, cost model or pin changed.

## Maintained consumers and adversarial cases

`Tests/SourceHelperCalls.lean` now derives sufficient thresholds from independent
actual insertion packet types, with shared references aliasing the owned table.
It also proves that every budget at least 32 preserves the exact existing
insertion run. Existing zero-fuel/readback and oversized-scalar rejection cases
remain in that suite.

`Tests/SourceRecursiveExecution.lean` retains the cold empty/nonempty evaluator
and maximum checks, and adds five warm-table cases through actual parsed
recursive execution. The warm cache maps the empty query to a typed result with
score `2^32 - 1`; this cache need not satisfy the separate optimality invariant.
The tests compare complete source/actual values, returned table and full costs,
protected caller roots, owner uniqueness/live Box classification/coverage and
absence of stray live callee stack storage.

| Warm-table path | Exact source steps | Solver calls | Result |
| --- | ---: | ---: | --- |
| Cache hit | 271 | 1 | Cached result |
| Subtotal overflow | 911 | 3 | None |
| Root increment overflow | 1115 | 3 | None |
| Recursive heads failure | 1189 | 4 | None |
| Recursive tails failure | 1517 | 5 | None |

These executions test guards on previously uncovered overflow/failure branches;
they are not universal success or cache-soundness proofs.

## Validation and reproduction

The 3,992-job root build and all four affected helper/typed/recursive/runtime
consumer suites pass, including the three retained cold cases and all five warm
cache/overflow/failure cases.
The 1,270-endpoint audit includes all 27 new theorems and retains only
`propext`, `Classical.choice` and `Quot.sound`. Shared `leanq` inspection exports
828 unique statement records from eight selected seeds, with no unknown
references. This is selected statement coverage, not a whole-library export.
All seven cache mounts are guest-local ext4. Rust/generated artifacts are
unchanged; no fresh Rust/native-WP/Python or full 47-suite run is claimed.
Their preceding evidence remains recorded at `d49f638` (Rust at `823df34`).

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceTypedCalls.lean)
(cd proofs && lake env lean Tests/SourceRecursiveCalls.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-budget-statements.json \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.snapshot_enlarge \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.readPacket_enlarge \
  SubtreeProofs.Rust.LookupSource.Heap.SnapshotTyped.native_word \
  SubtreeProofs.Rust.LookupSource.Heap.SnapshotTyped.native_table \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.typed_ready_exists \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.execute_budget_enlarge \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.typed_sufficient_fuel \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.typed_owned_total
```

Machine-local logs: `/var/tmp/subtree-budget-{build,helper-tests,typed-tests,
recursive-tests,runtime,axioms,statements}.log` and
`/var/tmp/subtree-budget-statements.json`.

## Next obligations

Use this helper existence result in a forward whole-program physical-success
proof. Derive every actual move/write/drop/storage/return/close check from legal
native inputs/warm tables, complete owner resources, computed loans and certified
reference views, without assuming parent execution. Combine sufficient recursive
call/readback budgets across selected finite executions. Interpret dynamic parsed
region binders and destructor instances under the explicit source-operation
boundary. Complete native public maximum/cold-table teardown, wrappers/input
policy, global resources/G3 and the other planning obligations. None of those
requirements is replaced by the helper theorem or finite runtime cases.
