# Constructed pair/pair head recursion and result scope

Date: 2026-11-18. Baseline: `54b1a96` on `Droschinsky-algos`.
Nineteen new proof modules provide 34 public checked theorems. The actual parsed
pair/pair miss path now constructs all twenty-six head-prefix instructions,
including the actual recursive head call, argument retirement, native result/
table extraction and inspection at the head-result switch. The principal
endpoint is `SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_head_scope_complete`
in [`SourcePairHeadScopeEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairHeadScopeEntry.lean).

This is an inductive step, with explicit universal totality for the strictly
smaller head query pair. It does not prove universal pair/pair totality, either
selected branch after the head-result switch, or the parent return/closure.
The consumer discharges the head contract using the proved empty-input base
case. Earlier complete cache-hit and empty-query miss endpoints remain checked.
Full SRC-01/C3 and the full planning goal stay open.

## Native contract and explicit recursive premise

`SourceEvaluatorNativeTotal.NativeTotal left right` quantifies over arbitrary
well-formed worlds, valid actual callers, native readable shared query/owned
table packets, complete input/caller/external owner resources and protected
caller reads. Its conclusion constructs fixed sufficient fuel/readback bounds,
a fixed final world/packet/full cost, the exact independent native result/table,
readability, well-formedness, preservation, complete ownership and live-Box
coverage. Every larger bound pair returns the same world/packet/full cost.

`native_empty_total` proves this complete contract whenever either query is
empty, for arbitrary warm tables, by splitting independent native lookup and
reusing `cache_hit_total` or `empty_miss_total`. No cache-soundness or global
owner/loan disjointness premise is added.

The head checkpoint takes `NativeTotal lh rh` for a parent request
`(Pair lh lt, Pair rh rt)`. `head_request_smaller` proves the strict decrease in
the sum of native Dyck semilengths, matching the existing functional/source
termination measure. No global instance of pair/pair totality is introduced.

`Derived.evaluator_call_total` constructs one actual caller argument evaluation,
scan, suspended context, complete owner transfer and result store from that
smaller-request contract. It derives the actual child input packets and caller
guards, invokes the contract with complete resources, transports the suspended
context, and stores the closed native output. Fixed sufficient bounds preserve
the exact whole-call world/activation/full cost; actual source action agreement
holds at every larger pair. This theorem does not assume successful execution
of the parent call or a supplied post-callee frame. Shared caller/query/table
aliases remain allowed.

## Shared routes and original loan origins

`SourceSharedRoute.SharedRoute` records that a source place crosses an existing
shared reference. Inline projections and owned dereferences before the crossing
introduce no new loan to the starting stack root. `BorrowFields.get_selected`
and `BorrowFootprint.read_shared` prove that every target read/root of the
reborrow belongs to the original borrow footprint. The proof uses actual
`locatePath`, partial snapshot reads and addressed graphs; it is not a source-text
scan or a replacement interpreter.

`LoanOrigin.borrow_shared` consequently constructs actual borrow success and
an addressed shared graph whose complete loans stay below the original bound.
`LoanOrigin.of_shared_graph` recovers the canonical local origin from an exact
stored pointer and graph using existing graph/resource uniqueness.

`OriginalLoanMachine.assign_borrow` and `original_borrow_view_complete` construct
fresh storage plus the guarded shared-view assignment, extending the original
loan family. The native safe-referent checks, current inventories, destination
write and old roots' raw-cell preservation are derived. Views of a boxed child
have native value `reference (boxed (encodeWord child))`; the later double
dereference produces the native shared word argument. A view may still point
inside a Box owned by the input table.

`OriginalLoanMachine.advance_call` preserves the original loan family through
an actual call with a closed output. Argument moves may clear family members;
unchanged members retain their exact resources via existing suspended-local
preservation. `original_move_view_complete`, `original_project_view_complete`
and `Prefix.frame_count` cover fresh closed moves, explicit partial inline
field moves and activation identity/count. These reuse the existing executor,
selected loan checks and complete ownership theorems.

## Exact twenty-six-instruction construction

`recurseHeads_actions` checks the unchanged pinned instruction list and real
head-result switch/continuations. The constructed checkpoints are:

- `pair_head_views_complete`: instructions 0–7 form the four actual Box-field
  views 27–30 from tuple 13. All new loans retain the pre-entry bound. Native
  table 3 and all old root cells are preserved.
- `pair_head_arguments_complete`: instructions 8–14 open result 33, reborrow
  the native head words into 34/35, and move table 3 into argument 36.
- `pair_head_call_complete`: instruction 15 constructs actual recursive
  dispatch and result storage from `NativeTotal lh rh`. Complete ownership,
  unchanged tuple/query origins, cleared argument masks and stable whole-call
  cost are retained.
- `pair_head_retire_complete`: instructions 16–18 retire argument roots
  36/35/34 while preserving the returned native tuple.
- `pair_head_unpack_complete`: instructions 19–25 move the optional result
  and updated table into 31/32, drop and retire the moved-out tuple 33, and
  open fresh empty payload storage 37.

`pair_head_prefix_complete` composes the first sixteen instructions and proves
native input queries and all four Box-field views remain available. It retains
the original empty return slot and moved table mask. `pair_head_scope_complete`
composes all twenty-six instructions into `PairHeadScope`: native queries,
query tuple, four native child views, native optional head result and updated
table, fresh empty payload/return roots, complete ownership, original loan
origins and exact live/retired/untouched root support. Its real continuation
is `headCases`, with both failure and tail-recursion branches intact.

`entry_pair_head_scope_complete` constructs parsed native entry, all fourteen
common lookup actions, all eleven miss-setup actions and this complete head
prefix at shared sufficient bounds. Independent native lookup selects the
parent miss. Actual addressed inspection of local 31 yields `lookupKey result`.
The proof keeps the linear prefixes and their actual continuations explicit;
it does not yet compose the selected head branch and outer parent return.

## Consumer, checks and boundaries

The extended `Tests/SourceCacheMissSetup.lean` uses the existing four-Box native
table fixture. Both parent queries select the same nonempty word in its owned
entry, so all four Box-field views overlap. The table's key is `(Empty, Pair
Empty Empty)` while the parent request is `(Pair Empty Empty, Pair Empty Empty)`;
lookup independently misses. The head request is empty/empty, whose complete
contract is proved. Without a child-success or recursive-totality premise, the
consumer obtains parsed/common/miss/head prefixes, native inserted head table,
complete original-loan machine, full `PairHeadScope`, retired root 33 and the
actual successful head-result inspection.

The 4,112-job root library build and all six affected Lean suites pass, including
the eight recursive runtime cases. The opt-in audit checks 1,686 endpoints,
including all 34 new public theorems, with only `propext`, `Classical.choice` and
`Quot.sound`. Ten elaborated statement seeds cover 1,322 unique declarations
with no unknown references. Thirteen ordered Rust tests and nine standalone
Python frontend regressions freshly pass. The full 47-suite/native-WP evidence
at `d49f638` is inherited, not rerun. No Rust source, generated extraction,
interpreter semantics, parser, tooling or dependency pin changes are included.

Reproduction commands, from the repository root unless shown:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
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
  --out /var/tmp/subtree-pair-head-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_head_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_head_scope_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_head_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_head_call_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.evaluator_call_total \
  SubtreeProofs.Rust.SourceEval.Evaluator.NativeTotal \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_empty_total \
  SubtreeProofs.Rust.SourceEval.Addressed.OriginalLoanMachine.advance_call \
  SubtreeProofs.Rust.SourceEval.Addressed.original_borrow_view_complete \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.BorrowFootprint.read_shared
```

All seven caches are guest-ext4 bind mounts; every Lake/Lean command runs from
`proofs`. Cargo metadata selects the mounted standalone-crate target; Cargo and
Rustup homes are ext4. Machine-local logs are
`/var/tmp/subtree-pair-head-{build,consumer,expressions,control,helpers,lifecycle,
runtime,axioms,statements,rust,python}.log`, with statement data in
`/var/tmp/subtree-pair-head-statements.json`.

## Next work

Use `PairHeadScope` to construct the selected head-failure cleanup/output path
and the successful-head/tail recursion, then score overflow, both contraction
requests, choice, final insertion and cleanup/return. Discharge all smaller-
request `NativeTotal` hypotheses by the actual complete pair/pair induction and
compose native routing, whole bodies and checked closure. Track fresh copied/
concatenated witness loans separately from original query origins. Dynamic
parsed regions/destructors, public maximum/cold-table teardown, wrappers/input
policy/resources/G3 and every other planning target remain. The full goal stays
active; no C3 or production runtime/resource closure follows from this increment.
