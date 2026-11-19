# Actual parent insertion through output assembly entry

Baseline: `c432f5c` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [actual parent choices](memo-evaluator-parent-choices.md) are now followed
by all eighteen actual insertion instructions. Successful-right payload,
both choices, insertion setup/call and physical argument retirement construct
the first thirty-nine finish instructions and reach `finishCode 39`.
Output assembly and the subsequent finish continuation remain open.

## Mixed loan permission

`SourceMemoLoanOrigins.lean` defines `MemoLoanOrigins`: each local either has
an original bounded loan origin or contains only native word/embedding loans.
`OriginalLoanMachine.memo_origins` and `MemoLoanOrigins.prepare` construct and
prepare this guard. `Inventory.memo_cells_above` proves that a loan above the
original boundary cannot select a word-opaque cell. An original loan would
contradict its strict bound; a native word/embedding loan excludes that cell
by its actual referent graph. `allowed_table_local_with_origins` uses this to
construct permission for moving a fresh table root, retaining original caller
read bounds independently.

This does not restrict every original referent to a word or embedding. Original
query/table/caller aliases remain legal, including aliases into the table whose
ownership is transferred to insertion. Fresh selected-witness references can
borrow its fresh stack root and descendants without being misclassified as
original loans. No global alias prohibition or desired successful call is a
premise.

## Constructed insertion region

`SourcePairInsertSetup.lean` proves `pair_insert_setup_complete`. It constructs
indices 21--29: open output 104; move table 89 through new 105; reborrow original
queries 1/2 through new 106/107; open empty view roots 108/109. The original-loan
family extends by 106/107. The actual raw empty roots, moved table mask, native
argument snapshots, count/frame, other roots and previous root bytes remain
checked. Selected 99 and owned queries 71/85 retain their original heap bounds.

`SourcePairInsertViews.lean` proves `pair_insert_views_complete` for arbitrary
native selected witnesses. The actual assignments at indices 30/31 borrow
99 into 109 and reborrow 109 into 108. Both fresh views are native embedding
references. Every original loan origin and zero-owner mask is retained; closed
outside masks and the mixed loan guard are derived. Complete native machine
ownership/coverage, selected/owned-query bounds and older root bytes survive.

`SourcePairInsertCall.lean` proves `pair_insert_arguments` and
`pair_insert_call_complete`. Actual preparation at index 32 ends direct view
109. Moving 105/106/107/108 and storing the native insertion result in 104 are
constructed using the guarded helper totality API. The exact result snapshot is
`MemoTable.Entry ⟨left, right, result⟩ table`; source helper reflection identifies
the result of the actual call. Its fixed constructed world, activation and
complete call cost are stable at every larger shared fuel/budget pair. All five
argument/direct-view masks are empty. The original loan family, complete
ownership/coverage and selected/owned-query bounds are restored. The returned
table can retain original owners; it receives no all-fresh-owner conclusion.

`SourcePairInsertion.lean` proves `pair_insertion_complete`. It composes the
first eleven setup/view instructions, actual insertion call and six cleanup
instructions: physically retire 108/107/106/105, observe 104, retire 109. All
five temporary roots are unbound, all corresponding masks are empty, and table
104/selected 99 have their independent native values. Count/frame, untouched
roots and unshared masks, older root bytes and owner bounds survive. The public
statement exposes the actual argument/call checkpoints, stable call and full
eighteen-instruction prefix through `finishCode 39`.

`SourcePairFinishInsertion.lean` proves `pair_finish_insertion_complete`.
Starting at the earlier successful-right scope, it constructs payload extraction,
both choices and the full insertion region. `FinishInsertionScope` records the
original query tuple, ended child views, scalar/option holes, both owned queries,
selected witness, inserted table, moved masks and retired roots. The selected
witness and owned queries retain original heap bounds through all thirty-nine
instructions. Initial setup/call/cleanup/full prefix checkpoints are exposed at
one shared sufficiently large fuel/budget pair and every larger pair.

All earlier endpoint statements, explicit smaller `NativeTotalFresh` contracts,
independent native success/checked-add hypotheses, generated files, maintained
Rust, source semantics and dependency pins are unchanged. The finite finish
program remains definitionally tied to pinned source by `finish_actions`.
These constructors assume neither a successful whole-parent invocation nor a
stronger universal recursive contract, expected post-frame or cache soundness.

## Consumer and validation

The new kernel consumer in `Tests/SourceCacheMissSetup.lean` starts at parsed
entry with twenty old table Box owners and both original queries aliasing a
table-owned word. Proved empty-query fresh contracts discharge all four smaller
requests, each hitting a nonempty cached witness. Payload extraction, both
choices and the actual insertion/retirement region reach output assembly.
The matched score-fifteen witness defeats score-seven alternatives. Its actual
separate owner inventory has six bounded owners. The inserted table has thirty-two
owners, including ownership transferred from the original input table. Both owned
query bounds, the native table/witness snapshots, the actual full prefix and all
five empty/unbound insertion temporaries are checked.

The 4,280-job library build and all five affected Lean suites pass: parsed
parent setup/insertion consumers, all parent choice orders/ties, addressed
control, owner lifecycle and all eight recursive runtime cases. All 2,003 unique
audited endpoints, including ten new public theorems across six modules, retain
only `propext`, `Classical.choice` and `Quot.sound`. Eight elaborated statement
seeds resolve 1,048 unique declarations with no unknown references. Thirteen
ordered Rust tests and nine Python frontend checks freshly pass. All seven build
caches were checked as ext4 bind mounts; Cargo metadata resolves to the mounted
standalone target and both Cargo/Rustup homes are on ext4.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceParentChoices.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-insertion-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_finish_insertion_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_insertion_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_insert_call_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_insert_setup_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_insert_views_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.allowed_table_local_with_origins \
  SubtreeProofs.Rust.SourceEval.Addressed.Inventory.memo_cells_above \
  SubtreeProofs.Rust.SourceEval.Evaluator.FinishInsertionScope
```

Machine-local logs use `/var/tmp/subtree-insertion-{origins,views,call,finish,build,parsed-consumer,branches,control,lifecycle,runtime,axioms,
statements,rust,python}.log` plus source/statement JSON. Shared source scanning
supplies candidates; kernel acceptance and elaborated statements/axiom closure
establish endpoints and assumptions. The earlier full 47-suite/native-WP check at
`d49f638` remains inherited evidence, not a fresh full-suite run.

## Remaining work

Construct actual optional result/table output assembly at indices 39--47,
retaining selected-witness owner provenance through field transfers even though
the output table can contain original owners. Execute all remaining owned-query
and zero-temporary cleanup, checked return and call closure. Preserve the exact
older hole/empty masks needed for the remainder of the parent frame.

Complete both optional joins, overflow/failure exits, remaining parent returns
and general pair/pair induction, including universal `NativeTotalFresh`.
Dynamic regions/destructors, public maximum/cold-table teardown, wrappers/input
policy/resources/G3 and every other planning requirement remain open. No
SRC-01/C3 or production resource closure is claimed. The full goal stays active.
