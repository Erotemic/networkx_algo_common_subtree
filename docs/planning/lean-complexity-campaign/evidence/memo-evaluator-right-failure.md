# Complete right-contraction failure dispatch

Baseline: `c0388b1` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [left-contraction failure checkpoint](memo-evaluator-left-failure.md)
constructs the preceding failure exit. This follow-up constructs right None
through the actual seventeen-instruction failure join, all outer cleanup joins,
guarded return and checked dispatch/closure. Both owned queries, the retained
left witness and the matched candidate are cleaned up. The universal pair/pair
fresh induction remains open.

## Actual failure join and retained root81

`SourceRightFailureProgram.lean` identifies the actual right failure:
nine `failurePackActions 89 97 98` instructions followed by eight cleanup
actions. The right optional switch selects `.done` on None, then executes this
entire failure join. The pack's actual suffix is the eight remaining cleanup
actions, so reference preparation retains the correct continuation.

`right_failure_cleanup_complete` in `SourceRightFailureCleanup.lean`
constructs `storageDead 95`, moved table89/None88 drops and retirement, owned
right-query85 drop/retirement, and owned left-witness81 drop. Both owned drops
use independently retained owner bounds. The twenty-six-root right checkpoint
becomes the twenty-two-root left checkpoint; root81 remains bound. The generic
actual retirement-mask-count theorem proves zero owners in81 after its positive
drop, providing the fact needed by the next outer `storageDead 81`. Output
None/table, complete original-loan resources and count survive.

`right_failure_continuation_complete` in `SourceRightFailureContinuation.lean`
constructs actual table89-to-output packing with the real eight-action suffix,
right cleanup, the actual None88 switch and its failure join. It derives the
older optional hole74, empty table75 and zero81 needed to reuse
`left_failure_cleanup_complete`. That outer join retires81, drops the retained
concatenated left query71 and matched candidate64, and retires their storage.
Actual scope/prefix facts derive both earlier witness holes, empty moved table42
and zero owners in scalar58. `pair_failure_outer_return_complete` supplies the
remaining scalar/tail/head/input joins and guarded parameter return. Six cleanup
joins execute; every final mask is empty. Allowed original table/query/caller
aliases are retained; no desired post-frame or parent run is supplied.

## Whole original body and dispatcher

`entry_right_failure_body_complete` in `SourceRightFailureBody.lean`
starts from parsed readable pair/pair inputs and complete resources. Four
explicit smaller `NativeTotalFresh` contracts cover heads, tails and both
contractions. Independent native equations establish head/tail/subtotal/root/
left success, right None and the initial miss. The existing parsed right-storage
constructor derives the actual right scope, held owner bounds, empty return
storage, count and left-success inspection. Real common/miss/head/tail/score/
root/matched/right prefixes derive exact root presence, older masks and all
four earlier optional tags. The complete sixty-instruction matched prefix and
36-instruction right prefix, all six cleanup joins and outer word/lookup routing
compose with the guarded return to the original body.

`SourceRightFailureTotality.lean` separately derives the native parent None
equation and proves `right_failure_total_fresh`. Checked entry/closure supplies
readable None/actual updated-table output, well-formedness, protected caller
reads, complete output/caller/external ownership and live-Box coverage,
source/native agreement, witness-field provenance and exact world/packet/full-
cost stability at all larger sufficient fuel/budget pairs. Old table owners are
allowed. No parent execution/native equation, desired post-frame or successful
close is assumed. All four smaller fresh contracts remain explicit for general
induction.

All pair/pair success and failure branch constructors are now available from
their explicit smaller contracts. Assembling the universal well-founded fresh
induction, dynamic region/destructor interpretation and the rest of SRC-01/C3
remain required. Earlier statements/contracts, independent specifications,
source semantics, generated artifacts, maintained Rust and pins are unchanged.
Logical retirement is distinct from physical allocator cost and peak space.

## Concrete consumers

`Tests/SourceRightFailure.lean` discharges all four smaller fresh contracts
using proved empty-input and one-edge-pair instances. Three warm keys supply
nonempty head/tail/left witnesses. Parent scores 2^31 and zero fit both additions;
left contraction returns a nonempty witness, while the smaller right request
doubles 2^31 and overflows. Both parent queries borrow inside the old table.
Right failure retires its two-owner query and two-owner held left witness;
outer cleanup retires the six-owner matched candidate. The concatenated left
query is empty in this concrete case. The kernel consumer constructs complete
dispatch, readable None/table output, eighteen output owners with full coverage,
result provenance and stable larger bounds. Eighteen output owners match the
old table's size; count alone is not an owner-address identity proof. No cache-
soundness premise is appropriate for this arbitrary typed warm-cache source case.

`Tests/SourceRecursiveExecution.lean` adds
`right-failure-owned-left-witness-query-candidate` with the same warm keys and
nonempty witnesses. It checks 4,252 source steps and seven solver calls, complete
source/addressed value/table/cost equality, suspended caller guard bytes/
liveness, owner uniqueness/live-Box classification, full output/caller coverage
and retirement of every other new storage cell. The runtime suite has thirteen
cases.

## Validation

The 4,340-job library build and all eleven affected Lean suites pass, including
thirteen runtime cases and every previous whole-parent/output/choice/cleanup
consumer. All 2,116 unique
audited endpoints, including six new theorems in five new proof modules, retain
only `propext`, `Classical.choice` and `Quot.sound`. Eight elaborated statement
seeds export 1,347 unique records with zero unknown references. Source scans
identify candidates; accepted status comes from Lean and the axiom audit.
Thirteen ordered Rust tests and nine Python frontend checks freshly pass.
The new kernel consumer is in ordinary verification CI. CI lists fifty-five
suites; this checkpoint freshly ran the eleven affected suites, not all fifty-five.
Full 47-suite/native-WP evidence at `d49f638` remains inherited.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceRightFailure.lean)
(cd proofs && lake env lean Tests/SourceLeftFailure.lean)
(cd proofs && lake env lean Tests/SourceRootOverflow.lean)
(cd proofs && lake env lean Tests/SourceSubtotalOverflow.lean)
(cd proofs && lake env lean Tests/SourceNoneResultProvenance.lean)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceParentOutput.lean)
(cd proofs && lake env lean Tests/SourceParentChoices.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo metadata --locked --no-deps --format-version 1 \
  --manifest-path rust/crates/verified_ordered_core/Cargo.toml
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  aiq-lean source scan --root proofs --json > /var/tmp/subtree-right-failure-source.json
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-right-failure-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.right_failure_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_right_failure_body_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.right_failure_continuation_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.right_failure_cleanup_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.rightFailure_actions \
  SubtreeProofs.Rust.SourceEval.Evaluator.left_failure_cleanup_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_failure_outer_return_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_right_scope_storage_complete_provenance
```

Logs use `/var/tmp/subtree-right-failure-{cleanup,continuation,body,totality,
build,consumer,parent,left,root,subtotal,none,output,choices,control,lifecycle,
runtime,axioms,statements,rust,python}.log`, plus source/statement JSON. Accepted
program/cleanup and continuation rebuilds are retained in the cleanup/body logs;
earlier failed continuation drafts are superseded by the accepted body build.
All regression commands start after their required compiled artifacts are
available; parent and runtime suites start after the complete library rebuild.
All seven caches are checked ext4 bind mounts; Cargo metadata selects the mounted
standalone target and Cargo/Rustup homes are local ext4.

## Remaining work

Assemble universal pair/pair `NativeTotalFresh` induction from all checked branch
constructors. Dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and every other planning requirement remain
open. No full SRC-01/C3 or production resource closure is claimed; the full goal
stays active.
