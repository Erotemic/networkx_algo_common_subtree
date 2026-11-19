# Complete subtotal-overflow dispatch and both witness drops

Baseline: `9554d33` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [head/tail failure checkpoint](memo-evaluator-tail-failure.md) constructs
both earlier failure returns. This follow-up constructs the complete subtotal
overflow parent body and checked dispatcher, including drops of both retained
owned witnesses. Root overflow, both contraction failures and universal pair/pair
induction remain open.

## Actual continuation and storage

`SourceFailurePacking.lean` now proves
`failure_pack_complete_with_suffix` for an explicit actual continuation. The
original `failure_pack_complete` statement is preserved as its `.done` instance.
This matters because reference preparation depends on the remaining code;
subtotal failure has a trailing `storageDead 52` after the nine packing actions.
The proof constructs the real prefix with that suffix, rather than assuming
prefixes with different suffixes have identical prepared frames.

`SourceSubtotalOverflowProgram.lean` identifies all ten actual
`subtotalOverflow` actions and the two actual `cleanupTails` actions. From the
real score prefix it derives exactly seventeen live roots, the fifteen tail
roots plus51/52. `subtotal_overflow_pack_complete` transfers the updated table42
into None output0, derives the scalar result52's zero owner count and retires
its real storage. It retains complete original-loan resources, the sixteen
remaining roots, empty42 and the actual count. Empty return storage and root
presence are checked source facts, not a desired post-frame.

`SourceSubtotalOverflowCleanup.lean` constructs the real `storageDead 51` and
owned drop47. The actual retirement-count theorem proves that dropped47 is
ready for its later storage retirement. The head witness37 retains its owner
bound. Reusing `tail_failure_cleanup_complete` then drops37, retires the moved
option/table masks and executes all ten shared input-cleanup actions. Output
and parameter roots0/1/2/3 remain. Both drops use independently retained bounds
above the original heap; old table/query aliases remain legal.

`SourceSubtotalOverflowContinuation.lean` selects the actual overflow arm,
executes packing and all three cleanup joins, and constructs parameter cleanup
and guarded return. It derives zero-owner facts from the actual older holes,
scalar scope and original-loan machine. Both witness bounds survive packing.
The returned None includes exactly the successful tail request's updated table.

## Whole original body and dispatcher

`entry_subtotal_overflow_body_complete` in `SourceSubtotalOverflowBody.lean`
starts with parsed readable pair/pair inputs and complete resources, two explicit
smaller `NativeTotalFresh` contracts, their independent native success equations,
a lookup miss and a native checked-add overflow equation. It reuses the existing
fresh score-entry constructor. Actual typing derives the payload holes and
optional tags; exact prefix execution derives root presence, empty return
storage and count. Common/miss/head/tail/score prefixes, the subtotal switch,
all outer cleanup joins and checked return compose to the whole original body.
No parent execution, parent native equation or successful close is a premise.

`SourceSubtotalOverflowTotality.lean` separately derives the parent native
None equation and proves `subtotal_overflow_total_fresh`. Existing checked
entry/closure constructs readable output, well-formedness, protected caller
reads, complete output/caller/external ownership and live-Box coverage, source/
native agreement, result-field provenance and exact world/packet/full-cost
stability at every larger sufficient fuel/budget pair. The table's owners may
be old; only the witness field has the freshness contract. The two smaller
fresh contracts remain explicit for future induction.

Earlier statements/contracts, independent specifications, source semantics,
generated files, maintained Rust and pins are unchanged. Logical retirement
is distinct from physical allocator cost and peak-space bounds.

## Concrete consumers

`Tests/SourceSubtotalOverflow.lean` discharges both smaller fresh contracts
using the proved empty-input instances. Its arbitrary typed warm cache returns
a nonempty two-Box word at the maximum u32 score for each child. Both parent
query references borrow that word inside the table's owned entry. The kernel
consumer constructs the whole parent dispatcher, readable None/table output,
complete ownership/coverage, result provenance and stable larger bounds, and
checks that the final packet owns four cells, matching the input table's size.
No cache-soundness premise is appropriate for this source overflow case.

`Tests/SourceRecursiveExecution.lean` adds `subtotal-overflow-owned-both`.
Both successful child hits copy their two owned descendants; subtotal failure
must retire all four fresh witness cells while the old table and suspended
caller remain live. The case checks 1,059 source steps and three solver calls,
complete source/addressed value/table/cost equality, caller guard bytes/liveness,
owner uniqueness, live-Box classification, full output/caller coverage and
retirement of every other new storage cell. The full runtime suite has ten cases.

## Validation

The 4,323-job library build and all eight affected Lean suites pass. All 2,089
unique audited endpoints, including eleven new theorems across six proof
modules (five new files), retain only `propext`, `Classical.choice` and
`Quot.sound`. Eight elaborated statement seeds export 1,316 unique records with
zero unknown references. Source scans identify candidates; accepted endpoint
status comes from Lean and the axiom audit. Thirteen ordered Rust tests and nine
Python frontend checks freshly pass. The new kernel consumer is now in ordinary
verification CI.
CI lists fifty-two suites; this checkpoint freshly ran the eight affected suites,
not the full fifty-two. Full 47-suite/native-WP evidence at `d49f638` is inherited.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
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
  aiq-lean source scan --root proofs --json > /var/tmp/subtree-subtotal-source.json
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-subtotal-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.subtotal_overflow_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_subtotal_overflow_body_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.subtotal_overflow_continuation_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.subtotal_overflow_cleanup_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.subtotal_overflow_pack_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_score_root_presence \
  SubtreeProofs.Rust.SourceEval.Evaluator.failure_pack_complete_with_suffix \
  SubtreeProofs.Rust.SourceEval.Evaluator.failure_pack_complete
```

Logs use `/var/tmp/subtree-subtotal-{packing,program,cleanup,continuation,body,
totality,build,consumer,parent,none,output,choices,control,lifecycle,runtime,
axioms,statements,rust,python}.log`, plus source/statement JSON. The body log's
first draft is superseded by the accepted body/totality rebuild in the totality
log. Kernel acceptance and elaborated statements/axioms establish status.
All seven caches are checked ext4 bind mounts; Cargo metadata selects the mounted
standalone target and Cargo/Rustup homes are local ext4.

## Remaining work

Construct root overflow and both contraction-failure returns, then universal
pair/pair `NativeTotalFresh` induction. Dynamic regions/destructors, public
maximum/cold-table teardown, wrappers/input policy/resources/G3 and every other
planning requirement remain open. No full SRC-01/C3 or production resource
closure is claimed; the full goal stays active.
