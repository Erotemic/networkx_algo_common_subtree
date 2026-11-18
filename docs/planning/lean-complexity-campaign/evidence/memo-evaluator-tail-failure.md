# Fresh head failure and complete tail-failure dispatch

Baseline: `a08a7ab` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [successful-parent checkpoint](memo-evaluator-parent-success.md) constructs
the all-successful pair/pair case. This follow-up gives the existing head-failure
dispatcher witness provenance and constructs the complete tail-failure parent
body, return and checked dispatch/closure. The retained owned head witness is
dropped constructively while the updated table may retain old owners. Subtotal/
root overflow, both contraction-failure returns and universal pair/pair induction
remain open.

## None provenance and head failure

`SourceNoneResultProvenance.lean` proves `none_result_owners_above` from a readable
`encodeOutput none table`. It reuses the generic zero-owner first-field theorem:
the absent witness has no owners, independently of the table's owner ages.
`head_failure_total_fresh` retains every guarantee of the existing complete
head-failure dispatcher and adds this result-field bound. Its smaller premise
remains the original `NativeTotal lh rh`; no stronger child contract or new
physical execution premise is added.

`Tests/SourceNoneResultProvenance.lean` checks an explicit returned None whose
table owns cells0/1. The witness bound holds for every threshold, while a bound
of2 on the whole packet's owners is false. This checks the intended distinction
between witness provenance and unrestricted old table ownership.

## Tail storage and cleanup

`SourceRetirementMaskCounts.lean` proves that actual drop/storage-dead prefixes
determine owned-cell counts by clearing selected locals. Reference preparation
preserves those counts. This derives zero owners for storage retirement after a
nonempty drop; it does not equate zero owners with zero destructor visits.
`rootPresence.absent` reflects a checked absence into the real root map.

`SourceTailFailureProgram.lean` identifies the pinned nine-instruction
`tailsFailure` pack at `(source, optional, table) = (42,49,50)` and all six actual
`cleanupHeads` instructions. `pair_tail_root_presence` derives exactly fifteen
bound locals from real entry and the four common/miss/head/tail prefixes:
`[0,1,2,3,13,27,28,29,30,31,32,37,41,42,47]`. No root addresses or desired later
frame are supplied.

`SourceTailFailureCleanup.lean` constructs both cleanup phases. It retires empty
47, moved table42 and None result41, then drops the retained owned head37 through
its independent owner bound. The actual mask-count theorem supplies the zero
count needed by the following storage-dead37. All ten input cleanup instructions
then retire the older holes, moved table, views and query tuple. Only output and
parameter roots0/1/2/3 remain. Complete native/caller/external ownership, live-Box
coverage and original loan origins survive; old table/query aliases remain legal.

`SourceTailFailureContinuation.lean` constructs the real tail-failure selection,
updated-table output packing, both cleanup joins, parameter cleanup and guarded
return. Every mask/root/zero fact consumed by cleanup is derived from the checked
tail scope and actual packing/prefixes. The held head's owners are retained
through packing and dropped using the fresh-owner permission. The returned value
is None with the tail request's actual table.

## Whole body and dispatcher

`SourceTailFailureBody.lean` proves `entry_tail_failure_body_complete`. Parsed
readable inputs, complete resources, two explicit smaller `NativeTotalFresh`
contracts, independent head success and independent tail failure construct
the whole original body. Actual prefix determinism aligns early miss/word
inspections. Original typing derives head inspection, and the real tail/head/
word/lookup joins compose with the constructed return. The endpoint exports the
actual returned world/packet/full cost, empty masks, root separation/freshness and
preserved original caller reads.

`SourceTailFailureTotality.lean` derives the native parent equation from the two
smaller equations and proves `tail_failure_total_fresh`. Existing checked body
closure supplies readable output, well-formedness, protected guards, complete
output/caller/external ownership/coverage and exact dispatcher stability at
larger sufficient bounds. None provenance follows from the real returned packet.
No parent execution, parent native equation, expected post-frame or successful
close is supplied as a premise. Earlier statements/contracts, independent
specifications, source semantics, generated files, maintained Rust and pins are
unchanged. Logical retirement remains distinct from physical allocator cost or
peak space. Both smaller fresh contracts remain to be discharged by induction.

## Validation

The 4,318-job library build and all seven affected Lean suites pass. All 2,078
unique audited endpoints, including twelve new theorems across seven proof
modules, retain only `propext`, `Classical.choice` and `Quot.sound`. Eight
elaborated statement seeds export 1,321 unique records without unknown references.
Thirteen ordered Rust tests and nine Python frontend checks freshly pass.

The runtime suite now has nine cases. Its new `tails-failure-owned-head` case
uses an arbitrary typed warm cached witness with a two-owner nonempty word and
maximum score. The parent retains that owned head while the tail fails through
checked-add overflow. Actual checked recursive dispatch agrees with the complete
source value/table/cost (1,739 source steps and five solver calls), preserves
caller guards/bytes, and checks owner uniqueness, live-Box classification, full
output/caller coverage and retirement of all other new storage. Old table-owned
witness cells remain live. This concrete execution complements the conditional
tail-failure theorem; it does not discharge universal smaller contracts.
The existing whole successful-parent, choice and six-owner cleanup consumers
also still pass. The new None consumer and the existing parent-output/choice
consumers are now included in the ordinary verification CI command list; all
three added commands passed locally. CI now lists fifty-one Lean suites; this
checkpoint freshly ran the seven affected suites rather than all fifty-one.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceNoneResultProvenance.lean)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceParentOutput.lean)
(cd proofs && lake env lean Tests/SourceParentChoices.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  aiq-lean source scan --root proofs --json > /var/tmp/subtree-tail-failure-source.json
PYTHONPATH="$PWD/submodules/aiq-lean-formalization-tools/src" \
  leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-tail-failure-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.tail_failure_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_tail_failure_body_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.tail_failure_continuation_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.tail_failure_cleanup_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_tail_root_presence \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.retirement_boxes \
  SubtreeProofs.Rust.SourceEval.Evaluator.head_failure_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.none_result_owners_above
```

Evidence logs use `/var/tmp/subtree-tail-failure-{build,parent-consumer,output,
branches,control,lifecycle,axioms,statements,rust,python}.log`,
`/var/tmp/subtree-tail-{none-consumer,runtime}.log`, source/statement JSON and the
accepted none-provenance, mask-count, program, cleanup, continuation, body and
totality module logs. Source scans yield candidates; kernel acceptance and
elaborated statements/axioms establish status. All seven caches are checked
ext4 bind mounts; Cargo selects the mounted standalone target and Cargo/Rustup
homes are local ext4. Full 47-suite/native-WP evidence at `d49f638` is inherited.

## Remaining work

Construct subtotal/root overflow and both contraction-failure returns, then
universal pair/pair `NativeTotalFresh` induction. Dynamic regions/destructors,
public maximum/cold-table teardown, wrappers/input policy/resources/G3 and every
other planning requirement remain open. No full SRC-01/C3 or production resource
closure is claimed; the full goal stays active.
