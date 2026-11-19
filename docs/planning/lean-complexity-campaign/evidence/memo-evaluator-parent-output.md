# Actual parent output assembly and initial cleanup

Baseline: `f1874ae` on `Droschinsky-algos`. Target: SRC-01 / W06-C3.
The [actual insertion region](memo-evaluator-parent-insertion.md) is followed
by nine output assembly instructions and eight actual drop/dead instructions.
The complete finish prefix reaches `finishCode 56`, given the empty bound
return-storage invariant at the earlier successful-right boundary. The existing
parsed-entry consumer still reaches `finishCode 39`; propagating that storage
invariant through its earlier checked checkpoints remains explicit work.
No whole-parent success, desired output frame or universal stronger recursive
contract is supplied.

## Generic constructors and witness-field provenance

`SourceOriginalAggregateOne.lean` proves `original_aggregate_one_complete`.
It constructs an actual unary aggregate assignment from a moved closed source
into existing empty bound storage. Source/destination guards follow from the
original loan family; complete native resources, count/frame, other roots and
older root bytes are preserved. The source mask becomes empty and the destination
has its independent native constructor value. Owned descendants are unrestricted.

`SourceResultAggregatePrefix.lean` proves
`Calling.Prefix.aggregate_result_owner_provenance`. It derives the existing
`LocalResultOwnersAbove` predicate from an actual two-field tuple assignment and
a bound on only the first moved source. The second source can transfer old owners.
The existing `Derived.assign_result_owner_provenance` proves the packet/store
step; actual reference preparation preserves the first bound.

These use the existing `ResultOwnersAbove` definition: only the optional witness
field is bounded. Neither the memo table nor the complete output tuple is
required to have all-fresh owners. The `NativeTotalFresh` induction contract is
unchanged.

## Actual assembly and retirement

`SourcePairReturnPacking.lean` proves `pair_return_packing_complete`. It
constructs all nine finish instructions at indices 39--47: open optional slot
110, move selected witness 99 through new 111, wrap it into `Some` at 110,
drop/retire emptied 111, move inserted table 104 through new 112, and assemble
the result/table tuple in 0. The actual eight-instruction argument checkpoint,
final tuple assignment and whole nine-instruction prefix remain exposed.

An explicit owner transfer plan carries the bound from 99 through 111 into 110.
The tuple assignment derives `LocalResultOwnersAbove` at 0 independently of the
table owners. Native output, emptied source/temporary masks, complete resources,
both owned-query bounds, count/frame, untouched roots/unshared masks and older
root bytes except written return 0 are checked. Roots 110/112 remain bound and
111 is physically retired.

`SourcePairReturnRetirement.lean` proves `pair_return_retirement_complete`.
The actual eight instructions at indices 48--55 drop and physically retire
112, 110, 104 and 99 after their ownership has moved into 0. Their masks and
roots become empty/unbound. The complete actual retirement plan preserves every
memory byte, the output snapshot, witness-field provenance and both owned query
bounds. Real source destructor/retirement accounting remains in the executor.

`SourcePairFinishPacking.lean` proves `pair_finish_packing_complete`. From the
earlier successful-right scope it constructs payload extraction, both choices,
insertion, output assembly and the initial cleanup through all fifty-six finish
instructions. `FinishPackedScope` records the native optional selected witness
and inserted table at 0, original query tuple, scalar/option holes, both owned
queries, moved masks and physically retired roots. All five assembly/source
locals 99/104/110/111/112 are empty and physically retired. The stored witness
field and owned queries retain their original heap bounds. Actual insertion,
assembly argument, tuple assignment, cleanup and full-prefix checkpoints are
stable at shared sufficiently large fuel/budget bounds.

This last constructor explicitly requires the original return slot 0 to be bound,
empty and backed by its actual empty tuple cell at the input successful-right
boundary. This is a pre-write storage invariant, not an expected result. Earlier
head/tail scopes record it, but the current parsed right-entry endpoint does not
export its later preservation. No claim of parsed-entry execution through 56 is
made here. All earlier endpoint statements, smaller contracts, independent
success/addition hypotheses, source semantics, generated files, maintained Rust
and dependency pins remain unchanged.

## Complete aliasing consumer

`Tests/SourceParentOutput.lean` builds an independent complete physical fixture.
The original two-cell heap contains the table's entry/tail owners 0/1. Six newly
owned witness descendants occupy addresses 2--7. A retained query tuple at 13
contains two shared pointers into different word fields of old entry 0; its
actual loan inventory is `[0, 0]`. The witness's actual input owner inventory is
`[3, 4, 2, 6, 7, 5]`, entirely beyond the original boundary 2.

Actual setup moves the table/witness into 104/99 and opens empty return 0.
The seventeen real assembly/cleanup instructions then execute without a desired
successful run or post-frame premise. The actual output local inventory contains
eight owners, while only its six-owner witness field is bounded above 2. The
native output and original query tuple survive; all five assembly locals are
empty and physically retired. Complete owner coverage is derived at entry and
preserved throughout. The old table owners are accepted without a fresh-table
premise or a prohibition on the retained aliases.

## Validation and reproduction

The 4,285-job library build and all six affected Lean suites pass: the complete
aliasing output fixture, parsed-parent insertion consumers, all parent choice
orders/ties, addressed control, owner lifecycle and all eight recursive runtime
cases. All 2,008 unique audited endpoints, including five new public theorems
across five modules, retain only `propext`, `Classical.choice` and `Quot.sound`.
Eight elaborated statement seeds resolve 1,231 unique declarations with no
unknown references. Thirteen ordered Rust tests and nine Python frontend checks
freshly pass. All seven caches were checked as ext4 bind mounts; Cargo metadata
selects the mounted standalone target, and Cargo/Rustup homes are on ext4.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceParentOutput.lean)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceParentChoices.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-output-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_finish_packing_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_return_packing_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_return_retirement_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.original_aggregate_one_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.aggregate_result_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.assign_result_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.FinishPackedScope \
  SubtreeProofs.Rust.SourceEval.Evaluator.NativeTotalFresh
```

Machine-local logs use `/var/tmp/subtree-output-{generics,packing,retirement,
finish,build,consumer,parsed,branches,control,lifecycle,runtime,axioms,statements,
rust,python}.log` plus source/statement JSON. Shared source scanning supplies
candidates; kernel acceptance and elaborated statements/axiom closure establish
endpoints and assumptions. The full 47-suite/native-WP evidence at `d49f638`
remains inherited, not a fresh full-suite run.

## Remaining work

Propagate empty return storage from the parsed head/tail boundary through all
intervening checked checkpoints, without adding a successful parent/post-frame
premise. `PairHeadScope` and `PairTailScope` already carry `returnRoot` and
`returnEmpty`. Stage constructors expose untouched-root byte preservation;
thread those facts through augmented entry wrappers while preserving previous
endpoint statements. Actual prefix local-preservation results retain empty mask
0 separately from the physical root bytes. Preserve the older live-root/hole/empty-mask facts required by the
remaining finish frame. Execute cleanup beginning at index 56: remaining moved
witness/table/option storage, the two owned queries, scalar/earlier result holes,
original query tuple and argument roots, then checked return and call closure.

Complete both optional joins, overflow/failure exits, remaining parent returns
and general pair/pair induction, including universal `NativeTotalFresh`.
Dynamic regions/destructors, public maximum/cold-table teardown, wrappers/input
policy/resources/G3 and every other planning requirement remain open. No
SRC-01/C3 or production resource closure is claimed. The full goal stays active.
