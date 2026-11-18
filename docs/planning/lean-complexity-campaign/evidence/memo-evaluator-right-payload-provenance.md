# Derived right-child provenance through the successful payload checkpoint

Baseline: `b1606e5`, branch `Droschinsky-algos`. SRC-01/W06-C3 now carries the
stronger right-child witness guarantee through parsed evaluator entry and all
seventeen earlier right-result checkpoints. The first six instructions of the
successful-right continuation are also constructed, transferring the bounded
witness into local 95. The complete parent invocation and general recursive
induction remain open.

## Recover the actual child checkpoint

[`SourceEvaluatorCheckpointProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceEvaluatorCheckpointProvenance.lean)
proves `Derived.evaluator_checkpoint_fresh_spec` and its projection
`evaluator_checkpoint_owner_provenance`. Their inputs are independent initial
validity, complete ownership/coverage, the native argument extraction statement,
an explicit smaller `NativeTotalFresh` contract and the actual constructed child
call. They require neither a desired physical post-frame nor additional forward
move/root-loan permissions.

The proof follows the actual guarded argument scans, derives the suspended
activation and complete owner partition, and instantiates the stronger contract
on the real physical packets. The actual child and its independently constructed
stronger run agree at joint larger fuel/budget. The actual guarded destination
store retains the packet graph. The endpoint derives exact initialized native
output masks, native result/table, validity, caller validity, well-formedness and
`LocalResultOwnersAbove` at the caller destination.

This is a retrospective transfer theorem for already constructed child calls,
not a totality proof from an assumed successful whole parent. The parent-side
constructors below supply those calls from their explicit smaller contracts.
Old memo-table owners remain unrestricted; no cache-soundness or global alias
separation premise is introduced.

## Retire arguments and unpack only the witness field

[`SourceResultPrefixProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceResultPrefixProvenance.lean)
proves `LocalResultOwnersAbove.weaken` and `extends`. The latter uses a fully
initialized represented source, its actual graph and retained reads; it does not
infer a graph or liveness from owner provenance alone.
`Derived.storageLive_result_owner_provenance` carries that selected tuple-field
bound through actual fresh storage opening. `OwnerTransfer.kept` reuses the
existing non-call and source mutation certificates.

`Prefix.open_result_field_owner_provenance`,
`Prefix.unpack_result_owner_provenance` and
`Prefix.retire_unpack_result_owner_provenance` follow actual continuation-aware
argument retirement, fresh destination opening, guarded tuple-field movement,
other-field table transfer and cleanup. Only the optional witness field's owners
need a bound. These generic statements support the corresponding head, tail,
left and right source patterns; this increment integrates the right pattern.

## Parsed entry reaches a bounded right option

[`SourcePairRightFreshScope.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRightFreshScope.lean)
proves `pair_right_scope_complete_fresh`. The independent actual argument
constructor is identified with the existing right-call checkpoint by deterministic
prefix uniqueness. Its native query/table values instantiate the retrospective
child theorem. The complete eleven-instruction post-call prefix derives the
owner bound at optional result local 88 relative to the original parent heap.
The transferred old table at 89 is not asserted to be fresh.

[`SourcePairRightFreshEntry.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairRightFreshEntry.lean)
proves `pair_right_from_concat_complete_fresh` and
`entry_pair_right_scope_complete_fresh`. They retain the complete preceding
native result/table, original and fresh query families, all seventeen stable
parsed-entry checkpoints, both actual contraction calls and exact costs, full
left/right region prefixes, physical retirement, count 113 and future unbound
roots. They additionally derive `LocalOwnersAbove world.memory.length` for 88.

Only the right smaller-request premise is strengthened to `NativeTotalFresh`.
The existing head, tail and left `NativeTotal` premises, independent successful
head/tail/left native results and checked score additions remain explicit.
Both possible right option results are supported. All preceding endpoint
statements and source definitions are preserved.

## The real successful-right payload continuation

[`SourcePairFinishProgram.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairFinishProgram.lean)
names the actual pinned `finishActions` and `finishCode` suffixes.
`finish_actions` proves definitional equality with the real parsed `finish` body;
`finish_payload_actions` identifies its first six instructions with the existing
generic optional-payload pattern. This adds no alternative algorithm, parser
or interpreter and assumes no success for later choice/insertion/cleanup.

[`SourcePairFinishPayload.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePairFinishPayload.lean)
proves `optional_payload_owner_provenance` for that generic actual six-instruction
pattern and `pair_finish_payload_complete` for the real successful-right branch.
The latter constructs payload movement from 88 through scratch 96 into 95,
the moved-out scratch drop, physical scratch retirement and the final fake read.
It retains the derived witness bound at 95, complete machine ownership/coverage,
exact root/frame/count and preserved unrelated heap bytes.

`FinishPayloadScope` records the original queries 1/2 and tuple 13, matched
candidate, held left witness, both owned contraction words, transferred table,
right option hole, actual right witness and retired scratch. Actual continuation
preparation ends unused child-view masks 27--30 here. Those masks are recorded
as empty; their physical stack roots await later cleanup. Preserving the earlier
`PairQueryScope` with all four shared masks would misdescribe the real execution.

The preceding right-result endpoint supplies the native discriminant and source
routing to the successful `finish` branch when its independent native result is
`some`. These contracts construct its payload prefix with the real remaining
`finishCode 6` continuation. They do not execute or assume success of the
remaining choices, insertion, owned drops, final return or whole parent join.

## Adversarial parent consumer

The new consumer in `Tests/SourceCacheMissSetup.lean` constructs a typed warm
table with twenty distinct old Box owners. Original parent queries borrow a
nonempty table-owned word. All four child requests hit nonempty cached Pair
witnesses of score seven; checked score additions give fourteen and fifteen.
No cache-soundness premise is supplied.

It instantiates the strengthened parsed-entry endpoint with proved empty-query
smaller contracts, derives the actual right result, then constructs all six
successful-right payload instructions. Local 95 has a real represented inventory
with exactly two Box owners, both at or above the incoming heap length. Query
and table aliases remain legal; child-view logical endings and physical scratch
retirement are recorded by the checked scope. The complete parent invocation is
not supplied as a premise.

## Validation and reproduction

The 4,233-job root build and seven affected Lean suites pass, including the new
nonempty parent consumer and all eight recursive runtime cases. All 1,941 unique
audited endpoints, including sixteen new public theorems across six new proof
modules, retain only `propext`, `Classical.choice` and `Quot.sound`. Eight
elaborated statement seeds resolve 1,328 unique declarations with zero unknown
references. Thirteen ordered Rust tests and nine Python frontend checks pass.

Preceding endpoint statements, native contracts, maintained Rust, generated
extraction, interpreter/parser semantics, dependency pins and shared tooling are
unchanged. The full 47-suite/native-WP evidence at `d49f638` is inherited, not
rerun.

From the repository root unless shown:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceOwnerProvenance.lean)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-parent-provenance-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_pair_right_scope_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_finish_payload_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_scope_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.evaluator_checkpoint_fresh_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.retire_unpack_result_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.optional_payload_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.pair_right_from_concat_complete_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.finish_actions
```

All seven build caches are guest-ext4 bind mounts. Cargo metadata selects the
mounted standalone crate target; Cargo/Rustup homes are ext4. Machine-local logs
are `/var/tmp/subtree-parent-provenance-{build,setup,consumer,expressions,control,
helpers,lifecycle,runtime,axioms,statements,rust,python}.log`; statement data uses
the same prefix. Shared source scanning supplies candidate names; kernel audits
and elaborated statement queries establish endpoints and assumptions.

## Remaining work

Derive and propagate owner bounds for the head, tail and left recursive results,
matched candidate and both concatenated owned words at the parent checkpoints.
Complete actual first/second `chooseLonger` calls, insertion, output assembly and
later owned cleanup while retaining legal original query/table/caller aliases.
The six successful-right payload instructions are complete; its remaining
continuation and both optional failure/success joins are not.

Prove all overflow/failure paths, remaining parent returns and full pair/pair
induction, including the general `NativeTotalFresh` contract. Dynamic parsed
regions/destructors, public maximum/cold-table teardown, wrappers/input policy,
resources/G3 and every remaining planning requirement stay open. This increment
does not complete SRC-01/C3, prove a production resource bound or finish the full
user goal.
