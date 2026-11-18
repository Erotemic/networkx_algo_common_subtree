# Complete warm-hit provenance and stronger empty-query induction bases

Baseline: `de35ac6`, branch `Droschinsky-algos`. This increment continues
SRC-01/W06-C3 from the checked move/return provenance endpoint. The complete
actual warm cache-hit evaluator now derives returned witness owner provenance,
including arbitrary nonempty typed cached witnesses. A separate stronger native
induction contract has proved empty-query bases and a constructive caller-store
adapter. General pair/pair induction and the remaining planning targets stay open.

## Primitive prefixes and retirement

[`SourcePrefixOwnerProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourcePrefixOwnerProvenance.lean)
proves `LocalOwnersAbove.prepare_any`: actual continuation preparation either
retains a local mask or ends a shared view with no owners. It therefore preserves
an established owner bound without requiring the selected local to be closed.
`memory_same` compares canonical represented owner lists through exact memory,
root and mask equalities; it does not infer liveness from provenance.

`Derived.storageDead_owner_provenance` and
`Derived.action_keeps_owner_provenance` retain established bounds through actual
storage retirement and unrelated non-call actions. The latter reuses the existing
`LocalPreservation.action` source certificate and existing guarded assignment/drop
preservation. Out-of-count locals are handled from actual frame validity.

`OwnerTransfer` is a finite mathematical certificate over the existing action
list. Its kept steps use the existing source mutation certificate and exclude
calls; its assignments require bounds only on their moved source locals.
`Calling.Prefix.owner_transfer` follows actual continuation-aware instruction
execution and guarded storage. The hit-path certificate explicitly transfers
local 4 to 9, then 11, then 10. It adds no parser, interpreter, success oracle or
unchecked source checker. `OperandSourcesAbove.single_move` supplies the selected
source-root bridge for the real projections.

`Prefix.split`, `Prefix.unique`, `prefix_of_exec` and `Prefix.noncall_valid`
connect these proofs to actual existing executions. `Prefix.retirement_memory`
records exact unchanged memory through real drop/storage-dead steps, retaining
their actual liveness changes and destructor costs.
`LocalResultOwnersAbove.memory_same` and
`Prefix.retirement_result_owner_provenance` retain the selected tuple field's
bound through cleanup without requiring freshness of the old table field.

## Complete parsed hit path

[`SourceCacheHitOwnerProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceCacheHitOwnerProvenance.lean)
proves the following actual execution endpoints:

- `common_prefix_owner_provenance` recovers the real native borrow prefix by
  deterministic prefix uniqueness, derives lookup argument readiness from its
  typed native table/query views, and applies the actual helper allocation
  ledger. The three lookup argument retirements preserve the derived bound.
- `hit_prefix_owner_provenance` follows all twenty real hit instructions.
  Payload movement and optional wrapping retain bounded witness owners. The
  old table moves from 3 through 12 into the result tuple at 0 with no owner
  freshness premise for that table. All nine cleanup instructions retain the
  selected witness-field bound.
- `returnResult_owner_provenance` follows the actual four-instruction return
  cleanup and guarded return extraction.
- `hit_continuation_owner_provenance` composes the selected native lookup
  switch, complete hit branch and return join.
- `entry_hit_body_complete_fresh` constructs real entry and the entire parsed
  body through its returned packet, with the original independent readable
  inputs, complete ownership, legal aliases, native result, caller preservation,
  empty post-state and fresh stack-root guarantees. The witness bound is derived
  from execution, rather than supplied as a desired post-frame.

[`SourceCacheHitTotality.lean`](../../../../proofs/SubtreeProofs/Rust/SourceCacheHitTotality.lean)
now proves `cache_hit_total_fresh`. Its statement preserves all premises and
endpoints of `cache_hit_total`: arbitrary native queries and typed warm table,
actual native hit result/table, lookup events, complete packet readability,
well-formedness, protected reads, complete ownership/coverage, exact full
`hitRunCost` and stable actual `Recursive.original` runs at larger fuel/budget.
It additionally proves `ResultOwnersAbove world.memory.length` after checked
closure. Only the returned optional witness field is bounded; old memo-table
owners remain unrestricted.

The old `cache_hit_total` is a projection with exactly its previous statement.
Neither theorem assumes cache soundness, input/query/table/caller disjointness,
a successful callee invocation or a desired physical parent result. Nonempty
cached witnesses are allowed even for an empty query; this is a native warm-cache
execution contract, not a mathematical cache-soundness theorem.

## Stronger induction contract and actual caller storage

[`SourceEvaluatorNativeFresh.lean`](../../../../proofs/SubtreeProofs/Rust/SourceEvaluatorNativeFresh.lean)
defines `NativeTotalFresh` separately from unchanged `NativeTotal`. It preserves
the original universal inputs, arbitrary warm tables, ownership/coverage,
protected-read preservation and stable full packet/cost contract, and adds the
selected returned witness owner bound. `NativeTotalFresh.total` proves projection
to the old contract.

`native_empty_total_fresh` proves this stronger contract whenever either query
is empty. Its hit branch uses complete `cache_hit_total_fresh`; its miss branch
uses the preceding complete `empty_miss_total_fresh`. Thus arbitrary warm hits
and misses both have proved bases. No universal pair/pair instance or unproved
stronger induction hypothesis is introduced.

[`SourceEvaluatorFreshCallTotality.lean`](../../../../proofs/SubtreeProofs/Rust/SourceEvaluatorFreshCallTotality.lean)
proves `Derived.evaluator_call_total_fresh` from an explicit stronger contract
for the smaller query pair. It constructs real argument extraction, suspended
caller scans, complete child invocation, owner transfer and guarded caller
storage with stable exact full costs and source reflection. The guarded store
retains the actual packet read graph, giving `LocalResultOwnersAbove` at the
caller destination. It preserves all preceding call-totality guarantees.
`Derived.evaluator_call_owner_provenance` recovers that same bound at an already
constructed call checkpoint. It extends the actual call and the independently
constructed stronger call to joint larger fuel/budget, then uses deterministic
execution equality. This supports existing parent checkpoints without changing
their weaker totality statements. The stronger child contract and physical
input/frame permissions remain explicit. These adapters support later recursive
result-field extraction; parent scopes still require propagation and the general
induction proof.

## Adversarial consumers

Two new consumers in `Tests/SourceOwnerProvenance.lean` check:

- Complete actual warm-hit execution with both empty queries borrowing the old
  cached witness's owned leaf Boxes. The typed cache deliberately returns a
  nonempty Pair witness of score seven. After real return and checked closure,
  the optional result has exactly two Box owners, each at or above the incoming
  heap length, and the exact full hit cost/packet is stable at larger bounds.
- The stronger empty-query contract consumed by a complete actual recursive
  call and guarded caller destination write. The caller retains its old query
  and cached-witness views while transferring the old owned table. The stored
  mixed tuple has a proved witness-field bound and stable actual call/cost;
  physical child/parent success is constructed from the native base theorem.
  The older call constructor supplies the checkpoint via the proved contract
  projection; the stable-call bridge recovers its bound without a desired
  post-frame premise.

## Validation and reproduction

The 4,227-job root build and seven affected Lean suites pass, including the
parent cache-miss setup suite and all eight recursive runtime cases. All 1,925
unique audited endpoints, including 23 new public theorems across four new proof
modules and the strengthened cache-hit module, retain only `propext`,
`Classical.choice` and `Quot.sound`. Eight elaborated statement seeds resolve
1,285 unique declarations with zero unknown references. Thirteen ordered Rust
tests and nine Python frontend checks pass.

The old `cache_hit_total` statement is byte-for-byte unchanged; the existing
`NativeTotal` source and the older generic call-totality API are unmodified.
The full 47-suite/native-WP evidence at `d49f638` is inherited, not rerun.
Maintained Rust, generated extraction, interpreter/parser semantics, dependency
pins and shared tooling are unchanged.

From the repository root unless shown:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceOwnerProvenance.lean)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-hit-provenance-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.cache_hit_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_empty_total_fresh \
  SubtreeProofs.Rust.SourceEval.Evaluator.NativeTotalFresh.total \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.evaluator_call_total_fresh \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.evaluator_call_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.common_prefix_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Evaluator.hit_prefix_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.Prefix.owner_transfer
```

All seven build caches are guest-ext4 bind mounts. Cargo metadata selects the
mounted standalone crate target; Cargo/Rustup homes are ext4. Machine-local logs
are `/var/tmp/subtree-hit-provenance-{build,consumer,expressions,control,helpers,
lifecycle,runtime,setup,axioms,statements,rust,python}.log`; statement data has the
same prefix. Shared source scanning supplies declaration candidates; Lean kernel
audits and elaborated statement queries establish theorem status and premises.

## Remaining work

Propagate the stronger child contract and stored witness-field provenance through
parent head/tail/left/right calls and actual payload extraction. The previously
constructed seventeen-checkpoint right-result scope still consumes the older
explicit smaller `NativeTotal` contracts. Establish provenance for selected
recursive candidate words, choice and later owned cleanup while retaining legal
original query/table/caller aliases. Complete both optional failure/success joins,
successful right payload transfer, overflow exits, insertion, remaining parent
returns and full pair/pair induction, including the stronger recursive contract.

Dynamic parsed regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and all remaining planning obligations stay
open. This increment does not complete SRC-01/C3, prove a production resource
bound or finish the full user goal.
