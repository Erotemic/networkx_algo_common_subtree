# Helper owner provenance and constructive concatenation cleanup

Baseline: `42e1156`, branch `Droschinsky-algos`. This increment continues
SRC-01/W06-C3 by proving descendant-owner provenance from actual helper
execution. The previous seventeen-checkpoint right-result scope remains the
parent source frontier. General recursive witness provenance, parent joins and
full evaluator totality remain open.

## Exact stored owners

`SourceEval.Addressed.LocalOwnersAbove` in
[`SourceStoredOwnerProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceStoredOwnerProvenance.lean)
asserts that every initialized Box-owner occurrence in a selected actual local
inventory lies at or above a specified heap address. It does not identify
stack-root freshness with descendant-owner freshness. Actual `LocalResources`
representations justify the owner lists; failed tracing is not interpreted as
an empty valid resource. Zero-owner locals satisfy the predicate, and its bound
can be weakened.

`Derived.store_local_owners` proves that a successful guarded destination store
retains exactly the readable packet's footprint owner list. The proof follows
the actual store, transports the packet representation across the selected
stack write and uses canonical local owner lists. It accepts arbitrary readable
packets, including transferred old owners. It supplies no desired post-store
frame or owner list as a premise beyond the independent input footprint.

## Actual helper allocation provenance

[`SourceHelperOwnerProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceHelperOwnerProvenance.lean)
selects the existing `copyWord`, `compare`, `copyResult`, `lookup`, `concatenate`
and `checkedAdd` helpers. `Helpers.typed_plain_packets` derives an empty input
ownership footprint from the actual readable packet types. Shared inputs may
alias owned table data, queries or suspended caller data.

`Helpers.callee_fresh_output` combines that fact with the existing complete
helper allocation ledger. Every output Box owner lies beyond the incoming
heap length. This applies to actual successful helper execution at every fuel
and readback budget; no native-height or cache-soundness premise is added.
Comparison and checked addition have no output Box owners.

`Derived.helper_call_fresh_output` derives actual operand packets, guards,
suspended frames and the destination store from a successful complete call,
then proves `LocalOwnersAbove world.memory.length` for its destination.
`Derived.original_helper_call_fresh_output` transfers the same result through
the unchanged recursive dispatcher at positive fuel. These are provenance
properties of actual successful calls; the existing helper totality proofs
remain responsible for constructing those calls.

Insertion and `boxNew` are excluded from this fresh-output class because they
transfer owned input descendants. A newly allocated outer Box does not make
its old descendants fresh. The insertion consumer below demonstrates an actual
output retaining old input table owners. No permission to drop borrowed old
owners is inferred from a fresh stack destination or outer allocation.

## Constructive concatenation and drop

`SourceEval.Evaluator.original_concatenate_fresh_complete` in
[`SourceOriginalConcatenateFresh.lean`](../../../../proofs/SubtreeProofs/Rust/SourceOriginalConcatenateFresh.lean)
constructs the existing actual native concatenation, its exact independent
append, native structural events and complete call cost. It derives destination
owner provenance relative to the original pre-entry heap from the helper
ledger, then uses it to construct a successful guarded drop of the resulting
owned word. The original-loan machine, complete ownership and Box coverage
persist after the drop. No desired physical concatenation/drop result, output
owner-freshness assumption or post-callee frame is supplied. Legal original
query/table/caller aliases remain supported.

The drop is a derived selected-local permission and execution. It does not
claim that the production evaluator drops its word at the concatenation
checkpoint; actual later source cleanup must retain and consume the provenance
at the corresponding source instruction. The wrapper preserves the earlier
concatenation theorem and its stable exact worlds/costs rather than weakening
its statement.

## Provenance through anchored views

[`SourceAnchoredOwnerProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceAnchoredOwnerProvenance.lean)
connects the property to canonical inventories. `LocalOwnersAbove.of_resource`
uses one represented inventory to establish the property for all equivalent
actual inventories. `LocalOwnersAbove.prepare` preserves it through actual
reference preparation for a closed mask.

`AnchoredLoanMachine.owner_provenance` proves that the same represented anchor
retains its descendant-owner provenance across checked anchored-machine
advances. Original and fresh reference families may change; the anchor owner
identities remain fixed. Existing view/call constructions already retain this
anchor, including its Box descendants. This transports independently established
provenance; it does not manufacture freshness for a recursive witness.

## Consumers and boundary case

The new `Tests/SourceOwnerProvenance.lean` uses a nonempty cached witness of
score seven, with two Box descendants owned by the input table. It checks:

- Actual `copyResult` owns two fresh output Boxes while both old witness Boxes
  remain live through their original table-owned alias.
- The full recursive-dispatcher derived copy call retains that provenance in
  its guarded destination while the caller retains the table and original
  query/witness aliases.
- Actual lookup through repeated references to one table-owned query clones
  the nonempty cached option into two fresh Boxes, preserving the old owners.
- Actual insertion retains an old input table owner below the incoming heap
  length. The helper selection explicitly excludes insertion and `boxNew`.

An additional `Tests/SourceCacheMissSetup.lean` consumer starts from parsed
pair/pair entry and the constructed matched checkpoint. Two nonempty original
left-query child operands execute actual concatenation into 71. The new theorem
derives all four result Box owners' provenance and constructs a guarded drop
retiring all four, with the original-loan machine and external/table-owned
original query aliases retained. Its smaller head/tail totality premises are
discharged with proved empty cases. This is a local concatenation/drop consumer,
not a completed physical parent invocation.

## Validation and reproduction

The 4,218-job root build and seven affected Lean suites pass, including eight
recursive runtime cases. All 1,882 unique audited endpoints, including
eleven new public theorems across four new proof modules, retain only `propext`,
`Classical.choice` and `Quot.sound`. Eight elaborated statement seeds resolve
1,002 unique declarations with zero unknown references. Thirteen ordered
Rust tests and nine Python frontend checks pass. The full 47-suite/native-WP
evidence at `d49f638` is inherited, not rerun. Maintained Rust, generated
extraction, interpreter/parser semantics, dependency pins and shared tooling
are unchanged.

From the repository root unless shown:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build SubtreeProofs)
(cd proofs && lake env lean Tests/SourceOwnerProvenance.lean)
(cd proofs && lake env lean Tests/SourceCacheMissSetup.lean)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-owner-provenance-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.original_concatenate_fresh_complete \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.original_helper_call_fresh_output \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.helper_call_fresh_output \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.callee_fresh_output \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.typed_plain_packets \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.store_local_owners \
  SubtreeProofs.Rust.SourceEval.Addressed.AnchoredLoanMachine.owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.LocalOwnersAbove.prepare
```

All seven build caches are guest-ext4 bind mounts. Cargo metadata selects the
mounted standalone-crate target; Cargo/Rustup homes are ext4. Machine-local logs
are `/var/tmp/subtree-owner-provenance-{build,consumer,setup,expressions,control,
helpers,lifecycle,runtime,axioms,statements,rust,python}.log`; statement data has
the same prefix. Shared source scanning supplies candidate names; kernel audits
and elaborated statement queries establish the reported endpoints and premises.

## Remaining work

Establish and propagate recursive witness owner provenance from actual evaluator
execution, including arbitrary typed warm-cache hits. Preserve the existing
weaker `NativeTotal` contract and independent specifications; any stronger
induction contract must prove its base cases and provide a projection to the
existing totality statement. Helper clone provenance is now available, but the
complete evaluator contract does not yet provide recursive witness freshness.
Propagate provenance through payload/field moves, candidate assembly, choice
and the actual later selected owned-word/witness cleanup.

Complete both left/right optional failure/success joins, successful right
payload transfer, overflow exits, choice, insertion, remaining parent returns
and full pair/pair induction. Dynamic parsed regions/destructors, public
maximum/cold-table teardown, wrappers/input policy/resources/G3 and the remaining
planning targets stay open. Full SRC-01/C3 and the full user goal remain active;
this increment proves no production resource bound.
