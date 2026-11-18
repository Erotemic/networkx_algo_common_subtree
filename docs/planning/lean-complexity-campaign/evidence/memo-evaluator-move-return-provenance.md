# Owner provenance through moves, mixed returns and closure

Baseline: `c87634a`, branch `Droschinsky-algos`. This increment continues
SRC-01/W06-C3 by transferring the checked helper-derived owner bounds through
actual operands, expressions, assignments, mixed witness/table returns and
closure. The parent source frontier remains the seventeen-checkpoint right
result scope. General recursive witness provenance and full pair/pair induction
remain open.

## Actual moves and remaining owners

[`SourceMovedOwnerProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceMovedOwnerProvenance.lean)
introduces `SourceEval.Addressed.CellOwnersAbove`: every actual footprint owner
of a selected cell lies at or above a specified address. `of_footprint` uses the
existing uniqueness of represented footprints, not a successful-trace default.

`move_owner_provenance` follows the existing physical owned projection and
owner partition. A moved packet receives only owner occurrences from its actual
source local. The remaining source also retains its owner bound, as do other
locals with established bounds. The result applies to partial moves through
Box shells and aggregate fields, leaving untouched shells and siblings owned
by their original local. It consumes an actual successful move and independent
pre-move frame validity; it does not assume a desired result owner list.
`operand_owner_provenance` lifts this to addressed moves, copies and literals.
Copies/literals add no transferred owners.

## Expressions, guarded stores and retained locals

[`SourceExpressionOwnerProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceExpressionOwnerProvenance.lean)
proves `operands_owner_provenance`, `fields_owner_provenance` and
`expression_owner_provenance`. Operand sequencing retains established bounds
for later operands; aggregates combine their actual represented owner lists.
Address expressions and successful scalar comparisons return no owned Boxes.
`OperandSourcesAbove` and `ExpressionSourcesAbove` specify independent bounds
only for the actual moved source locals. They impose no global alias ban.

`Derived.assign_owner_provenance` derives a selected destination's owner bound
through actual expression execution and guarded storage. The earlier exact
stored-owner theorem identifies the destination's complete actual owner list.

[`SourceRetainedOwnerProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceRetainedOwnerProvenance.lean)
proves bounds survive actual storage opening and unrelated checked drops or
assignments. Real local inventories and retained reads justify transport.
Destination/source distinctions, finite local bounds and the existing source
mutation certificate are explicit where required. No desired post-frame,
callee success or successful surrounding parent invocation is supplied.

## Bound the witness field, retain the old table

[`SourceResultOwnerProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceResultOwnerProvenance.lean)
defines `ResultOwnersAbove` for the actual tuple cell. Its first field is the
returned optional witness; its second is the memo table. Only the witness field
is required to have bounded owners. `LocalResultOwnersAbove` connects that
predicate to an actual stored local tuple. A complete returned tuple may still
own old table Boxes.

`CellOwnersAbove.transport` and `ResultOwnersAbove.transport` use actual graphs
and retained heap reads to preserve owner identities. `ResultOwnersAbove.of_zero`
handles an independently represented first field with zero Box owners.

`Derived.store_packet_kept` proves the actual guarded write preserves its
packet's read graph and stores its exact cell. `assign_result_owner_provenance`
then constructs a tuple from an independently bounded first operand and an
unrestricted second operand. It derives the selected witness-field bound
without incorrectly requiring freshness of the transferred table.

`operand_result_field_owner_provenance` and
`assign_result_field_owner_provenance` extract the bounded optional first field
from an actual mixed tuple and retain its bound in guarded destination storage.
The table's old owner occurrences remain in the partial source tuple. They do
not require a freshness premise for the whole recursive output tuple.

`return_result_owner_provenance` follows the actual guarded return move from
local 0 into its packet. `close_result_owner_provenance` uses checked closure's
exact memory equality to retain the selected owner bound. Bounds do not alone
assert liveness: the existing independent readable/ownership/coverage and close
contracts supply those guarantees.

## Complete empty-query cache-miss endpoint

`SourceEval.Evaluator.empty_miss_total_fresh` in
[`SourceEmptyOwnerProvenance.lean`](../../../../proofs/SubtreeProofs/Rust/SourceEmptyOwnerProvenance.lean)
preserves the complete earlier `empty_miss_total` endpoint and all its premises,
native output/table, read preservation, complete ownership/coverage, exact full
cost and stable runs at larger fuel/readback bounds. It additionally derives
`ResultOwnersAbove world.memory.length` for the actual returned packet after
closure. The returned empty witness has no Box owners; the updated table can
retain old owners and contain nonempty cached witnesses.

This covers either empty query with any typed warm table whose requested key
misses, including legal query/table/caller aliases. It adds no cache-soundness
or physical-success premise. It is the stronger miss branch, not a proof of
owner provenance for arbitrary warm cache hits or all empty-query requests.
The existing universal `NativeTotal` contract is unchanged. No unproved stronger
global contract or pair/pair instance is introduced.

## Kernel consumers

Four additional consumers in `Tests/SourceOwnerProvenance.lean` exercise the
new contracts:

- An actual nonempty cached witness is cloned through the recursive dispatcher.
  Its two fresh owners pass through a partial word-field move, a zero-owner
  embedding-shell drop, embedding reconstruction, optional wrapping and a
  tuple containing the transferred old memo table. Actual return extraction
  and stack closure retain the witness-field bound. Both old table witness
  Boxes and both fresh returned witness Boxes remain live. Provenance is derived
  from the helper ledger and transported by the new theorems.
- Extraction of just the optional witness from that mixed tuple yields two
  bounded destination Box owners while its partial source still owns four old
  table Boxes. The complete mixed tuple is never asserted to be fresh.
- A move through an owned Box's dereference extracts its empty payload while
  retaining that emptied shell in the source. Both remaining source Box owners
  still satisfy the established bound; a moved payload does not erase its shell.
- Complete actual empty-query miss execution starts from a nonempty typed warm
  table with a nonempty cached witness of score seven. Both queries borrow
  table-owned data. The new native key is inserted, and the complete stable
  returned packet carries the witness-field provenance after closure.

The first is a composition of actual helper/primitive/return/close execution,
not a claimed complete parsed parent evaluator run. The fourth consumes the
complete parsed empty-miss theorem. Neither assumes recursive witness freshness
or a desired physical return frame.

## Validation and reproduction

The 4,223-job root build and six affected Lean suites pass, including eight
recursive runtime cases. All 1,902 unique audited endpoints, including
twenty new public theorems across five new proof modules, retain only
`propext`, `Classical.choice` and `Quot.sound`. Eight elaborated statement seeds
resolve 1,168 unique declarations with zero unknown references.
Thirteen ordered Rust tests and nine Python frontend checks pass. The larger
`SourceCacheMissSetup` suite at `c87634a` and full 47-suite/native-WP evidence
at `d49f638` are inherited, not rerun. Maintained Rust, generated extraction,
interpreter/parser semantics, dependency pins and shared tooling are unchanged.

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
(cd proofs && lake env lean BaselineAudit.lean)
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-move-return-statements.json \
  SubtreeProofs.Rust.SourceEval.Evaluator.empty_miss_total_fresh \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.assign_result_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.return_result_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.close_result_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.assign_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.move_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.operands_owner_provenance \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.assign_result_field_owner_provenance
```

All seven build caches are guest-ext4 bind mounts. Cargo metadata selects the
mounted standalone-crate target; Cargo/Rustup homes are ext4. Machine-local logs
are `/var/tmp/subtree-move-return-{build,consumer,expressions,control,helpers,
lifecycle,runtime,axioms,statements,rust,python}.log`; statement data has the same
prefix. Shared source scanning supplies candidate names; kernel audits and
elaborated statement queries establish the endpoints and premises.

## Remaining work

Apply helper-derived provenance to the complete actual warm cache-hit path,
including nonempty cached witnesses, payload extraction/wrapping, mixed result
construction and cleanup. Combine this with the stronger empty-miss endpoint
for a proved stronger empty-query induction base that projects to unchanged
`NativeTotal`. Establish general recursive witness provenance from actual
execution and propagate it through parent candidate assembly, choice and later
selected word/witness cleanup.

Complete both left/right optional failure/success joins, successful right
payload transfer, overflow exits, insertion, remaining parent returns and full
pair/pair induction. Dynamic parsed regions/destructors, public maximum/cold-table
teardown, wrappers/input policy/resources/G3 and the remaining planning targets
stay open. Full SRC-01/C3 and the full user goal remain active; this increment
proves no production resource bound.
