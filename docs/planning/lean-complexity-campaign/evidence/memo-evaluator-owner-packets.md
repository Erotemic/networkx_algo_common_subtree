# Exact owner transfer through packets, assignment, drops and return cleanup

Baseline: `b1335bc` on `Droschinsky-algos`. Eight maintained proof modules
connect complete actual owner identities to operand/RHS packets, guarded
assignment, exact drops, the actual callee input boundary, return extraction and successful
stack closure. The existing interpreters, production Rust/generated artifacts,
source/native specifications, hypotheses, costs and pins are unchanged.
W06-C3/SRC-01 and the full planning goal remain open.

## Complete occurrence accounting

`SourceOwnerInventory.lean` computes `ownerList` using the existing pure partial
destructor traversal, then `ownerState` and finite `Activation.owners`. The
fallback on failed traversal supplies no validity: `LocalRep.ownerList`,
`EnvRep.ownerState`, `Frame.ownerState` and `Inventory.owners` identify these
lists with represented resources. `Activation.scan_owners` identifies the
canonical list with an actual successful scan. Reusing this ghost traversal
adds no production destructor or source cost.

`OwnerState.collect_partition` preserves every occurrence in the finite local
collection. A successful source move has an in-bounds root, derived from actual
frame boundedness rather than guessed from a scan. `SourceOwnerMoves.lean`
bridges owned projections to the actual physical `locatePath`/`Storage.locate`.
`Activation.move_owners` retains the moved cell's physical identity,
representation and complete footprint, with a permutation partition of the
original activation owners into moved and remaining owners. Moving a Box
payload leaves the containing Box shell owned even though stale pointer bits
remain in memory under a now-empty payload mask.

`SourceOwnerPackets.lean` exports `operand_owners`, `operands_owners` and
`expression_owners` for every successful actual operand list and RHS form.
These derive the exact complete packet footprint and remaining activation
partition. Scalar/shared copies contribute no owners; shared read graphs may
alias. The list equations preserve multiplicity and never deduplicate owners.

`OwnerFrame world owners` records duplicate-free complete owner occurrences,
Box classification and liveness. It does not assert coverage of all live Boxes;
`BoxCoverage` is a separate predicate for that property. Packet/operand/RHS
owner-frame theorems transport an initial ledger with any external owners to
the actual temporary packets plus remaining activation and external owners.
Initial ownership uniqueness is explicit: a readable graph or successful scan
alone does not establish exclusive ownership.

## Guarded assignment and actual suspended callers

`SourceOwnerUpdates.lean` proves exact owner identity preservation under
certified unused shared-reference views, and exact owner-state transport under
retained frame reads. `Activation.withoutLocal` extracts a mathematical
remaining-local context. It does not authorize erasing owners during execution.
A zero-mask destination has the same owner ledger as this context.

`SourceOwnerAssignments.lean` proves `Derived.store_owners`: the actual guarded
write puts the packet owners into the destination while preserving the complete
context owner list and world classes/liveness. The store itself checks that
the old destination is empty. Packet representation is transported across the
write using its actual read guards.

`Derived.assign_owners` decomposes the existing one-pass assignment, derives
the post-RHS frame and destination-excluding context from its real scans, and
composes extraction with storage. No guard list, RHS packet, post-RHS frame or
desired owner partition is supplied. The old and new complete activation lists
are permutations; classes/liveness are unchanged. `assign_owner_frame` preserves
the external ledger and `assign_box_coverage` preserves coverage of all live
Box-class addresses.

`SourceOwnerCalls.lean` identifies represented caller owner lists before/after
retained-world transitions. `assign_caller_owner_frame` therefore preserves
uniqueness/classification/liveness using the actual final caller lists, including
the real suspended stack. Caller validity and world well-formedness remain
explicit where needed; a successful truncated scan is not used to infer them.

`Derived.call_argument_owner_frame` decomposes a successful complete actual
call, retaining the precise argument execution and successful callee invocation
with its actual post-argument activation followed by the original callers.
It proves a complete packet footprint and owner frame over packets, remaining
active/suspended callers and external owners at that input boundary. It makes
no assertion yet about ownership of the callee output, fresh allocation or
retired addresses. The callee output-transfer contract remains required.

## Exact Box retirement

`SourceOwnerRetirement.lean` proves `OwnerFrame.retire` and
`BoxCoverage.retire`: removing the discarded prefix of a separated complete
ledger preserves unique/live Box ownership and coverage of all remaining live
Boxes. These generic lemmas do not by themselves authorize retirement.

`Derived.drop_owner_partition` uses the actual successful existing drop checks,
represented local footprint and bounded root to derive the exact destroyed
address list. The old activation owners partition into those addresses and the
actual remaining activation owners. Its length equals the original source
local's destructor Box count; actual final caller owner identities are unchanged.
`drop_owner_resources` composes this partition with the initial complete owner
frame/coverage and retains both for remaining locals, actual callers and external
owners. The existing drop theorem retains source cost, read protection and
exact logical destruction. No extra production work is billed.

## Return packets and checked closure

`SourceOwnerReturns.lean` proves `Derived.returnValue_owner_frame` from actual
local-zero extraction: packet owners plus remaining active/caller/external
owners are exactly the old ledger up to permutation. `Activation.owners_zero`
derives an empty actual owner list from represented zero-Box local masks.

`Storage.close_owner_transfer` consumes the existing successful close check,
valid activation/callers, readable output, its complete footprint, initial
OwnerFrame and full live-Box coverage. The close checks leave no active owners,
retire only the remaining stack roots and preserve memory, classes and Box
liveness. The returned packet retains its complete footprint; actual final
callers plus output/external owners retain OwnerFrame and full live-Box
coverage. This is conditional transfer through existing successful cleanup.

## Consumers and adversaries

`Tests/SourceOwnerFrames.lean` uses a mixed world with nested Box owners
`[0,1,3]`, caller owner `[7]`, and an active/caller shared reference to Box 3.
Moving the nested payload extracts owner 0 while retaining shell 1 and sibling
3. An operand list extracts owners 0 and 3, copies the shared pointer twice,
and retains shell 1/caller 7. Aggregate packing consumes the RHS theorem.
Actual in-place assignment consumes caller owner-frame and full-coverage
preservation; stale payload pointer bits and caller bytes are checked. Dropping
the moved inner Box then consumes `drop_owner_resources`, retires address 0
exactly once, and retains the outer shell, sibling, shared aliases and caller
owner. Complete post-drop owner identities and liveness are kernel checked.

A successful real `boxNew` call consumes the actual callee-input boundary
endpoint. It does not turn that endpoint into a general callee-output proof.
A separate stored graph with owners `[0,1,0,1]` scans successfully but fails
OwnerFrame uniqueness. A complete return/close client transfers owner 0,
retires its stack root, leaves caller storage live and retains full live-Box
coverage. All these consumers are kernel checked.

## Remaining scope

Compose complete callee output/fresh/retired owner transfer with the actual
argument boundary and result store. Extend complete owner accounting through
entry, storage, selected control and recursive execution, preserving
permitted query/insertion/shared aliases. Then derive adequate source/readback
budgets and success of every move/write/drop/storage/return/cleanup check on
legal native executions. Readability and typing alone do not establish this.
Full dynamic parsed regions/destructor interpretation also remains required.

The stronger typed native evaluator refinement at baseline remains unchanged
and still requires concrete success. Public maximum/cold-table teardown,
wrappers/input policy, global time/space, G3 and other LV/Droschinsky/software/
release/application obligations remain. The D12 source-operation boundary and
compiler/runtime/physical allocator boundaries are unchanged. No planning gate
or full goal is closed by this increment.

## Validation and reproduction

The root build passes 3,974 jobs. The eight new modules and focused consumer
suite compile warning-free; the root build replays pre-existing unrelated
warnings. All 46 maintained Lean suites, native WP and nine Python reifier
tests pass. The focused suite was rerun after adding the exact drop consumer.
The 1,166-endpoint audit includes all 51 new public theorems and
retains only `propext`, `Classical.choice` and `Quot.sound`. Shared `leanq`
statement inspection covers 333 unique declarations from eight selected seeds
with no unknown references. This is the selected statement closure, not the
entire library. Initial owner-frame/coverage and concrete success premises
remain visible in the inspected signatures. Cache setup/status confirms all
seven listed Lean/Rust caches are bind-mounted over VM-local ext4.

Rust/generated artifacts did not change. The thirteen ordered Rust tests
passed at `823df34`; this proof increment does not claim a fresh Rust run.

From the repository root:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceOwnerFrames.lean)
(cd proofs && lake env lean BaselineAudit.lean)
# Run every maintained suite in .github/workflows/verification.yml.
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-owner-statements.json \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.Activation.move_owners \
  SubtreeProofs.Rust.SourceEval.Addressed.operands_owner_frame \
  SubtreeProofs.Rust.SourceEval.Addressed.expression_owner_frame \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.assign_caller_owner_frame \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.drop_owner_resources \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.call_argument_owner_frame \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.returnValue_owner_frame \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.close_owner_transfer
```

Machine-local evidence: `/var/tmp/subtree-owner-{tests,full-build,regression,
axioms,statements}.log` and `/var/tmp/subtree-owner-statements.json`. The
regression log records the complete maintained suite sequence and terminal pass.
