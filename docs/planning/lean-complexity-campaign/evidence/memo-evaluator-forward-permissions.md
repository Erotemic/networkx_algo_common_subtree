# Forward storage, drop and cleanup permissions

Date: 2026-11-18. Baseline: `fe8a64d` on `Droschinsky-algos`. Nine proof
modules add 44 checked public theorems. Actual storage creation, storage
retirement, Box drops and closed-result cleanup now have forward success
contracts: complete ownership, independent loan facts and valid storage construct
the runs. No successful addressed/source parent or supplied final frame is an
input. Selected-path assignment/move/return permissions and complete interpreted
choice/evaluator/maximum success still remain; W06-C3/SRC-01 and the full planning
goal are open.

## Complete reads, canonical scans and fresh roots

`SourceReadPartition.lean` proves `BorrowFootprint.read_partition`,
`BorrowFields.read_partition` and `ResourceRep.read_partition`: the complete read
list is a permutation of owner occurrences plus shared-loan occurrences. This
retains every occurrence, including repeated shared aliases. Local/inventory/
caller `read_cases` add the actual local stack roots, exposing the three reasons
an address occurs in a read inventory.

`SourceResourceCanonical.lean` proves `ResourceRep.trace`,
`FieldsResourceRep.trace`, `LocalResources.inspect`, `Inventory.inspect`,
`Scanned.scan`, `Callers.scan` and `Callers.unique`. Every represented inventory
is the exact result of the existing actual tracer/scan. Complete caller loan
lists as well as owner lists are canonical; this supports transferring current
permissions from a preserved older caller inventory.

`SourcePermissionSeparation.lean` defines `Activation.RootsSeparate` as address
separation between active and actual caller stack bindings. `binding_lt`,
`rootsSeparate_of_fresh` and `initialActivation_rootsSeparate` derive separation
from existing valid callers and fresh argument addresses. `RootsSeparate`'s
`set_fresh` and `erase` preserve it through storage creation and retirement.
Symbolic frame IDs need not be unique; actual address freshness is sufficient.

`Inventory.owner_read_disjoint` and `Callers.owner_read_disjoint` reduce
owner/read conflicts to other owner occurrences and actual shared loans. Box
classification rules out stack-root aliases. `Activation.context_root_not_read`
and `RootsSeparate.caller_root_not_read` likewise reduce destination-root
conflicts to shared loans and separate roots. Remaining locals' stack roots
cannot equal the destination because their checked stack classes have different
local indices.

## Forward operations and exact owner resources

`SourceDropTotality.lean` connects actual remaining inventories to canonical
complete owners with `Inventory.context_owners` and
`Activation.partition_owner_frame`. `Derived.DropLoansAllowed` describes a
semantic current-machine permission: the affected root and discarded owners are
disjoint from remaining/caller shared loans. It says nothing about successful
execution, owner uniqueness, allocation classes or a desired final world.

`Derived.drop_complete` derives all actual scan/class/uniqueness/read guards and
constructs the actual drop. The discarded list is the exact `destroyLocal` owner
list and its length equals the original source Box destruction count.
`drop_total` composes this with the existing source `Step`, protected actual
callers, valid final storage and complete final owner-frame/live-Box coverage.
It retains explicit initial owner resources, separate caller roots and semantic
loan permissions.

`SourceClosedLoans.lean` proves `BorrowFootprint.closed_loans`,
`BorrowFields.closed_loans` and local/inventory/caller `closed_loans`. Independent
partial typing of closed types gives empty loan inventories even after moves,
through holes and partially moved Box shells. `Graph.closed_reads` identifies a
closed typed full value's exact reads with its complete owner list. These laws
do not require owner uniqueness or complete initialization of partial locals.

`SourceStorageTotality.lean` proves `Derived.{storageLive_complete,
storageLive_total,storageDead_complete,storageDead_total}`. Fresh creation needs
only a declared slot bound and an absent binding, in addition to valid frames.
Retirement allows initialized nonowning locals; it requires zero Box destruction
and `RootLoansAllowed`, a permission about represented remaining/caller loans.
Owner classification and root separation discharge the rest of the read checks.
The stronger endpoints preserve actual source steps, caller validity, separate
roots and complete global owner resources.

`SourceCloseTotality.lean` proves `Storage.{close_complete_owned,close_total}`.
Zero remaining source Box masks, readable independently typed closed output,
complete owner resources, separate roots and current caller-loan facts construct
actual checked cleanup. Protected addresses must belong to actual caller reads,
as already checked by guarded recursive entry. Closed output reads are Box
owners and cannot escape through callee stack roots. Every active stack root
retires; output footprints, caller/global owner resources, world validity,
protected bytes and complete live-Box coverage remain.

`SourceLoanPermissions.lean` proves `Callers.preserved_read_bound` and
`Derived.{RootLoansAllowed,DropLoansAllowed}.of_closed_preserved`. Preserved old
caller reads remain below the original memory boundary. Fresh roots are therefore
separate from all those reads, including shared aliases. Closed remaining local
types eliminate active loans. For a Box drop, separation between its actual
owners and old caller loans remains explicit; it is not inferred from owner
uniqueness. These are facts about represented current inputs and earlier preserved
callers, not a desired parent execution.

`SourceChoicePermissions.lean` checks the actual pinned declaration's local type
vector: three embeddings, a boolean and two u32s. `Choice.{actual_local_types,
actual_local_types_closed,typed_inventory_no_loans}` show that independently
typed states at every bounded choice point have no active shared loans. The
113-local evaluator has shared-reference locals, so this closed-local result is
not claimed for the evaluator. Whole choice execution still needs forward
assignment/move/control/return and scope composition.

No blanket disjointness is imposed on shared read graphs. Query/insertion/shared
aliases remain permitted where the actual operation retains their targets.
Logical owner/stack retirement is not physical freeing, allocator time, peak
space or production runtime. No Rust, generated Charon/Aeneas artifact,
interpreter, specification, source hypothesis, cost model or pin changed.

## Maintained consumer and validation

`Tests/SourceOwnerLifecycle.lean` constructs ending the initialized shared input's
storage from closed remaining types and preserved caller reads, then constructs
the formerly blocked owning drop. It checks exact destruction and complete final
owner/coverage resources without a supplied successful action. A second proof
rejects `DropLoansAllowed` while the original live alias still exists, even though
the global owner frame is valid. A universal frame-parameter example confirms
that fresh entry separation does not require distinct symbolic frame IDs.

The 4,005-job root build and affected ownership/lifecycle suite pass. All nine
new modules compile without warnings. The 1,333-endpoint audit includes all 44
new theorems and retains only `propext`, `Classical.choice` and `Quot.sound`.
Ten selected `leanq` statement seeds cover 958 unique declarations with zero
unknown references. This is selected statement coverage, not a whole-library
export. All seven cache mounts remain guest-local ext4.

CI still lists 47 maintained Lean suites. No new whole-suite/native-WP/Python/
Rust or runtime-execution run is claimed. The full 47-suite/native-WP/nine-Python
run remains evidence at `d49f638`; eight runtime cold/warm/overflow/failure cases
remain evidence at `a56e701`, and thirteen ordered Rust tests at `823df34`.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-forward-statements.json \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.ResourceRep.read_partition \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.Callers.unique \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.initialActivation_rootsSeparate \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.drop_total \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.storageLive_total \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.storageDead_total \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.close_total \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.RootLoansAllowed.of_closed_preserved \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.DropLoansAllowed.of_closed_preserved \
  SubtreeProofs.Rust.SourceEval.Choice.typed_inventory_no_loans
```

Machine-local logs: `/var/tmp/subtree-forward-{build,owner-tests,axioms,
statements}.log` and `/var/tmp/subtree-forward-statements.json`.

## Next obligations

Construct forward stores/assignments, all selected move routes, scrutinees and
returned packet extraction, then compose actual whole choice and recursive
source execution. Derive source-specific live-loan permissions from actual
native inputs/copy freshness and certified last-use views, preserving allowed
query/table/insertion aliases. Reuse canonical caller inventories, exact global
owners and fixed helper/recursive budget extension to combine finite bounds.
Interpret dynamic parsed-region binders/destructor instances; finish public
maximum/cold-table teardown, wrappers/input policy, global resources/G3 and all
other planning targets. The explicit semantic loan and root/scope conditions
above are prerequisites to discharge along actual paths, not a C3 closure.
