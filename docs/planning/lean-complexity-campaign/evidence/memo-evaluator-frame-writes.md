# Guarded in-place writes and storage lifecycle: 2026-11-17

Baseline: `c5b612f`. Four maintained modules now transport finite concrete read
and owner graphs across changes outside their guards, authorize in-place stack
writes and compose actual source storage markers/assignment continuations with
addressable frames. Existing stack identity, allocation class, liveness and
memory length survive a write. This advances SRC-01/W06-C3; full addressed
operation/control/callee traces and the full planning goal remain open.

## Read and owner preservation across mutable worlds

`SourceHeapTransport.Retains` preserves existing cells only at selected read
roots. It does not require global immutable extension. `Retains.read` preserves
an inline pointer read when its root is guarded. `Graph.transport` and
`PartialGraph.transport`, with their field variants, preserve the entire finite
transitive graph, including shared targets and initialized-mask selection.
`PartialGraph.owner_transport` preserves an existing complete `Rep` ownership
ledger under the same read conditions. No fresh/contiguous ownership premise is
introduced, and shared aliases remain permitted.

`SourceHeapWrites.Storage.Preserves` combines guarded reads, retained allocation
classes and liveness. Its reflexive/transitive/restriction laws compose writes
with the earlier append/retire transitions through `Keeps.preserves`.
`Loan.preserve` and `Frame.preserve` retain actual reference graphs/source masks
in these mutable worlds. Their old immutable APIs remain unchanged.

`World.write` updates the existing memory cell with `List.set`; it does not
allocate a replacement root. `World.write_spec` and `WellFormed.write` retain
length, classes and live flags. `World.write_preserves` proves a write outside
a guard retains the whole guarded world. `Loan.write` and `Frame.write` consume
that result. Global `Heap.Extends` can fail for the same legal write, which is
why the new guarded transport is required.

`World.writeStack` checks the actual frame/slot/generation class, root liveness,
existing allocation bound and disjointness from the supplied read guard.
`writeStack_iff` states the exact executable success conditions. Protecting only
an outer reference is insufficient: the graph guard must include every nested
referent root. The primitive itself cannot discover omitted caller resources;
frame/loan traces must supply the complete guard coverage.

## Destination frames and actual source assignment

`SourceFrameUpdates.Frame.bind` requires an absent destination binding and
retains the other actual locals. `Frame.store` consumes a context containing
those other locals, an empty destination mask, a matching live stack root and
a concrete RHS partial graph. The target must be absent from both the retained
context guards and RHS guards. The write succeeds, preserves the root identity,
and produces the initialized destination frame. Source-local set/restore lemmas
retain the exact original root map and expected source mask update.

`Frame.erase` is only a graph-view lemma; it does not authorize discarding owned
resources or invalidating loans. Its unchanged conservative guard list still
contains the erased storage root. Actual mutation/ending-storage contracts
require separate empty/owner and guard conditions.

`SourceEval.AddressedPrimitives.action_assign_store` consumes the actual
successful RHS expression result and its represented intermediate frame. It
proves the actual source action equality, guarded store, resulting frame and
unchanged memory length at the original complete source cost. It is a store
continuation contract, not an assumption that arbitrary RHS addressed execution
is already complete. `action_assign_number` closes the entire scalar-constant
case, including the original 32-bit bound and exact two source steps.

Ownership-ledger transport is available separately; arbitrary incoming RHS
ownership separation/transfer and all intermediate operand/frame updates must
still compose along actual execution. A partial graph alone does not establish
exclusive ownership. Initialized owned destinations must be moved/dropped before
using the current empty-destination store contract.

## Actual storage-live and storage-dead

`action_storageLive` consumes an absent binding, creates a classified live stack
root for an uninitialized mask and preserves the retained frame. Placeholder
stored data is not initialized source readback. The source marker keeps its
original one-step cost and adds no Box event. Generations identify symbolic
storage instances; no physical allocator/address-reuse theorem is inferred.

`World.endStack` checks the matching live stack root and disjoint guard, then
logically retires that root. `Frame.endStorage` retains the remaining frame.
`action_storageDead` handles source-empty locals. The actual evaluator also ends
still-initialized nonowning references: for example `emptyLeft` creates local 23
as a borrow of local 16, reborrows it into local 22, then ends local 23's storage
without moving/dropping its reference. The same normal pattern occurs in
`emptyRight` and at shared input endpoints.

`action_storageDead_nonowning` handles these actual cases with the explicit
zero-Box premise and the same source one-step cost. `storageDead_no_owners`
derives an empty complete owner list from that premise and existing `LocalRep`;
it does not assume that the owner list was empty. Shared referents remain live.
A retained Box shell has one Box even with an empty payload, so it cannot pass
this test. Dropping an owner and ending its stack storage remain separate actions.

## Consumers and validation

`Tests/SourceFrameUpdates.lean` performs an actual scalar assignment into an
existing empty local while a caller retains a shared Box reference. It checks
changed stored data with unchanged root/class/liveness/length, failure of global
immutable extension, initialized borrowing of the new value, caller reborrowing,
and complete old owner-ledger transport. Wrong class/frame, dead storage and
protected-root writes are rejected.

Other consumers end source-empty storage, end a still-initialized shared local
while retaining its target, reject a partial Box shell as nonowning, and start
a new symbolic storage generation without reviving the old pointer. A nested
stack-target case shows an outer-only guard admits a corrupting write while
the full transitive guard rejects it; the bad write fails `Retains`.

Reproduce:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceFrameUpdates.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Validation passes:

- Full maintained library: 3,918 jobs; all four new modules have no warnings.
- All 35 maintained Lean suites, native WP and nine Python reifier tests.
- 867 distinct audited endpoints, including 37 new endpoints, with only the
  unchanged `propext`, `Classical.choice`, `Quot.sound` axiom baseline.
- Shared `leanq` inspection of `PartialGraph.owner_transport`, `Frame.store`,
  `action_assign_store` and `action_storageDead_nonowning`: 245 unique
  declarations, no unknown references; elaborated seed signatures reviewed.
- `git diff --check`; Rust/generated files and existing interpreter/model/parser/
  toolchain definitions are unchanged.

Local logs: `/var/tmp/subtree-frame-updates-full-build.log`,
`/var/tmp/subtree-frame-updates-regression.log`,
`/var/tmp/subtree-frame-updates-axioms.log`, and
`/var/tmp/subtree-frame-updates-statements.{json,log}`. The focused new suite is
also recorded in `/var/tmp/subtree-frame-updates-tests.log`. The unchanged
production-source baseline retains `6137120` regeneration/thirteen ordered Rust
tests; no Rust or generated file changed in this increment.

## Remaining requirements

Construct actual initial frames and the contexts consumed above along the
113-local evaluator and all callees. Connect moves, copies, aggregate/less/address
RHS execution, stores, drops, storage endpoints, switches/returns and recursive
calls to concrete owner/spatial/read/loan traces with complete costs. Preserve
all suspended caller resources, insertion's transferred table and shared aliases.
Guarded transport and storage continuation proofs are not a whole evaluator
simulation or an automatic conflict checker.

Current guards protect entire roots. This suffices for the supported whole-local
write operation; it is not a theorem about arbitrary overlapping field writes.
`Loan` is retained-data/liveness evidence; initialization and legal mask changes
still need actual source trace arguments. Dynamic interpretation of parsed
regions, destructor-instance semantics, public maximum, separate wrappers/input
policy/resources/G3 and the remaining mathematical/software/release/application
program remain required. No full C3, compiler, allocator or runtime closure is
claimed. Production Rust, generated source, old interpreter/model definitions,
parsers and pins are unchanged.
