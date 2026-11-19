# Addressed partial moves and logical destruction: 2026-11-17

Baseline: `2696690`. Six maintained modules connect the existing source partial
values to concrete Box identities in the existing addressed heap. Owned field
moves, fresh Box creation, exact partial destruction and caller-owner frames now
compose with the actual expanded-source move/Box/drop primitives. This is a
primitive simulation/ownership foundation. Complete addressed evaluator
execution, stack/local-borrow storage and loan validity, destructor-instance
interpretation, public core/wrappers and global resources remain open. The full
planning goal and W06-C3 remain open.

## Stored data, initialization and ownership

`SourcePartialHeap.Rep` relates an existing `Heap.Cell`, a source `Partial.Slot`
initialization mask and its complete ordered Box-occurrence list. Existing cells
retain stored data after moves. Holes carry no initialized value or ownership;
node tags, siblings and Box shells remain represented. Shared pointers retain
existing heap readback and own no addresses. This extends the existing model
without adding a second cell/type universe or changing source parsing/execution.

`Rep.materialize` recovers the old independent `Heap.Represents` and
`Heap.Footprint` relations whenever the selected value is fully initialized.
`Rep.of_full` and `FieldsRep.of_full` lift those completed existing proofs in the
other direction. `Rep.mono` reuses immutable heap extension. `Rep.bounds` proves
that every selected owner is an existing heap address; `Rep.boxes` equates the
complete occurrence-list length with the existing source destructor Box count.
Lists retain multiplicity; data representation does not establish uniqueness.

## Owned projections and fresh Boxes

`SourcePartialHeapMoves.ownedProjection` follows concrete owned Box pointers and
field paths. It rejects traversal through a shared reference. `FieldsRep.focus`
retains the exact unaffected field frame. `Rep.take` consumes a successful actual
source partial move and returns a concrete moved cell, its old full readback/
footprint, the remaining partial representation and a permutation partition of
the original ownership list. It preserves concrete addresses and stored data.
Moving a Box payload leaves its Box address in the remaining shell.

`Rep.take_typed` additionally consumes the preceding independent partial-local
and projection typing proofs to recover the existing addressed `Heap.Typed`
relation for the moved complete value. The remaining mask keeps its original
source type. Raw projection alone can still find stale stored data; the source
move/materialization premise is required to justify initialized readback.

`Rep.alloc` and `Separated.alloc` reuse the existing `Heap.alloc` operation and
freshness theorem. Payload owners remain unchanged and exactly one new Box
address is added. Existing caller-owned addresses remain disjoint. The full
ownership list need not be a fresh contiguous interval: old memo-table ownership
and shared aliases can be retained. Interval-specific corollaries are provided
only when the existing independent `Heap.Owns` premise supplies that interval.

## Addressed traversal and logical retirement

`SourcePartialHeapDrop.destroy` traverses concrete stored Box pointers under the
initialization mask. It computes owner identities and visit/Box work during
traversal; it does not read a precomputed final footprint as its answer. Shared
referents and moved fields are not traversed. `Rep.destroy` proves exact equality
with the complete occurrence list and existing source `Slot.dropWork`.
`Rep.unique` follows from this deterministic traversal.

`destroy_full_owned`, `destroy_packed_word` and `destroy_packed_result` consume the
existing full representation/ownership and native packing theorems. The earlier
copy/choice destructor formulas remain reusable; no separate word/embedding
count proof or source-helper implementation is introduced.

`Live`, `AliveOn` and `retire` provide explicit logical allocation liveness.
Retirement clears precisely the selected identities while retaining stored data.
`Rep.destroy_retire` requires live, duplicate-free owners and an explicitly
disjoint guarded address list. Protected references may alias each other.
`retired_not_alive` rules out satisfying the live-owner premise for a second
retirement of the same nonempty list. This is logical retirement, not a proof of
physical Rust allocator calls, address reuse, failure or byte-space bounds.

`SourcePartialHeapSpatial.Separated` retains complete duplicate-free ownership
across an arbitrary caller frame. `Separated.of_full` lifts the old independent
spatial relation. `Separated.take` retains moved and remaining values plus the
same caller frame. `Separated.destroy_frame` proves that caller-owned addresses
remain live after selected owners are retired. Shared pointers own no addresses,
so owner separation alone cannot establish shared-loan safety.

## Actual local and source primitive composition

`SourcePartialHeapLocals.LocalRep`/`EnvRep` retain concrete local storage,
initialization masks and per-local complete owner lists. `EnvRep.of_full` reuses
the old full local representation and footprint proofs. `EnvRep.move` changes
only the selected mask/owner ledger, retains concrete local data and partitions
the selected local's owners. Other locals are retained. `destroyLocal` covers
both missing local storage and stored partial values.

`SourceEvalHeapMoveDrop` consumes the actual existing expanded-source primitives:

- `operand_move`: concrete projection/readback/owner transfer and remaining
  represented source state for every successful source move.
- `box_new`: actual source intrinsic execution, unchanged entry cost and the
  existing addressed allocator with the same payload plus one fresh owner.
- `action_drop`, `action_drop_retire`: actual source drop, exact addressed
  selection, cleared local representation and explicit live/guarded resources.
- `action_drop_cost`: existing source work includes visits once and its
  diagnostic Box count equals the selected occurrence-list length.

These are generic primitive contracts, not assumed parent results, global work
bounds or whole-evaluator heap totality. Representation-preserving clear/store
lemmas alone do not justify destroying live owners. Complete call/storage/loan
invariants must establish their resource side conditions along the actual code.

## Consumers and remaining work

`Tests/SourcePartialHeap.lean` moves a nested Word payload with owners `[0,1]`
from a parent retaining Box owners `[2,3]`, while a caller retains owner `4`.
Destruction then selects exactly `[2,3]`, performs four visits and two Box
retirements, and gives source work five. The payload's Box shell is retained
and later selected exactly once. Tests also cover fresh Box/caller separation,
typed readback, native packing reuse, stale-data initialization rejection,
shared-projection rejection and shared referents excluded from destruction.

An aliased owner occurrence list `[0,0]` is representable as stored data but
fails separation. A separate shared pointer to owner `2` owns no address, so
owner separation still holds when retirement would invalidate its referent;
the guarded-address premise fails. These false neighbors retain the missing
loan obligation rather than hiding it in a source/runtime claim.

Reproduce:

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourcePartialHeap.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Validation passes:

- Full maintained library: 3,910 jobs; new modules have no warnings.
- All 33 maintained Lean suites, native WP and nine Python reifier tests.
- 780 distinct audited endpoints, including 46 new endpoints, within the
  unchanged `propext`, `Classical.choice`, `Quot.sound` axiom baseline.
- Shared `leanq` inspection of typed move, caller-frame destruction, guarded
  source retirement and Box creation: 275 unique declarations, no unknowns.
- `git diff --check`; Rust/generated files and pins remain unchanged.

Local logs: `/var/tmp/subtree-partial-heap-full-build.log`,
`/var/tmp/subtree-partial-heap-regression.log`,
`/var/tmp/subtree-partial-heap-axioms.log`, and
`/var/tmp/subtree-partial-heap-statements.{json,log}`. The focused new suite is
also recorded in `/var/tmp/subtree-partial-heap-tests.log`.

Production Rust, generated source, existing memory/control/type/region models
and pins are unchanged. The `6137120` full regeneration/thirteen ordered Rust
tests remain the unchanged source-provenance baseline.

Next construct the full addressed evaluator state and operation/callee
simulation. Retain allocation/storage classes, active local owners and suspended
caller frames. Address creation for newly constructed local values needs a
framed stack interpretation; current raw-pointer data representation and live
owner flags do not supply it. Derive guarded addresses from actual live loans,
then prove storage, owner/spatial, loan/region and destructor-instance contracts
through all actual calls/branches. Reuse the completed source/static/recursive
snapshot/type/region certificates and functional/native totality. Then public
maximum, separate wrappers/input policy/G3, global resources and the remaining
mathematical/software/release/application program are still required.
