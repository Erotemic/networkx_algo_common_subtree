# Intermediate framed lookup ownership: 2026-11-16

Baseline: `c3106fc`. This advances W06-C3 from
[operational typing](lookup-type-preservation.md) and
[normal local cleanup](lookup-frame-safety.md) to spatial separation of
simultaneously owned values throughout completed normal execution. It uses
the existing complete `Footprint`/`FieldsFootprint` occurrence lists. No
production/generated semantics, source inputs or dependency pins change.

## Independent spatial invariant

`Rust/LookupSpatialOwnership.lean` defines `Separated memory cells`: the
combined ownership-occurrence list of all the cells exists and has no
duplicates. Nested Boxes contribute their payload occurrences and their own
address; shared references contribute no owned address. This detects duplicate
owners within one aggregate and ownership shared between separate live roots.
`Separated.every_footprint` uses footprint uniqueness to show that choosing
another witness cannot hide a duplicate.

Footprints remain valid under memory extension. Every owned occurrence names
an actual address below the current memory length. Permuting live values
permutes their complete occurrences and preserves separation. Plain values
own nothing; building an aggregate combines its actual fields without losing
occurrences. `Separated.alloc` proves that the actual new Box is separated
from its payload and the entire retained frame, using the new address's
freshness against every pre-existing occurrence.

`Transfers` is explicitly framed: for every other list of live values, input
separation implies output separation with those other values retained. It is
a separation-preservation judgment, not an exact resource-inventory equation.
The existing local no-owner cleanup and final all-allocation ownership results
remain separate, stronger accounting obligations where applicable.

## Locals, temporaries and execution

`Rust/LookupSpatialLocals.lean` enumerates occupied local slots, preserving
list multiplicities. `Bounded` proves all slots outside the enumeration are
empty; `mem_values` and `values_covers` prove that no live local is omitted.
Moving a value permutes it out of the complete local list and clears the slot.
Store/reset/return transfer rules use the prior concrete no-owner cleanup
conditions. These rules do not silently drop an owning overwritten local.

`Rust/LookupSpatialPrimitives.lean` proves framed transfers for the actual
operand, operand-list, rvalue and scrutinee interpreters. Moves invalidate the
source, copies and borrows are non-owning, and aggregate construction combines
the sequentially extracted temporary values. Previously evaluated arguments
are retained in the frame while later arguments are evaluated.

`Rust/LookupSpatialExecution.lean` combines static destination bounds, actual
frame guards and those transfers. `ActionSpatial` records the actual
post-operand temporary bundle. `Trace` records separated and bounded local
states at every statement/control frontier, the post-scrutinee state, actual
action execution, temporary ownership, callee occurrences, early returns and
continuations. `Trace.erases` recovers exactly the unchanged heap execution
and complete cost. `exec_spatial` constructs the trace and separated post-state;
callee contracts are local at this stage.

## Recursive caller frames and nonvacuity

`Rust/LookupSpatialCalls.lean` discharges those contracts by fuel induction.
`RunSpatial` retains the actual run and framed body traces for every compatible
external frame. At a call, all remaining caller locals join the external frame
passed into the callee. Consequently callee allocations and owned results are
separated from every suspended caller, not just its immediate argument values.
Ordinary helper profiles borrow inputs; generic Box transfers its one payload
and allocates its actual fresh cell.

`original_spatial` and `mutant_spatial` cover all functions/fuels of the two
actual normalized programs. They consume the existing kernel-checked frame
certificates and source type/body-prefix witnesses. No recursive spatial safety
or final ownership premise is left open. The well-typed extra-comparison mutant
passes spatial safety while still violating its old resource allowance.

`Rust/LookupSpatialRefinement.lean` exports `lookup_spatial` for every completed
lookup and `lookup_spatial_total` for all represented native inputs at the
established sufficient fuel. The latter constructs an actual successful run
with recursive spatial traces, normal frame safety, final exclusive fresh
ownership, independent first-hit/typed readback, old-memory preservation,
exact allocation/event counts and the instruction envelope. It also retains
every valid external owner frame. Existing totality supplies existence;
spatial certificates are not used to assume execution succeeds.

## Validation

The main 3,800-job build, all thirteen Lean suites, native WP example, seven
Python frontend tests and 304-endpoint axiom audit pass. Fifty-two new audited
closures stay within `propext`, `Classical.choice`, `Quot.sound`. New modules
have no warnings. Main pins, Rust, generated code/JSON and extraction tooling
are unchanged; the prior pinned regeneration remains the provenance baseline.
Shared `leanq` inspected `lookup_spatial_total`'s elaborated statement closure
(202 records), including its actual successful run, spatial/frame certificates,
native readback, event/allocation bounds and arbitrary retained owner frame.

`Tests/LookupSpatial.lean` is registered in Lean CI. It proves that individually
typed duplicate owned aliases fail joint separation, both within a single
aggregate and across separate roots. Positive cases cover distinct owners,
an actual invalidating move retaining another owner, fresh Box allocation
beside an existing caller owner, shared aliases into an owned frame and the
actual lookup's arbitrary-frame theorem. These are explicit model inputs and
instruction fragments, not new compiled Rust mutations.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/LookupSpatial.lean)
(cd proofs && lake env lean Tests/LookupFrame.lean)
(cd proofs && lake env lean Tests/LookupTypePreservation.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
# Optional elaborated statement inspection through the shared tools.
leanq --project proofs statement SubtreeProofs.Rust.LookupSource.Heap.Spatial.lookup_spatial_total \
  --root-module SubtreeProofs.Rust.LookupSpatialRefinement
```

## Remaining source and lifetime obligations

Intermediate separation is now proved for completed normal executions and
their traced active owner roots. Shared pointees are not counted as new owners;
an external owner of borrowed input storage can be retained in the frame.
The theorem does not impose spatial validity on arbitrary unowned/unreachable
heap cells or infer ownership of a borrowed referent from its representation.
Inputs with invalid duplicate ownership cannot satisfy a frame that purports
to own those duplicates. Shared input aliases remain supported.

The memory still has no free or mutable operation. Stack storage allocation/
liveness, borrow regions/lifetimes, official typed LLBC/Rust primitive
correspondence and failed/unwind execution remain open. Next address those
source/lifetime obligations, then insertion, concatenation, memo evaluation/core
and public wrappers. Full Rust/runtime costs, physical residency/peak space,
allocator time and CPU-time bounds are not established by spatial separation.
W06-C3, SRC-01, MEM-04 and the full planning objective remain open.
