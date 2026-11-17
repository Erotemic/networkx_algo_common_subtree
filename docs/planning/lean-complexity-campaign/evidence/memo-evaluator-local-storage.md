# Addressable local storage and retained reference graphs: 2026-11-17

Baseline: `e2a67e8`. Four maintained modules extend the existing addressed heap
with allocation classes, live storage roots, transitive read graphs and partial
local frames. Actual source address expressions now produce concrete pointers
and liveness-backed readback, including inline fields of partially moved locals.
Fresh Box creation and selected-owner destruction preserve a retained caller
frame under explicit resource conditions. This advances W06-C3/SRC-01; full
addressed evaluator execution and the planning goal remain open.

## Reference graphs and initialized place reads

`SourceHeapReachability.Graph` annotates the existing finite `Heap.Represents`
relation with every pointer root encountered, including transitive shared
referents and owned payloads. `Graph.represents` erases the annotation;
`graph_of_represents` recovers a finite graph from any existing full readback.
The field variants preserve concatenation and aliases. These lists are read
resources, not ownership footprints; a shared pointer contributes its root and
its target graph, while owning no address in the older footprint relation.

`PartialGraph` uses the existing source initialization mask. Holes expose no
value or pointer graph, retained Box shells still contribute their addresses,
and shared referents have complete finite graphs. `Rep.graph` lifts the preceding
partial ownership foundation. `Graph.partial`, `PartialGraph.materialize` and
immutable extension lemmas connect complete and partial values without changing
the existing cell, snapshot or type universes.

`SourceHeapPlaces.locatePath` follows concrete fields, owned dereferences and
shared pointers, retaining an address throughout. It appends inline field paths
and resets the root only on pointer dereference. `PartialGraph.locate` consumes
an actual successful `Slot.get`; `PartialGraph.read` consumes actual successful
initialized source readback and returns the concrete cell/pointer/read graph.
Every selected graph address and final pointer root is among the original graph
and starting storage root. A parent need not fully materialize to borrow one of
its surviving fields. A moved sibling is still rejected by its source mask.

## Allocation classes, storage liveness and loans

`SourceHeapStorage.Storage.World` retains the same immutable `Heap.Memory`, an
allocation-class map and logical liveness. `Class.box` is distinct from
`Class.stack frame slot generation`. `World.allocate` appends exactly one
classified live root; `World.allocate_spec`, `WellFormed.allocate` and
`allocate_keeps` prove freshness, classification, extension and preservation.
`World.retire` retains stored data and classification while clearing selected
live flags; well-formedness is preserved. `BoxOwners.stack_disjoint` and
`BoxOwners.retire_stack` rule out freeing stack storage as a Box owner.

`Keeps` explicitly preserves stored data, prior classes and the selected live
resources. Reflexivity, transitivity and restriction compose these transitions.
`readLive` checks the addressed root's live flag. This alone does not check
transitive targets: `Readable` and `Storage.Loan` additionally require liveness
for the full finite read graph. `Loan.readLive`, `Loan.shared` and `Loan.typed`
compose checked access, existing readback and independent snapshot/heap typing.
`Loan.keep` handles retained worlds. `Loan.retire_iff` characterizes preservation
of the same loan after retirement by disjointness from every graph/root address,
including transitive shared targets. No uniqueness premise is imposed on shared
read resources.

## Addressable local frames and source primitives

`SourceEvalLocalBorrow.Storage.Frame` links each local to an actual stack root,
its frame/slot/generation class and a partial graph for the current source mask.
Its guard list covers all those graphs and local storage roots; the list may
contain repetitions or extra live resources. `Frame.distinct` derives distinct
roots for distinct slots from their actual class assignments. `Frame.empty`
and `Frame.allocate` construct frames; allocation requires an absent destination
binding and records that its preceding source mask was empty. This is not an
unchecked replacement rule for an existing live local.

`Frame.keep`, `Frame.retire`, `Frame.retire_iff` and `Frame.weaken` retain the
same caller state and bindings across permissible world transitions. They apply
to active or suspended frames; a complete call trace still has to construct and
retain the actual frames. `Frame.borrow` reads the current source mask, follows
the concrete stored graph and returns a pointer with a `Loan`. Its entire loan
guard is a subset of the caller frame's guard list. The executable borrow checks
the final root's live flag; transitive liveness is supplied by the frame proof.

Three actual source primitive contracts consume this model:

- `SourceEval.AddressedPrimitives.expression_address`: the actual source address
  expression returns the same reference snapshot and source state, with an
  actual addressed borrow and liveness-backed shared readback.
- `box_new_frame`: the actual Box intrinsic retains its existing entry cost,
  uses exactly the old `Heap.alloc` data operation, adds one live classified Box
  owner and preserves the caller frame.
- `action_drop_frame`: the actual drop and exact existing destructor work
  compose with the preceding concrete owner traversal/retirement. Live,
  duplicate-free owners and disjointness from the retained caller graph are
  explicit. The same caller frame remains valid afterward.

The stack arena is symbolic storage; stack-root creation is not charged as a
source Box allocation. Global storage/space and physical allocation pricing are
still separate obligations. Generation identifiers do not establish address
reuse or in-place reassignment semantics.

## Consumers, validation and remaining scope

`Tests/SourceLocalBorrow.lean` constructs a Box root, a partially moved local and
a caller containing a nested shared reference into that local. It checks:

- initialized sibling reads/borrows with an incomplete parent and rejection of
  moved fields despite retained raw bytes;
- identical concrete roots for owned/shared reborrows, including a two-reference
  caller chain, and independently typed addressed readback;
- classified fresh stack binding, empty-destination evidence and distinct Box/
  stack lifetimes;
- stack retirement rejects checked access while raw data remains readable;
- a live outer stack root cannot justify a loan into a retired transitive Box;
- actual Box/drop contracts retain the caller's nested references through fresh
  allocation and retirement, and the caller can reborrow afterward.

Reproduce:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceLocalBorrow.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Validation passes:

- Full library: 3,914 jobs; the four new modules have no warnings.
- All 34 maintained Lean suites, native WP and nine Python reifier tests.
- 830 distinct audited endpoints, including 50 new endpoints, with only the
  unchanged `propext`, `Classical.choice`, `Quot.sound` axiom baseline.
- Shared `leanq` statement inspection of `Frame.borrow`, `Loan.retire_iff`,
  `box_new_frame` and `action_drop_frame`: 278 unique declarations, no unknowns.
- `git diff --check`; Rust/generated files and existing model/parser/pins unchanged.

Local logs: `/var/tmp/subtree-local-borrow-full-build.log`,
`/var/tmp/subtree-local-borrow-regression.log`,
`/var/tmp/subtree-local-borrow-axioms.log`, and
`/var/tmp/subtree-local-borrow-statements.{json,log}`. The focused new suite is
also recorded in `/var/tmp/subtree-local-borrow-tests.log`. Production-source
regeneration/thirteen ordered Rust tests retain the unchanged `6137120` baseline;
no Rust or generated file changed in this increment.

This is a live retained-data model. `Loan` alone does not prove that a later move,
mutation, mask change or storage action was legal. `Frame.keep` retains the same
source state; initialization at borrow creation comes from its actual partial
mask. Complete source traces must prove conflict-free moves/assignments, update
active frame masks and owner resources, retain suspended callers, and retire
storage roots at the right endpoints. Those obligations cannot be inferred from
immutable raw readback or a live outer pointer. Parsed region bindings are
already checked, but their dynamic interpretation for these new local loans and
destructor instances remains required.

Next implement the full addressed operation/control/callee simulation using
these frames and the preceding move/Box/drop foundation. Connect initialization,
owner/spatial separation, active/suspended storage and loan conflicts along the
113-local evaluator's actual branches and calls; compose dynamic parsed-region
and destructor interpretation. Reuse the completed source/static/recursive
snapshot type certificates and universal native/full-cost evaluator proof.
Then public maximum, separate wrappers/input policy/global resources/G3 and the
remaining mathematical/software/release/application program remain required.
No full C3, compiler, allocator or runtime closure is claimed.
