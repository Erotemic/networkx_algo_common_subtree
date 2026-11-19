# Memo local guards and intermediate owner separation: 2026-11-17

Baseline: `38fbb83`. Five `MemoFrame{Profile,Calls,Refinement}` and
`MemoSpatial{Calls,Refinement}` modules extend the
[memo type/scope proof](memo-source-typing.md) with actual recursive local guards
and intermediate spatial traces. Insertion's owned table argument is retained
through initial locals, temporary bundles and suspended callers. Native-input
endpoints compose these traces with source/heap success, independent readback,
returned ownership, table identity and unchanged complete costs. Normal storage
allocation/initialization and dynamic loan/lifetime traces remain next.

## Explicit owner profiles and guarded execution

`LookupFrameChecker.inferActionWith`/`verifyWith` accept a callee owner-profile
check and result-class map. The original lookup entry points specialize the
same analysis at their original rules. `LookupFrameExecution` supplies generic
`CallSafetyFor`, `CallSoundWith`, `ActionSafeWith`, `GuardedWith`, sound action/
checker theorems and exact execution/cost erasure. Existing lookup theorem
entry points remain available as specializations.

`MemoFrameProfile` uses the existing meaning of owner flags: false means an
actually non-owning value; true means possibly owned, so plain values may also
match it. `flagsFit`/`FieldsMatch.widen` permit widening from plain to may-own,
never from may-own to plain. Generic Box accepts a single arbitrary payload.

| Helper | Input owner flags | Result may own |
| --- | --- | --- |
| copy word | false | true |
| copy result | false | true |
| concatenate | false, false | true |
| insert | true, false, false, false | true |
| Box | arbitrary single argument | true |

This is independent of source value typing. In particular insertion's first
input is the table value, not a shared table or a Box of it. Shared query/witness
arguments may point into that table. A true input flag does not prove exclusive
ownership; the spatial input premise separately does that.

`MemoFrameCalls.original_checked` kernel-checks all four actual bodies against
these profiles. Its 15-slot padding is conservative analysis capacity beyond
the argument prefix, not a claim of physical stack size or 15 allocations per
call. `run_sound` discharges recursive callee contracts by fuel induction.
`RunSafe` retains every actual clobber, conditional moved drop, callee occurrence
and return cleanup. No non-return local may still own data at return; moving
slot zero to the caller leaves the departing frame disposable. `RunSafe.erases`
recovers the same completed addressed execution and complete cost.

`MemoFrameRefinement` composes these guards with actual retained source runs.
`concatenate_guarded` and `insert_guarded` apply to every completed call at every
fuel with their concrete pointer/owned-table profiles. Checker acceptance is
not used to invent successful execution; native success remains separately
proved by the preceding source/heap totality theorems.

## Exact initial owners and suspended caller frames

The earlier lookup spatial proof can drop all initial arguments from the owned
ledger because they are shared. That shortcut is invalid for insertion.
`Spatial.values_initial` proves the actual local occurrence list is exactly the
argument list whenever the declared local bound covers the argument prefix.
This preserves insertion's table owner; no plainness premise or set erasure is
used. `boundary_bound` obtains that bound from the actual checked source prefix.

`LookupSpatialExecution` now has generic call/spatial contracts and soundness
parameterized by argument profiles and static callee type maps. Its `Trace`
records bounded local environments, complete separated ownership occurrences,
post-operand temporary bundles, actual control flow, recursive callees and full
costs. It reuses the existing primitive ownership transfers and local guards.
The old lookup interfaces retain their original specialization.

`MemoSpatialCalls.run_spatial` discharges recursive spatial contracts by fuel
induction. For every separated input-owner/frame combination, the actual callee
has a spatial trace and preserves separation at return. The nested call's frame
contains all remaining caller locals and the caller's own suspended frame.
Box transfers its payload's complete footprint into its actual fresh cell;
return cleanup and guard proofs are checked independently of final reachability.

`RunSpatial` retains the actual completed run and recursively scoped traces for
all valid external owner frames. Its frame premise is explicit: separation of
the actual arguments plus the frame. Insertion's table must already have a
valid duplicate-free owned footprint disjoint from that frame. Shared aliases
own no cells and remain allowed. A trace is not asserted for an invalid aliased
input owner merely because its snapshot is representable.

## Composed native source endpoints

`MemoSpatialRefinement.source_run_spatial` composes actual retained source
execution with the same-cost addressed run, guarded/spatial recursive witnesses,
independent represented output, old-memory extension and exact allocation
growth, preserving every valid external owner frame.

`concatenate_spatial_total` and `insert_spatial_total` additionally construct
native-input success at the existing sufficient fuel, retaining typed append/
prepend readback, native translated-Rust agreement and exact structural events.
Concatenation retains fresh returned ownership. Insertion retains the original
table cell under the new tail Box and transfers the complete old-plus-fresh
occurrence ledger established earlier. Intermediate separation is supplied by
the new trace theorem, not inferred from that final ledger. No sound-cache,
unique-key, optimal-witness or consistent-score premise is added.

All local instruction and callee costs remain unchanged. The declared currency
still does not claim allocator time/bytes, interpreter implementation runtime,
physical stack space or a complete source instruction pricing envelope.

## Validation

The main 3,847-job build, all twenty Lean suites, native WP example, nine Python
reifier tests and 516-endpoint axiom audit pass. The 32 newly audited endpoints
use only the accepted `propext`, `Classical.choice`, `Quot.sound` baseline;
new modules have no warnings. Existing lookup frame/storage/type/spatial/loan/
region certificates and suites remain checked against the generic interfaces.
Shared `leanq` inspected the native insertion endpoint and recursive spatial
contract's statement closure (586 records), retaining actual source/heap runs,
guarded/spatial predicates, typed readback, costs and explicit frame premises.
Rust, generated code/JSON, source readers, tooling and pins are unchanged.
The prior `63f929f` full pinned regeneration and thirteen ordered Rust tests
remain the unchanged provenance/behavior baseline.

`Tests/MemoSpatial.lean` is in CI. Cases reject an owned key passed into a shared
profile, clobber/overwrite/drop of the live table, repeated moves and leaving
an owner at return. Widening a plain argument into a may-own role is allowed;
clearing the table slot after its move is allowed. Actual initial owner
enumeration retains the table occurrence. Native insertion with aliased key/
witness borrows into that table constructs guarded/spatial recursive traces
and preserves an independent external owner. A duplicated external owner fails
the spatial premise even though owner-class guards cannot identify addresses.
Instruction fragments are model adversaries, not compiled Rust mutants; actual
helper bodies are separately certified.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/MemoSpatial.lean)
(cd proofs && lake env lean Tests/LookupFrame.lean)
(cd proofs && lake env lean Tests/LookupSpatial.lean)
(cd proofs && lake env lean Tests/LookupStack.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement SubtreeProofs.Rust.MemoSource.Spatial.insert_spatial_total \
  SubtreeProofs.Rust.MemoSource.Spatial.RunSpatial \
  --root-module SubtreeProofs.Rust.MemoSpatialRefinement
```

## Next required work

Retain the completed source/type/scope, addressed/final-owner and intermediate
local guard/spatial proofs. Next normal local allocation/initialization/storage
traces for this function set, then dynamic shared-loan preservation and the
scoped retained-world lifetime interpretation. A `.scope` owner guard does not
distinguish storage allocation/deallocation or prove storage liveness.

Then model the actual memo evaluator's owned-local borrows, checked arithmetic,
losing-candidate destruction and overflow/table returns, compose one public core,
and handle indexed/token/reconstruction wrappers, full work/input/error policy
and G3 adversaries. Physical provenance, general free/mutation/unwind behavior
and compiler/runtime correspondence remain explicit boundaries. W06-C3,
SRC-01, MEM-04, APP-01 and the full planning goal remain open.
