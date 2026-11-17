# Computed frame resources and assignment: 2026-11-17

Baseline: `43ba691`. Four maintained modules derive complete finite read/owner/
loan inventories from actual cells, roots and source masks, extract remaining
store contexts, scan suspended callers, and execute assignment without supplied
guard lists or a post-RHS frame premise. This advances SRC-01/W06-C3; actual
program control/callees, exclusive transfer and dynamic region/destructor traces
remain required. The full planning goal stays open.

## Three distinct resource lists

`SourceHeapResources.Resources` records full read roots, Box-owner occurrences
and shared-loan roots. `traceResources` traverses the existing partial mask and
concrete cells. A hole contributes nothing. An owned shell contributes its root
to reads/owners; shared values contribute their complete transitive graph to
reads/loans and own nothing. Owned payloads are traversed for shared references,
but owning a Box does not itself create a shared loan. Alias multiplicity is
retained throughout.

`BorrowFootprint`/`BorrowFields` independently specify the initialized shared
references and their full target graphs. `ResourceRep` combines that annotation
with the existing `PartialGraph` and complete `Rep` ownership relation.
`PartialGraph.resources` and its field variant prove tracing succeeds and
produces exactly these semantic resources. `ResourceRep.boxes` recovers the
original source Box count. `BorrowFootprint.subset_reads` places every loan
inside the full read graph; `ResourceRep.transport` preserves all three
interpretations across changes outside that graph.

This computes proof resources, not an additional production Rust algorithm.
Ghost traversal cost is not a hardware/allocator-time claim or a new source
operation charge. Normal source work remains the existing declared currency.

## Slot inspection and remaining contexts

`SourceFrameInventory.inspectSlot` validates the actual stack frame/slot/
generation class, stored cell/mask and liveness of every derived read root.
Missing storage requires an empty source mask. `Frame.inspectSlot` produces a
`LocalResources` witness linking reads to the addressable local frame, owners
to `LocalRep`, and loans to `BorrowFootprint`. Its Box count is exact.

`inspect` folds actual selected slot inventories into `Inventory`.
`Inventory.get` retains each slot's complete read/owner/loan coverage;
`Inventory.boxes` equates the complete owner-list length with the sum of source
Box counts over those slots. `Inventory.frame` derives the actual represented
frame when the selected slots cover every live binding.

`Bounded roots count` requires all roots outside the declared finite range to be
absent. `remainingSlots count destination` selects every declared slot except
the destination. `Inventory.context` proves this selection yields the actual
other-local frame at the cleared destination mask. This supplies the context
which the previous assignment theorem required as an independent premise.
A smaller count cannot silently certify omitted live locals: the bound is an
explicit input invariant, and the test suite rejects a truncated descriptor.

`LocalResources.borrowed`, `Inventory.loan_coverage` and `Scanned.loan_coverage`
expose actual initialized shared-reference footprints covered by the computed
loan list. Local/inventory/caller loan lists are subsets of their read lists.
Transport preserves exact ownership and loan occurrences as well as readback.

## Bounded activations and suspended callers

`SourceActivationInventory.Activation` records a frame ID, declared local count,
root map and current masks. `Activation.Valid` combines a represented input frame
with the finite bound. `Activation.scan_complete`/`scan_spec` derive `Scanned`
resources and a frame covered by their actual read list. `context_complete` and
`context_spec` derive the remaining frame from a successful destination-excluding
scan. No desired output value or parent function postcondition is assumed.

`scanCallers` computes suspended frame resources. `Callers` records each actual
bounded activation's inventory; `scanCallers_complete`/`scanCallers_spec` prove
that interpretation. `Callers.get` preserves each caller's resource coverage.
`Scanned.transport` and `Callers.transport` retain the same caller data, owner
occurrences and loan footprints under a retained-world transition.

Move guards use active shared loans plus all suspended caller reads. Store
contexts use all remaining active reads plus caller reads. This distinction
permits transfer from an active owned local while preserving actual shared
aliases, suspended storage roots and caller-owned data. The eventual control/
call interpreter must thread the complete actual caller stack; an omitted caller
is not declared safe by this local API.

## Assignment derives its inputs

`SourceEval.Addressed.Derived.assign` performs these steps:

1. Scan the active activation and suspended callers.
2. Run the existing addressed RHS once with derived move guards.
3. Rescan the actual intermediate masks, excluding the destination.
4. Compute the RHS reference graph and write the existing empty destination
   using the derived remaining/caller reads and the RHS graph.
5. Return the updated world and activation with unchanged frame/count/roots.

`Derived.store` is the store continuation. `assign_eq_store` relates it to the
previous executor's suffix without rerunning RHS execution in the new function.
`Derived.assign_spec` consumes only valid input activations/callers, a well-formed
world and a successful concrete execution. It derives the actual source action
and original complete `Cost.local Action.weight`, updated activation validity,
caller validity, world well-formedness and preservation of the exact computed
caller inventory. The former supplied guard and post-RHS context premises are
absent. `assign_run` exposes the concrete one-pass composition.

## Consumers and validation

`Tests/SourceFrameInventory.lean` constructs an owned Box, an inline shared alias,
a destination and a caller with a transitive loan into the owned payload. It
checks exact reads/owners/loans, exact owner counts and automatic context
extraction; complete source/derived assignment and caller retention; rejection
of a caller-conflicting payload move; success without that caller, retaining the
Box shell; and discovery of the newly stored reference in the next state's loan
inventory. Wrong frame identity and a retired transitive target are rejected.
A truncated slot count cannot satisfy the activation invariant. Duplicate owners
are still reported as duplicate occurrences and fail `Nodup` separately.

The full public library build passes (3,929 jobs). `Tests/SourceFrameInventory.lean`
passes without diagnostics. All 37 maintained Lean suites, the native WP pilot
and nine Python reifier tests pass. `BaselineAudit.lean` checks 929 distinct endpoints,
including all 41 new theorems, using only `propext`, `Classical.choice` and
`Quot.sound`. Shared `leanq` exports 313 unique elaborated statement records from
four seeds, with zero unknown references. Inspection confirms `assign_spec`
requires input validity and concrete execution, with no assumed desired source
answer, guard list or post-RHS frame; the other seeds expose actual context,
loan coverage and retained caller inventories.

Reproduce from the repository root, with caches prepared as in
`proofs/VERIFICATION.md`:

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceFrameInventory.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
# Run every maintained Lean suite in .github/workflows/verification.yml.
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-derived-inventory-statements.json \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.assign_spec \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.Activation.context_spec \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.Scanned.loan_coverage \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.Callers.transport
```

Local evidence logs are `/var/tmp/subtree-derived-inventory-full-build.log`,
`/var/tmp/subtree-inventory-tests.log`,
`/var/tmp/subtree-derived-inventory-axioms.log`,
`/var/tmp/subtree-derived-inventory-statements.json` and
`/var/tmp/subtree-derived-inventory-regression.log`. These temporary files are
machine-local, not committed dependencies. The full pinned regeneration and
thirteen ordered Rust tests at `6137120` remain the unchanged source baseline.

## Remaining requirements

Construct actual initial activations from the parsed function layouts and
compose storage/drop/call/switch/return/control transitions along the 113-local
evaluator. Thread the actual suspended caller stack, prove route/check success
on all source branches, and instantiate the completed ordinary helper/intrinsic
contracts. Reuse the existing snapshot/native/type/binder/RHS proofs rather than
rebuilding those chains.

Inventories retain multiplicity; they do not by themselves establish global
exclusive ownership, Box-class legality of every owner, or once-only destruction.
Prove complete owner/spatial transfer and temporary ownership through operand
lists and calls. For drop/storage endpoints, protect affected stack roots as well
as Box owners so a scalar/zero-owner value cannot be invalidated through a live
reference. Dynamic parsed-region and destructor-instance interpretation remain
required. Whole-root guards are conservative and do not prove arbitrary
nonoverlapping field mutation.

Then public maximum, separate wrappers/input policy/resources/G3 and the remaining
mathematical/software/release/application program still need completion. No full
C3, compiler, allocator or runtime closure is claimed. Production Rust, generated
source, existing source/type/region/control models, readers and pins are unchanged.
