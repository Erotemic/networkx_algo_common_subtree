# Initial activations and executable storage/drop actions: 2026-11-17

Baseline: `d8eb3fb`. Four maintained modules construct actual addressable
parameter frames, derive storage/drop contexts and compose successful non-call
action sequences at the original complete source costs. Initial construction
uses the parsed declaration's local count and signature boundary. This advances
SRC-01/W06-C3; calls, switches/returns, actual branch check success, global
exclusive ownership and dynamic region/destructor interpretation remain open.
The full planning goal stays active.

## Initial arguments follow the actual source layout

`SourceActivationInitial.World.stackCells` appends actual argument cells to the
existing memory. Old data/classes/live flags stay unchanged; new cells receive
fresh symbolic stack addresses/classes and become live. `stackCells_keeps`
retains any old guard list, and `World.WellFormed.stackCells` preserves the full
classified-storage domain invariant. These are stack roots, not Box allocations.

`argumentRoots` binds arguments to locals one through their arity and leaves
return local zero and other locals absent. `initialActivation.state` is exactly
`SourceEval.initialState (packets.map Prod.snd)`. The argument cells and their
value metadata are supplied independently; `packetReads_spec` derives full read
graph coverage from each input's existing `Readable` interpretation, including
transitive reference targets. `initialActivation_valid` proves the resulting
addressable frame and finite root bound.

`enter` checks the local bound and every argument's finite traced read graph and
liveness before constructing that world/activation. `enter_complete` proves
success for independently readable inputs, plus activation/world validity and
retention of all old resources. `enter_definition` derives the bound from an
actual `SourceEval.TypeReader.Definition`'s signature boundary and local count;
callers need supply only the argument arity and read interpretation. The test
consumer applies this theorem to every definition read from the pinned source
using `TypeReader.Certificate.original_declarations`, including the evaluator's
full layout. It does not choose a smaller bound from an example trace.

This is initial representation construction. Input exclusive owner separation,
owner class legality, source typing, fresh invocation IDs and the actual caller
argument transfer still need their existing/separate interpretations. No output
of the parent function or whole-run safety answer is an input.

## Computed storage contexts

`SourceEvalDerivedStorage.scanContext` combines the actual destination-excluding
active inventory with all supplied suspended caller inventories.
`scanContext_spec` produces the cleared-destination frame at exactly their
combined reads and the concrete caller scan/certificate. No hand-selected guard
or desired intermediate frame is assumed.

`storageLive` requires an absent in-bound local, validates active/caller scans,
and allocates a fresh stack root with generation equal to its fresh address.
`storageLive_spec` proves source marker/cost agreement, unchanged frame/count,
updated activation/world validity and exact suspended caller preservation.

`storageDead` allows initialized nonowning masks as observed in actual source
reference temporaries. It checks zero remaining Box work, derives the retained
context, and invokes the existing `endStack` with those guards. Its theorem
proves source marker/cost agreement, removal of that binding, empty source mask,
exact logical root retirement and preservation of callers. Remaining owners or
a Box shell cannot disappear through this operation. An unrelated initialized
shared local can end storage directly; it need not first move or drop.

`Bounded.set_none`/`set_some` retain the declared finite layout through updates.
`Step` packages source agreement for arbitrary source callees, unchanged frame/
count, resulting activation/world validity and the exact computed caller
inventory before/after one non-call step. `Step.callers` derives caller validity.

## Drop protects both ownership and initialization

`SourceEvalDerivedDrop.drop` inspects the actual local and its complete partial
owner inventory, derives the remaining/caller context and checks all of:

- victim owner occurrences are duplicate-free;
- every victim owner has the Box allocation class;
- the affected stack root is absent from retained reads;
- every victim owner is absent from retained reads.

`Rep.subset_reads` and its field/resource/local variants place each complete
owner occurrence inside the actual read graph. This derives owner liveness from
slot inspection. `Frame.inspectSlot_spec` recovers the semantic inventory from a
successful concrete inspection under the represented input frame.

`drop_spec` proves the actual `destroyLocal` traversal returns exactly that owner
list and the source mask's complete `dropWork`. Each owner was live and becomes
logically retired exactly once; its count equals the source Box count. The stack
root stays live/classified at the same address, with an empty initialization
mask. Stored bytes remain. Other locals and all caller graphs/owners/loans are
retained. The original source charge is `Cost.local 1 oldMask.dropWork`; its
visits already contribute to `work.steps` and are not charged twice.

Protecting only Box owners would be insufficient. A scalar has no Box owners but
its stack root can be referenced by another activation. Both drop and storage
retirement reject that conflict. Whole-root protection remains conservative;
arbitrary disjoint field mutations are not established.

## Non-call action sequences compose

`SourceEvalDerivedActions.action` executes storage-live/dead, all existing
assignment RHSs, drop and the source model's inert fake-read marker. Calls and
the undefined-behavior leaf return failure; their execution is not supplied as a
hidden contract. `actionCost` recovers the unchanged source local charge.
`action_spec` derives `Step` for every successful supported action.

`actions` executes a finite sequence, threading the actual world/activation and
summing those costs. `actions_spec` proves equality with the existing source
`exec` on `instructions.foldr Control.Tree.step .done`, exact total cost,
unchanged frame/count and final activation/caller/world validity. Each step
preserves its exact caller inventory; the sequence theorem currently exports
final caller validity, not a separate end-to-end inventory/region theorem.

This is forward correspondence for successful concrete executions. It does not
prove every required source check succeeds or execute switches, early returns,
ordinary/intrinsic calls or the complete recursive evaluator. Existing universal
snapshot/native totality and all RHS/type/binder/helper proofs remain reusable.

## Consumers and validation

`Tests/SourceStorageLifecycle.lean` checks initial source masks, exact argument
root positions, a too-small declared count and retired argument targets. A
12-action chain ends an initialized shared local, destroys its formerly
protected Box, retires parameters, opens/initializes/drops/retires/reopens one
local and derives complete source sequence correspondence. The final generation
is fresh, old roots stay retired, the exact source cost is 18 steps with four
destructor visits and one Box, and the input owner cannot be reused.

A suspended caller points to an initialized scalar with zero Box owners. Drop
and storage-dead both reject invalidating it while unrelated teardown preserves
the exact computed caller resources. Duplicate victim owners and a stack root
misclassified as an owned Box are separately rejected. The tests also reject
reopening a live local and accessing a local outside the finite bound.

The complete public library build passes (3,933 jobs). All 38 maintained Lean
suites, the native WP pilot and nine Python reifier tests pass. The focused suite
passes with no diagnostics. `BaselineAudit.lean` audits 949 distinct endpoints, including
all 20 new theorems, using only `propext`, `Classical.choice` and `Quot.sound`.
Shared `leanq` inspection exports 456 unique elaborated statement records from
four seeds, with zero unknown references. Seed inspection confirms initial
construction uses independent readable arguments/arity and the parsed declaration;
storage/drop consume represented inputs and concrete success; sequence execution
retains an explicit success premise and does not assume the desired source answer.

Reproduce from the repository root after preparing VM caches:

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceStorageLifecycle.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
# Run every maintained Lean suite in .github/workflows/verification.yml.
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-lifecycle-statements.json \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.enter_definition \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.storageDead_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.drop_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.actions_spec
```

Local evidence is in `/var/tmp/subtree-lifecycle-full-build.log`,
`/var/tmp/subtree-storage-lifecycle-tests.log`,
`/var/tmp/subtree-lifecycle-regression.log`,
`/var/tmp/subtree-lifecycle-axioms.log` and
`/var/tmp/subtree-lifecycle-statements.json`. These temporary machine-local files
are not committed dependencies. The full pinned regeneration and thirteen
ordered Rust tests at `6137120` remain the unchanged source baseline.

## Remaining requirements

Use these initial/non-call action endpoints in addressed switch/return and
ordinary/intrinsic call execution. Thread the complete actual caller stack,
argument/temporary ownership and initialization masks. Reuse completed Box/
checked-add and helper source/heap/owner/borrow/type/cost chains, preserving
insertion's transferred table and allowed shared aliases. Prove every physical
route/check succeeds on all actual evaluator branches, not just examples.

Complete global owner/spatial uniqueness, classification and once-only transfer
along the 113-local evaluator and dynamic parsed-region/destructor-instance
interpretation. The local drop checks do not establish all global invariants.
Logical storage retirement is not physical allocator or Rust glue execution.
D12's explicit scoped source-operation boundary remains; a whole LLVM/runtime
proof is not an initial prerequisite.

Then public maximum/cold-table teardown, separate wrappers/input policy/global
resources/G3 and the remaining mathematical/software/release/application program
still need completion. Production Rust, generated artifacts, existing source/
type/region/control models and pins are unchanged. No full C3 or planning-goal
closure follows from this increment.
