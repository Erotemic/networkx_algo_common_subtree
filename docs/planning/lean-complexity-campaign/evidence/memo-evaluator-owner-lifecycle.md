# Owner ledgers through entry, storage and non-call destruction

Baseline: `40bcb57` on `Droschinsky-algos`. Three proof modules extend the
complete owner ledger through real parameter entry, storage markers and every
successful finite sequence of existing non-call actions. Removed owners are
unique, have exactly the source Box destructor count, and are dead in the final
symbolic world. Production Rust, generated artifacts, existing execution,
independent source/native specifications, costs, hypotheses and pins are unchanged.
W06-C3/SRC-01 and the full planning objective remain open.

## Parameter entry

`SourceOwnerEntry.lean` computes the complete `packetOwners` list from the
existing canonical initialized-cell owner traversal. `packetOwners_footprint`
and `packetOwners_unique` identify it with the actual complete packet footprint
on readable arguments, including shared references with empty owner lists.

`OwnerState.collect_get` connects finite indexed lists with collection over the
actual local range. `initialActivation_ownerState` proves the exact per-local
layout: return local zero owns nothing, argument locals one through the actual
arity own their corresponding packet occurrences, and other locals own nothing.
The proof uses actual appended parameter cells, their stored addresses, existing
initial masks and retained represented graphs. `initialActivation_owners` derives
that the whole entered activation owns exactly the argument packet list.

`OwnerFrame.keep` retains uniqueness/classification/liveness across an existing
`Keeps` transition on those owners. `BoxCoverage.stackCells` proves that fresh
symbolic stack cells add no Box owners. `enter_owner_resources` composes actual
successful entry with readable argument footprints, valid actual callers and
the initial complete owner frame/coverage. The entered activation, actual final
callers and external owners retain both resources. Caller owner identities come
from transported represented caller resources, not presumed absence of aliases.
A maintained generic consumer uses `enter_definition` on the real parsed
declaration's arity and local count. No alternate declaration/count is supplied.

Entry's existing readable-argument checks are not exclusive ownership checks.
The input owner frame remains an explicit premise; duplicate owning arguments
cannot obtain it merely because entry succeeds. Shared argument/caller read
graphs may alias. Parameter storage is stack-class storage, not a fresh Box.

## Actual storage markers

`SourceOwnerStorage.lean` proves that binding an empty local or removing a
represented zero-owner local leaves the exact owner list unchanged. The latter
includes initialized scalar and shared-reference masks; it does not require
that every local be empty. A zero-owner view alone does not authorize teardown.

`OwnerFrame.retire_stack` separates classified Box owners from the actual
retired stack root. `BoxCoverage.retire_same` and `allocate_stack` retain coverage
through stack retirement and fresh stack allocation. These are ownership
transport facts; actual execution still supplies root identity/liveness/bounds,
remaining/caller read guards and storage legality.

`Derived.storageLive_owner_resources` and `storageDead_owner_resources` consume
the real successful existing operations. They derive exact unchanged active
and actual caller owner lists, then preserve complete owner-frame and live-Box
coverage resources. Storage-live obtains the old empty mask from the absent
root and valid frame, retains every existing represented graph and binds a fresh
stack root. Storage-dead uses the operation's actual zero-Box check and represented
local destructor count, removes its root, and retires only that stack address.
An initialized owner or Box shell must move or drop before storage can end.

## Complete non-call sequences and destruction counts

`SourceOwnerActions.lean` exports:

- `Derived.action_owner_resources`: every actual successful storage marker,
  assignment, drop or fake read partitions the complete initial owner ledger
  into removed occurrences and the actual final active/caller/external ledger.
  The removed-list length is that action's original source Box destruction
  count. Assignment composes the previously proved one-pass RHS/store partition;
  drops use the exact actual destroyed list. Selected calls and undefined
  behavior still fail in this older non-call executor.
- `actions_owner_resources`: finite induction through the actual existing
  action-sequence executor, with intermediate validity/callers/world supplied
  by the existing source-step theorem. The complete removed list is
  duplicate-free, its length equals the accumulated `cost.destroyed.boxes`, and
  actual final owners retain uniqueness, Box classification, liveness and full
  coverage of live Boxes. No intermediate or desired final ledger is supplied.
- `action_box_class`, `actions_box_class`: every old Box address retains Box
  classification through these existing operations. Fresh storage allocation
  cannot overwrite an old class because world well-formedness places it below
  the fresh address. Other operations preserve classes directly.
- `actions_owner_destruction`: combine the exact partition, initial uniqueness,
  old-Box class retention and final complete coverage. Every removed address
  was initially a live Box and remains Box-class but is dead in the final world.
  A remaining live removed Box would violate coverage and separation. Thus the
  removed occurrence list cannot charge the same Box twice.

This is exact logical Box retirement and source destructor accounting. It does
not identify compiler-generated destructor instructions, allocator calls,
physical deallocation, wall time or physical peak space. Destructor visits are
already in the existing source work and are not billed again.

## Consumers and adversaries

`Tests/SourceOwnerLifecycle.lean` constructs real argument storage for an owned
Box 0, a shared alias to Box 0 and a scalar. An actual suspended caller owns
Box 1. The complete input list is `[0,1]`; entry preserves it. The active shared
reference initially blocks dropping Box 0, and the initialized owner cannot end
storage.

An eleven-action successful sequence ends the shared-reference storage, drops
Box 0, retires its parameter root, drops/retires the scalar parameter, then
opens/assigns/drops/retires/reopens/assigns local four. Its final root has fresh
address/generation 7. The exact kernel-checked result has eight stored cells,
live addresses `[1,2,7]`, no active Box owners, caller owner `[1]`, seventeen
source steps, four destructor visits and one Box destruction. The general
`actions_owner_destruction` theorem is consumed on this same actual run.

Duplicate owning arguments pass entry's read checks but fail the explicit
OwnerFrame uniqueness requirement. A separate generic parsed-declaration
consumer retains the real declaration's arity/count and complete ownership
boundary without supplying an expected output or post-state.

## Remaining scope

Compose concrete callee output/fresh/retired transfer with the existing actual
argument boundary, parameter entry, result store and checked return/close.
Extend complete owner resources through selected calling control, certified
unused-reference views and full recursive execution. Preserve permitted shared
query/insertion aliases. Then derive adequate call/readback budgets and success
of every physical guard on legal native inputs/warm tables, alongside complete
dynamic parsed region/destructor-instance interpretation.

The native typed evaluator refinement still has a concrete-success premise.
Public maximum/cold-table teardown, wrappers/input policy, global time/space,
G3 and all other LV/Droschinsky/software/release/application targets remain.
The D12 source-operation and compiler/runtime/allocator boundaries are unchanged.
No full W06-C3, SRC-01 or planning-goal completion is claimed.

## Validation and reproduction

The root build passes 3,977 jobs. All three new modules and the new lifecycle
suite compile warning-free. Four affected consumers pass: lifecycle, owner
packets/returns/drops, existing storage lifecycle and frame inventory. The
1,186-endpoint axiom audit includes all twenty new public theorems and retains
only `propext`, `Classical.choice` and `Quot.sound`. Shared `leanq` statement
inspection covers 335 unique declarations from eight selected seeds with no
unknown references; this is the selected statement closure, not the library.
Initial owner-frame/coverage and actual operation-success premises remain visible.

CI now lists 47 maintained Lean suites. The full preceding 46-suite/native-WP/
nine-Python regression passed at baseline `40bcb57`; this increment checks the
new suite and the three affected existing consumers, without claiming a fresh
whole-suite run. No Rust/generated files changed; the thirteen ordered Rust
tests remain evidence from `823df34`. All seven Lean/Rust cache mounts remain
VM-local ext4.

From the repository root:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceOwnerFrames.lean)
(cd proofs && lake env lean Tests/SourceStorageLifecycle.lean)
(cd proofs && lake env lean Tests/SourceFrameInventory.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-owner-lifecycle-statements.json \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.packetOwners_unique \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.initialActivation_owners \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.enter_owner_resources \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.storageLive_owner_resources \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.storageDead_owner_resources \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.action_owner_resources \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.actions_owner_resources \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.actions_owner_destruction
```

Machine-local evidence: `/var/tmp/subtree-owner-lifecycle-{build,regression,
axioms,statements}.log` and `/var/tmp/subtree-owner-lifecycle-statements.json`.
