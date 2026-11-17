# Addressed switches, return packets and actual choice: 2026-11-17

Baseline: `3b2a824`. Four maintained modules execute concrete discriminants,
boolean scrutinees, return extraction and shared source-control routing over the
addressed action layer. Successful runs preserve the original source result and
complete costs, frame/count, active/caller validity and returned packet readback.
A bridge consumes the already checked actual `chooseLonger` body and independent
native tie rule. This advances SRC-01/W06-C3; ordinary/intrinsic calls, universal
physical check success, complete exclusive transfer and function storage/region/
destructor closure remain open. The full planning goal stays active.

## Discriminants survive partial moves

`SourceEvalAddressedScrutinees` adds `Storage.Frame.locate_node`, using the
existing `PartialGraph.locate` to locate a concrete node under the actual initialization
mask. It preserves kind/tag and partial field graphs without materializing
holes. The selected pointer and transitive graph remain covered by the input
frame's live reads.

`Addressed.discriminant` checks the selected source mask is a constructor,
locates the actual cell, checks the pointer root's liveness and reads kind/tag
from that concrete cell. `discriminant_complete` proves every represented source
constructor can be inspected, even after fields move out.
`discriminant_spec` proves agreement with the existing source scrutinee. This
execution does not call the parent source scrutinee to obtain its answer.

`Addressed.scrutinee` handles constructor discriminants and all existing boolean
operand forms using the addressed operand executor and physical move guards.
Its theorem preserves the actual source key/masks and represented frame.
`Derived.scrutinee` computes active loan and caller read guards from the actual
inventories; its specification retains activation identity/bounds/roots and
validity. The world itself does not change during scrutinee execution.

## Return extracts an actual packet

`SourceEvalAddressedReturn` adds `Derived.Flow`, distinguishing continuing states
from returned world/activation/cell-value packets. `Flow.snapshot` maps those
results to the existing independent source outcomes. `Flow.Valid` retains active
frame/world/caller validity and, on a return, the packet's full concrete live
reference graph.

`Derived.returnValue` scans current/caller resources and moves local zero using
the existing addressed operand executor. Active loans and caller reads protect
the move. `returnValue_spec` proves agreement with the original snapshot return
and its one-step source cost, unchanged world/frame/count, packet readback and an
empty source mask at local zero. Source return reads that old mask; physical
extraction additionally transfers the actual cell out of it.

This is return extraction, not function storage closure. The old stack roots
remain in the returned activation; the callee's other locals can still have
resources. The packet may be readable while its referent is still local to that
activation. A caller-facing return contract must close storage, reject escaping
local loans and complete exclusive output ownership/region interpretation.

## Reuse shared control, routing and costs

`SourceEvalAddressedControl` adds `Derived.exec`, using `Control.execWith`,
`selectSource` and `selectIndex`, with concrete instruction/scrutinee/return
adapters. No second source parser or copied routing interpreter is introduced.
`exec_done`, `exec_ret`, `exec_step` and `exec_switch` expose the operational
equations. `selectSource_simulation` lifts successful selected arms through the
result map; the existing `selectSource_spec` carries validity across that arm.

`exec_spec` proves every successful concrete execution agrees with
`SourceEval.exec` for arbitrary source callees, with exactly the same total
`Cost`, unchanged frame/count and `Flow.Valid` at the result. Continuing branches
run the actual rest at their resulting world/activation. Returning branches
skip the rest, retaining only scrutinee/branch charges. Boolean moves update
initialization before routing; partial discriminants retain the current masks.

The underlying action executor still rejects selected ordinary/intrinsic calls
and undefined behavior. Unselected branches are not executed. The theorem keeps
an explicit concrete-success premise; it does not prove all required source
branches/checks succeed. It is not whole recursive evaluator totality.

## Actual owned choice consumes prior proofs

`SourceEvalAddressedChoice` adds `Choice.addressed_refines`, composing `Derived.exec_spec`
with `Choice.actual_body` and `Choice.body_exec`. For an activation at the exact
initial source masks and a successful concrete execution of the pinned
`chooseLonger` body, it produces an actual returned cell, readable independent
native `OrderedSolver.selectResult` encoding, final frame/caller/world validity
and exact body cost `26 + destroyed.visits`, with the existing complete
`destroyed` annotation. The separate function entry charge is not added here.

This reuses the existing all-input snapshot/native/tie proof. It does not assume
the desired native result as a premise or rebuild the earlier owned-choice
model. Universal physical success and full output-exclusive/storage/region
closure remain separate. Inputs need not be represented by fresh output owner
addresses: the tested winning Box identities are transferred unchanged.

## Consumers and validation

`Tests/SourceAddressedControl.lean` moves an optional payload out, then switches
on its retained concrete tag while the aggregate can no longer materialize. The
selected branch returns the moved value; both an undefined other arm and an
undefined continuation are skipped. Exact source agreement, 11 source steps and
final represented validity are derived. Missing/invalid dispatches and a retired
discriminant root are rejected.

A suspended caller points to a scalar in local zero. Return extraction fails
with that loan and succeeds without the caller, despite the scalar having no
Box owners. The complete actual choice body is then exercised in both winner
branches and on a tie. Losing nonempty input retires exactly Box roots zero/one
and has body cost 33, seven destructor visits and two Boxes. Winning nonempty
input retains those same roots in its returned packet and has body cost 29,
three visits and zero destroyed Boxes. Ties retain the first result, using the
existing native rule. A consumer lifts concrete success to the pinned source
body and native result through the new public theorem. The six-local choice
layout agrees with the existing `Certificate.original_counts` certificate.

The full public library build passes (3,937 jobs). All 39 maintained Lean suites,
the native WP pilot and nine Python reifier tests pass; the focused suite has no
diagnostics. `BaselineAudit.lean` audits 962 distinct endpoints, including
all 13 new theorems, using only `propext`, `Classical.choice` and `Quot.sound`.
Shared `leanq` inspection exports 920 unique elaborated statement records from
four seeds, with zero unknown references. The inspected signatures retain input
representation/liveness, actual initial masks where needed and explicit physical
success premises. They do not assume the desired parent source/native answer.

Reproduce from the repository root after preparing VM caches:

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
# Run every maintained Lean suite in .github/workflows/verification.yml.
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-control-statements.json \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.exec_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.returnValue_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.discriminant_complete \
  SubtreeProofs.Rust.SourceEval.Choice.addressed_refines
```

Local evidence is in `/var/tmp/subtree-control-full-build.log`,
`/var/tmp/subtree-addressed-control-tests.log`,
`/var/tmp/subtree-control-regression.log`, `/var/tmp/subtree-control-axioms.log`
and `/var/tmp/subtree-control-statements.json`. These temporary machine-local
files are not committed dependencies. The full pinned regeneration and thirteen
ordered Rust tests at `6137120` remain the unchanged source baseline.

## Remaining requirements

Execute ordinary and intrinsic callees through the complete actual suspended
caller stack, including source argument moves, temporary ownership and guarded
result initialization. Reuse completed helper heap/owner/borrow/type/source/cost
contracts and the Box/checked-add semantics; retain insertion's transferred
table and allowed aliases. A compositional helper boundary may reuse the
completed helper interpreter while explicitly lifting its fresh Box suffix over
the mixed stack/Box world. Do not repeat extraction, native totality, typing,
binder certificates or completed helper proofs.

Prove actual physical routes/checks succeed throughout every evaluator branch,
not only the control examples or a conditional correspondence theorem. Complete
global owner/spatial/temporary transfer, caller-stack completeness and callee
storage closure, then dynamic parsed-region/destructor-instance and returned
loan/ownership interpretation. Returned readability alone is not escape safety.
Keep D12's source-operation boundary explicit; ghost resource scans are not
production Rust work or a physical allocator/runtime proof.

Then public maximum/cold-table teardown, separate wrappers/input policy/global
resources/G3 and the remaining mathematical/software/release/application program
still need completion. Production Rust, generated artifacts, existing source/
type/region/control definitions and pins are unchanged. No full C3 or planning-
goal closure follows from this increment.
