# Concrete helper calls in the mixed world: 2026-11-17

Baseline: `0e9803a`. Nine maintained modules reuse the six existing ordinary
helper executors, implement both intrinsics, recover live output metadata from
actual cells, and compose one-pass caller argument moves/callee execution/result
storage. Native input shapes and call-nesting bounds discharge the local callee
contracts. This advances SRC-01/W06-C3; integrating this call step into addressed
control/recursive entry, serving choice/evaluator/maximum, universal readiness/
physical-check success and complete ownership/storage/region/destructor closure
remain open. The full planning goal stays active.

## Concrete output metadata

`SourceHeapReadback` adds `snapshot`/`snapshotFields` over actual cells, inline
fields and concrete shared/owned pointer targets. Successful readback returns a
snapshot and the exact transitive read list. `snapshot_spec` and its field
variant derive the existing independent `Graph`/`GraphFields` relations.
`Graph.snapshot` and `GraphFields.snapshot` prove completeness at the finite
`valueDepth`/`fieldsDepth` bound. `represents_unique` derives unique snapshot
readback for any represented concrete cell.

The executable cell reader recurses structurally on its explicit budget and
uses a structural field collector; this permits kernel computation of closed
examples. The soundness/completeness theorems remain over the existing semantic
graphs. Dangling/cyclic data cannot acquire a successful finite representation.

This budget bounds ghost readback nesting. It is distinct from source
call-nesting fuel and is not production Rust work, a new source-operation charge
or a claim that input/output traversal is free in a runtime implementation.
The executable helpers never run the parent source function to obtain output
metadata. Native output values appear in independent correctness proofs, not
as an oracle supplied to the implementation.

## Lift a Box suffix over actual stack storage

`SourceHeapHelperWorld` adds `Storage.World.boxSuffix`, lifting a helper's actual output memory
over the mixed input world. Old classes and live flags remain exactly unchanged;
new suffix cells receive live Box classes. `Extends.length_le`,
`World.boxSuffix_keeps` and `World.WellFormed.boxSuffix` retain the old data and
full classified-storage domain. `boxSuffix_old`, `boxSuffix_fresh` and
`BoxOwners.boxSuffix` expose old identities and fresh allocation classes.

`readPacket` reads the actual result cell and checks every derived read root's
liveness. Its soundness/completeness and represented-result theorems produce a
concrete cell/value packet without an assumed output-liveness answer.

`SourceHeapOutputReadback` proves `Graph.footprint` and its field variant, showing that a deep
`Unborrowed` ordinary output has the same full read and ownership graph.
`readable_of_footprint`, `readable_owners`, `readable_fresh` and
`readable_transfer` derive liveness from existing fresh/transferred owner
contracts. Insertion may retain old owners; it is not forced into a wholly fresh
or contiguous output interval. Alias multiplicity remains explicit.

## Reuse the actual helper interpreters

`SourceEvalHeapHelpers` adds `Helpers.lookup` and `Helpers.memo`, passing argument cells to the
existing `LookupSource.Heap.run` and `MemoSource.Heap.run`, with their existing
certified program bodies. `finish` lifts the returned memory, reads the concrete
output packet and preserves the exact old cost through `Legacy.costMap`.

`lookup_spec` and `memo_spec` are local source/heap composition lemmas. Their
source-success premise is discharged from the completed independent helper
contracts in the native totality and dispatcher theorems below; it is not an
assumption about the evaluator's desired result. The prior helper
stack/owner/loan/region certificates remain available over these same concrete
runs and costs. Their broader interpretation in the evaluator's dynamic world
still needs the remaining program-level composition.

`SourceEvalHeapLookup` instantiates the existing contracts for word copy,
comparison, result copy and table lookup. Its `copy_total`, `compare_total`,
`copyResult_total` and `lookup_total` prove actual mixed-world execution and
matching source runs at sufficient call fuel/readback budget, retaining old
resources and fresh output ownership. Ordinary outputs contain no shared loans.

`SourceEvalHeapMemo` adds `Helpers.concatenate_total` and `Helpers.insert_total`, instantiating
concatenation and insertion for independently readable native inputs. Insertion
retains the complete old table owner ledger, appends exactly the actual fresh
suffix, preserves duplicate-freedom when the old ledger has it, and exposes the
fresh tail Box containing the exact transferred input table cell. Query/result
references may point into that same old table. Old owners remain live and
classified as before; fresh ones are live Boxes. Input global owner class/
separation invariants are not inferred merely from representation.

## Intrinsics and local callee readiness

`SourceEvalHeapIntrinsics` proves `Helpers.boxNew_total`, allocating a real live Box containing the
actual input cell, preserving the packet's read graph and source entry cost.
`checkedAdd_total` inspects actual number cells, checks both 32-bit bounds and
returns the concrete encoded success/overflow option at the original entry
cost. Neither intrinsic needs ordinary-output readback fuel.

`Helpers.execute` dispatches these two intrinsics and all six ordinary helper
backends. Choice, evaluator and maximum currently return failure here. The
existing separately checked addressed choice control remains reusable for its
future call wrapper and storage closure.

`SourceEvalHelperCalls.Ready` specifies only native argument cell/metadata shapes
and sufficient call-nesting fuel (plus positive/bounded scalar intrinsic
inputs). It contains no desired output or parent-run answer.
`callee_respects` discharges `Derived.CallsRespect` for the actual dispatcher and
`SourceEval.run Certificate.original.body fuel`, using each earlier native
helper contract. Every successful ready call preserves source output/cost,
complete output readability, world well-formedness and all retained reads.
Sufficient ghost readback budget guarantees ordinary helper success through the
native totality theorems; forward correspondence itself retains concrete success.

## Actual caller argument/store composition

`SourceEvalDerivedCalls.call` performs:

1. Scan the active activation and all supplied suspended callers.
2. Evaluate all actual operands once with active loan plus caller-read guards.
3. Rescan the intermediate masks excluding the destination.
4. Call the concrete callee with those retained/caller reads plus the actual
   existing destination stack root protected.
5. Trace the actual returned packet and initialize the existing empty destination
   using the derived context and returned graph.
6. Return the updated world/activation and original call-site plus callee cost.

`packets_readable` derives every temporary argument's full live graph from
`operands_spec`. `store_spec` isolates the existing guarded store continuation.
`call_spec` composes the local callee contract and independent readiness of the
actual evaluated arguments, deriving the original `SourceEval.action` call,
unchanged frame/count/roots, final activation/world validity and exact computed
suspended caller resources. No desired post-argument context or hand-selected
guard list is an input. The readiness selector concerns input shapes/fuel only.
Complete exclusive temporary/argument transfer remains a separate invariant.

This checked call step is not yet wired into `Derived.exec`: that earlier
control dispatcher still rejects selected calls. Next integrate it and establish
readiness/budgets along every actual branch, rather than treating this local
composition as whole-program C3 closure.

## Consumers and validation

`Tests/SourceHelperCalls.lean` builds a mixed prefix containing a retired stack
cell, other stack cells and a nonempty owned table. All insertion query/result
pointers point into the table's old entry. Direct helper execution preserves the
retired flag and old classes, adds exactly two live Box cells, and returns the
owner occurrence list `[freshEntry, oldEntry, oldTail, freshTail]`. A theorem
consumer derives the complete old-plus-fresh ownership permutation, liveness and
exact transferred table tail.

The caller example opens the real return slot, moves all four actual arguments,
executes insertion and writes the result into that same stack root. The original
source action/cost, final activation validity and well-formedness follow from
`call_spec` plus `callee_respects`, with readiness derived from the actual operand
execution. It rejects a retired transitive argument target and a still-initialized
destination. The suite also exercises every other ordinary backend, Box
allocation, checked-add success at the maximum 32-bit value, overflow, invalid
width, insufficient source/readback budgets and dangling/cyclic readback.

The full public library build passes (3,946 jobs), and the focused suite passes
without diagnostics. All 40 maintained Lean suites, native WP and nine Python
tests pass. `BaselineAudit.lean` audits 1,007 distinct endpoints,
including all 45 new theorems, using only `propext`, `Classical.choice` and
`Quot.sound`. Shared `leanq` inspection exports 914 unique elaborated statement
records from four seeds with zero unknown references. Inspected signatures
retain independent representation/liveness, native shape/fuel and ghost budget
conditions. `callee_respects` discharges the local callee contract;
`call_spec` retains readiness of the actual arguments and concrete success, not
a desired parent source answer or a supplied post-argument context.

Reproduce from the repository root after preparing VM caches:

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
# Run every maintained Lean suite in .github/workflows/verification.yml.
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-helper-statements.json \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.call_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.callee_respects \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.insert_total \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Graph.snapshot
```

Local evidence is in `/var/tmp/subtree-helper-full-build.log`,
`/var/tmp/subtree-helper-calls-tests.log`, `/var/tmp/subtree-helper-regression.log`,
`/var/tmp/subtree-helper-axioms.log` and `/var/tmp/subtree-helper-statements.json`.
These temporary machine-local files are not committed dependencies. The full
pinned regeneration and thirteen ordered Rust tests at `6137120` remain the
unchanged source baseline.

## Remaining requirements

Integrate the checked call step into the shared addressed control engine and
recursive program driver. Serve actual choice, evaluator and maximum calls with
initial frame construction and callee storage closure. Thread the complete
actual suspended caller stack; derive native readiness and sufficient source/
ghost budgets on every actual source path. Reuse completed source/native/type/
binder/helper/control proofs instead of reimplementing them.

Complete exclusive argument/temporary/output owner transfer, actual caller
completeness, returned-loan escape checks and dynamic parsed-region/destructor
interpretation across all branches/calls. Readability alone does not establish
those global invariants. D12 retains the explicit source-operation boundary;
physical compiler/allocator/runtime adequacy is not an initial prerequisite.

Then public maximum/cold-table teardown, separate wrappers/input policy/global
resources/G3 and the remaining mathematical/software/release/application program
still need completion. Production Rust, generated artifacts, existing source/
type/region/control definitions and pins are unchanged. No full C3 or planning-
goal closure follows from this increment.
