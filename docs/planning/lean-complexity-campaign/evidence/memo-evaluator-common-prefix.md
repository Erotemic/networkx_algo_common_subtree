# Complete common evaluator prefix and native lookup routing

Date: 2026-11-18. Baseline: `9f93779` on `Droschinsky-algos`.
Seven new proof modules add 15 public checked theorems. The actual parsed
113-local evaluator entry and all fourteen common instructions now reach the
lookup switch from independent native readable packets and complete ownership.
The result is the independent native lookup answer; all three argument-reference
roots are retired, table view 6 has ended, and return storage is fresh with an
empty mask. Both the actual discriminant inspection and native hit/miss routing
are constructed. Shared query/table/caller aliases remain permitted.

The cache-hit and cache-miss branch bodies, recursive budget composition,
return/closure, public maximum and every other planning target remain open.
This does not close W06-C3/SRC-01 or the full goal.

## Retaining moved-reference pointer cells across actual calls

`SourceCallRootPreservation.lean` proves
`Derived.call_preserves_other_root` from the existing callee respect/readiness
contract and actual call execution. It reconstructs the actual one-pass argument
masks and remaining context. Every non-destination bound root belongs to the
remaining-context guards, including a moved reference local with an empty mask.
The callee and checked result store therefore preserve its raw cell, allocation
class and liveness. There is no supplied post-callee frame or stronger immutable
heap/callee premise. `source_call_state` separately exposes the existing source
call's mask/result-store shape.

`SourceNativeStorageRetirement.lean` proves
`LoanSafeMachine.storageDead_reference`. Native shared referents cannot loan a
cell containing another shared pointer, and preserved original caller reads lie
below fresh callee roots. Those facts discharge the actual storage-dead root
permission even after a moved local's logical mask is empty. Existing owner,
class, root-separation and scan contracts derive every other physical check.
`shared_root` recovers the raw pointer cell from an independently valid initialized
shared local. The general storage and loan rules remain unchanged.

## Actual three-step lookup retirement

`SourceEvaluatorLookupRetirement.lean` splits the real continuation into
`lookupRetire = [storageDead 8, storageDead 7, storageDead 5]` and the existing
lookup switch. `afterLookup_retire` is definitional body identity.
`retire_observes` kernel-checks that locals 1, 2, 3 and 4 remain observed at each
retirement point; `InputLocals.prepare_retire` transports their native values
through the actual reference-ending scan.

`retire_lookup_complete` constructs all three actual instructions with the real
switch as continuation, the retained raw pointer cells, native machine safety,
complete ownership and original caller preservation. It retains native inputs,
result local 4, memory contents, local count and empty unrelated masks, and
returns precisely the three root removals. It assumes neither successful
retirement operations nor execution of a parent evaluator.

## Native lookup answer and stable common execution

`SourceEvaluatorLookupContinuation.lean` proves
`lookup_continuation_complete`. The earlier constructed helper-call endpoint
supplies fixed sufficient fuel/readback bounds and stable world/activation/cost.
The fuel threshold is enlarged by the existing independent native `lookupDepth`.
The existing source lookup theorem then identifies the result with
`encodeOption (LookupEvents.lookup table left right).1`, without an expected
callee result or cache-soundness premise.

The endpoint derives post-argument masks, unchanged roots/count and native inputs,
uses actual retained-context preservation for the moved reference cells, and
constructs all three retirements. Lookup and retirement compose in the existing
`Calling.Prefix` relation at every larger fuel/readback pair. Other old local
root cells and unrelated empty masks remain preserved. The prefix retains actual
instruction/call costs; constructing the suffix is still necessary for a complete
evaluator result/full-cost theorem.

## Last use and concrete scope for the following branches

`SourceReferenceLastUse.lean` proves `LoanEnding.forget_ended_shared` for the
existing finite scan: a listed shared local becomes empty once the actual
continuation certifies its final observation has ended. Repeated indices are
allowed. This changes no source code, lifetime algorithm or source equivalence.

The preceding storage/table/query/borrow prefix theorems are strengthened to
expose root preservation, return-cell freshness, the return mask's emptiness,
raw table-view pointer storage, and the actual end of view 6 before lookup.
The last-use fact is checked against the pinned continuation at the first query
storage-live instruction, following the final table reborrow. Existing endpoints
and consumers are retained; no previous mathematical statement is weakened.

`SourceEvaluatorCommonPrefix.lean` proves `actual_body_common_prefix`: the
fourteen recorded actions followed by `lookupSwitch` are exactly the pinned
source body. `LookupScope` records native input/result locals, the actual local
count, initialized result storage, fresh empty return storage, the bound raw
pointer and ended mask for view 6, retired roots 5/7/8, and preservation of every
other original local root. `common_prefix_complete` constructs the whole common
prefix and this scope from the earlier independent native machine assumptions.
It needs no successful evaluator or desired final world.

`native_entry_machine` factors the actual parsed entry construction out of the
earlier `entry_lookup_complete`, retaining independent readable packets,
complete ownership, exact initial state, local count 113 and unbound non-argument
roots. The earlier eleven-instruction endpoint still checks through this shared
entry theorem.

`SourceEvaluatorCommonEntry.lean` proves `lookup_switch_native` and
`entry_common_prefix_complete`. The former constructs actual addressed
inspection of local 4 and checks the unchanged routing: a native cached result
selects branch 0, and a miss selects branch 1. The latter composes actual parsed
entry, all fourteen instructions, complete native scope and successful actual
switch inspection at fixed joint sufficient bounds. No branch-body execution
claim follows from selecting its route.

## Consumers and validation

`Tests/SourceAddressedControl.lean` now has two new common-prefix consumers:

- Warm hit: both query pointers select inline words inside the same Box owned
  by the table. The endpoint constructs the actual entry/common prefix, native
  optional result, ended view 6, all three retired argument roots and actual
  hit discriminant. The expected answer is derived through the independent
  lookup model after applying totality, rather than supplied as a call premise.
- Cold miss: both query references borrow the same actual suspended caller's
  root. Independent readability and complete owner resources construct the
  prefix, native miss and actual miss discriminant. The original caller's raw
  word cell and liveness are preserved through every call and retirement.

All checks terminate successfully:

- Full maintained library: 4,042 jobs; replayed warnings are in older modules.
- Five affected suites: `SourceAddressedExpressions`, `SourceAddressedControl`,
  `SourceHelperCalls`, `SourceOwnerLifecycle`, `SourceRecursiveExecution`.
- All eight recursive cold/nonempty/warm-hit/overflow/failure runtime cases
  retain complete source values/full costs, caller bytes, live Box ownership/
  coverage and cleanup checks.
- `BaselineAudit.lean`: 1,480 distinct endpoints, including all 15 new public
  theorems; only `propext`, `Classical.choice`, `Quot.sound`.
- Ten selected `leanq statement` seeds: 1,085 unique elaborated declarations,
  zero unknown references.

Rust/generated source, maintained Python, source semantics, reference-ending
algorithm and dependency pins are unchanged. Broader 47-suite/native-WP/nine-
Python evidence remains at `d49f638`; thirteen ordered Rust tests remain at
`823df34`, not fresh runs of this increment.

Reproduction from the repository root:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceAddressedExpressions.lean)
(cd proofs && lake env lean Tests/SourceAddressedControl.lean)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceOwnerLifecycle.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-common-prefix-statements.json \
  SubtreeProofs.Rust.SourceEval.Addressed.Derived.call_preserves_other_root \
  SubtreeProofs.Rust.SourceEval.Addressed.LoanSafeMachine.storageDead_reference \
  SubtreeProofs.Rust.SourceEval.LoanEnding.forget_ended_shared \
  SubtreeProofs.Rust.SourceEval.Evaluator.retire_lookup_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.lookup_continuation_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.actual_body_common_prefix \
  SubtreeProofs.Rust.SourceEval.Evaluator.common_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.lookup_switch_native \
  SubtreeProofs.Rust.SourceEval.Evaluator.entry_common_prefix_complete \
  SubtreeProofs.Rust.SourceEval.Evaluator.native_entry_machine
```

All seven caches are guest-ext4 bind mounts; all Lake/Lean commands run from
`proofs`. Machine-local logs:
`/var/tmp/subtree-common-prefix-{build,control,expressions,helpers,lifecycle,
runtime,axioms,statements}.log` and `subtree-common-prefix-statements.json`.

## Next work

Construct the cache-hit branch and return/closure from the checked native scope,
then empty-query insertion/return and all pair/pair recursion, overflow and
failure paths. Derive the remaining selected move/write/drop/storage/transfer
permissions from actual query read origins, copied-result freshness, closed
masks and last-use facts. Preserve allowed query/table/caller aliases; do not
replace selected permissions with an all-owner/all-loan separation condition.
Compose sufficient stable budgets, interpret dynamic parsed regions and
destructor instances, finish public maximum/cold-table teardown, wrappers/input
policy/resources/G3, and every other target in `docs/planning`. The full goal
remains active.
