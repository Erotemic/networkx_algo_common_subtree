# Memo normal storage and initialization: 2026-11-17

Baseline: `188e5f3`. Three `MemoStack{Calls,Certificate,Refinement}` modules
extend the [memo guard/spatial proof](memo-spatial-ownership.md) with retained
source allocation/deallocation markers, exact declared local counts, and
recursive normal storage/initialization traces. Dynamic loan/lifetime
interpretation, the actual evaluator/core and wrappers remain open.

## Reused storage semantics

`LookupStackCode.Code`, lowering and exact-cost erasure now accept a callee
type. `LookupStackState.inferActionWith`/`verifyWith` accept its value-arity map.
`LookupStackExecution` generalizes call contracts, action witnesses, traces,
erasure and checker soundness at that map. Original lookup entry points remain
specializations of these same definitions and theorems.

The status of each declared slot is dead, allocated empty, or initialized.
Moves require initialized storage and leave it allocated empty. Operand reads,
reborrows and discriminants require an initialized base local. Assignments and
call destinations require allocated storage. Conditional moved drops require
empty storage. The checker follows both branch continuations and early returns;
return requires initialized slot zero. Each trace relates the exact status
state to the actual addressed value environment at every normal instruction.

Distinct `StorageLive` and `StorageDead` instructions are retained until trace
erasure. Both erase to the existing reset instruction with its unchanged step
cost. Repeated markers are permitted by the pinned source profile; owner guards
separately prevent a live owner from being silently lost. This is logical source
storage, not physical frame layout, allocator work, or a new Box allocation.
Normal return transfers slot zero and closes the departing logical frame; it
does not add an unmodeled deallocation charge.

## Actual source and recursive calls

`MemoStackCertificate.original_lower` obtains storage code from the actual
source-control certificate, not from a manually reconstructed function.
`original_erase` recovers the already certified memo program. Kernel checks
verify the actual four bodies and their declaration counts:

| Helper | Value inputs | Declared local slots |
| --- | --- | --- |
| copy word | 1 | 10 |
| copy result | 1 | 6 |
| concatenate | 2 | 13 |
| insert | 4 | 15 |

`countsCheck_sound` relates the counts to the independently typed source
reader's successful declarations and complete helper coverage.
`original_initial_length` confirms that each ordinary helper's initialized
analysis frame has exactly its declared number of slots. The opaque Box
primitive has no interpreted local frame.

`MemoStackCalls.run_sound` discharges all recursive storage-call contracts by
fuel induction. `RunSafe` retains actual source storage traces at every ordinary
call and the same actual successful run for primitive Box. `RunSafe.erases`
recovers exactly the same addressed run and complete cost. Success is still
established separately; checker acceptance is not a totality assumption.

`source_run_stack` composes retained source execution with addressed storage
traces, readback, immutable extension and exact Box-allocation growth.
`concatenate_stack_total` and `insert_stack_total` additionally retain the prior
native totality, independent append/prepend result, operational typing,
guarded local traces, spatial/caller separation, exact event counts and native
Rust agreement. Concatenation owns its fresh result. Insertion returns its
original owned table under the new tail Box and preserves each valid external
owner frame. The spatial premise remains explicit and conditional; storage
checking alone does not prove owner uniqueness, typed pointers, or loan validity.

## Validation

The full 3,850-job build passes. All 21 CI Lean regression suites, native WP
and nine Python reifier tests pass (23 command checks). The opt-in axiom audit
reports 531 endpoints; all 15 new closures stay within `propext`,
`Classical.choice`, and `Quot.sound` (one new closure uses no axioms). The
original lookup storage/borrow/region tests pass against the generalized API.
New modules have no warnings; existing unrelated warnings remain.

Shared `leanq statement` inspection of `insert_stack_total` and `RunSafe`
produced 595 elaborated statement records. The endpoint retains the original
source body, actual input table cell, storage/guard/spatial traces, exact costs,
typed independent readback, tail identity and conditional spatial frame.
Statement inspection is supplementary to Lean checking and the axiom audit.

The source Rust, generated inputs, parser, tools and dependency pins are
unchanged, so the preceding pinned regeneration evidence still applies.
Bind-mount status was checked before building; caches remain on VM-local ext4.
Local logs are `/var/tmp/subtree-memo-stack-{full-build,regression,axioms}.log`
and `/var/tmp/subtree-memo-stack-statements.{json,txt}`.

```bash
(cd proofs && lake build)
(cd proofs && lake env lean Tests/MemoStack.lean)
(cd proofs && lake env lean Tests/LookupStack.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement \
  SubtreeProofs.Rust.MemoSource.Stack.insert_stack_total \
  SubtreeProofs.Rust.MemoSource.Stack.RunSafe \
  --root-module SubtreeProofs.Rust.MemoStackRefinement
```

`Tests/MemoStack.lean` distinguishes successful reset-only runs from invalid
unallocated/dead writes, checks memo call arities and dead destinations, moved
initialization, reborrow readiness, repeated markers, bounds, branch joins,
early returns, recursive copying, primitive Box, and successful native
concatenation/insertion with aliased keys and an arbitrary witness score.
These synthetic fragments are not compiled Rust mutants. Actual bodies are
covered by the kernel certificates and recursive theorems.

The next work is dynamic shared-loan preservation for these helpers and its
composition with checked source-region metadata in the retained-world lifetime
interpretation. Then inspect the actual evaluator's arithmetic, owned-local
borrows, losing-candidate destruction and error/table returns, and compose a
public core and wrappers. W06-C3, SRC-01, MEM-03/04 and the full planning goal
remain open. D12's scoped source-operation boundary remains unchanged.
