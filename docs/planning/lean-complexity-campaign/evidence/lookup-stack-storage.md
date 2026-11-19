# Checked normal lookup storage lifetimes: 2026-11-17

Follow-up: [stable typed shared loans](lookup-shared-loans.md) now track actual
typed reads in the retained caller heap through source-certified reborrows and
recursive execution, with borrow-free ordinary results. Source region and
official interpretation adequacy remain open. The storage milestone and its
historical next steps are recorded below.

Baseline: `00549d4`. This advances W06-C3 from
[intermediate spatial ownership](lookup-spatial-ownership.md) to explicit
normal-path local storage allocation, initialization and deallocation. The
retained source's `StorageLive` and `StorageDead` instructions stay distinct.
Both concrete source extractions and their exact declaration counts are
kernel-checked; no Rust, generated JSON/code, pins or extraction tools change.

## Pinned source conventions

Charon revision `454586e9b770231e66d2062993e632dfc06463e2` describes
`StorageLive` as allocating or reallocating a local, and `StorageDead` as
deallocating it, with repeated deallocation allowed. Remaining non-return
locals are implicitly deallocated at function exit. Its
`charon/src/transform/finish_translation/insert_storage_statements.rs` pass
adds missing storage markers for used non-argument locals, including the return
slot. The retained extractions start each ordinary helper with `StorageLive 0`.
The AST definitions are in `charon/src/ast/bodies/structured.rs`.

The model starts argument slots allocated and initialized, and other slots
dead. It permits `StorageLive` on already allocated storage, which resets
initialization; requiring prior deallocation would incorrectly reject the
pinned source convention. Source compilation and extraction remain trusted
boundaries; reading these definitions is not an official Rust semantics proof.

## Storage syntax and checked states

`Rust/LookupStackCode.lean` normalizes the supported source routing while
retaining each original storage action. `lower_erases` proves that erasing
this view gives exactly the existing source-control normalizer's code.
Concrete erasure certificates connect both actual stack bodies to the
unchanged original/mutant `Program.body` functions.

`Rust/LookupStackState.lean` distinguishes dead, allocated-uninitialized and
allocated-initialized slots. `StateRep` relates these states to every actual
value-environment index, including out-of-range slots. Dead/uninitialized
slots contain no value; an initialized slot contains an actual value.

The executable checker requires initialized roots for copies/borrows/projections,
initialized moved operands, and allocated assignment/call destinations after
operand moves. A move leaves allocated uninitialized storage. Allocation resets
the slot to uninitialized; deallocation marks it dead. Supported conditional
drops require allocated uninitialized storage, matching the accepted moved-drop
fragment. This is a conservative supported profile, not a complete treatment of
all Charon drop forms. Calls check their actual arity. Both source branches
retain their own states through common continuations; early returns skip the
continuation and require an initialized return slot.

`Rust/LookupStackPrimitives.lean` proves exact state consistency after actual
successful primitives. `StateRep.initialized` constructs the actual initialized
value, and `placeReady_sound` identifies the initialized base slot. `store_spec`
proves the destination was allocated. Argument evaluation preserves sequential
move effects and proves the actual argument count. These facts are independent
of value typing and ownership classes.

## Traces and recursive calls

`Rust/LookupStackExecution.lean` supplies actual post-operand state witnesses,
allocated destination guards and callee occurrences. `Trace` records exact
source storage transitions and actual value environments at statement/control
frontiers, including early returns. Normal frame exit closes its local storage;
`closed_frame` proves consistency of that closed state. This logical closure
does not prove a destructor safe; the previous normal frame-safety certificate
separately proves that departing non-result locals own no Box.

`verify_sound` constructs these traces from accepted checks and actual
successful execution. `Trace.erases` recovers exactly that heap execution and
the complete cost. Pointer/variant read validity is not inferred from an
initialization flag; actual successful reads and the independent operational
typing proof retain those obligations.

`Rust/LookupStackCalls.lean` proves initial argument consistency, recursive
storage safety and erasure at every fuel. Every callee receives its own local
state. Generic Box uses the existing opaque allocation primitive; ordinary
callee safety is discharged by fuel induction. No whole-program storage safety
premise remains open.

`Rust/LookupStackCertificate.lean` kernel-checks both real bodies and matches
the chosen counts to actual parsed typed declarations: 10, 15, 6 and 20 locals,
with 23 for mutant lookup. `countsCheck_sound` also proves coverage of all four
ordinary helpers, ruling out an empty-list count certificate. These are exact
declaration counts, not physical stack sizes. Both concrete lowerings, erasures,
body checks and count checks are kernel-checked without a native proof oracle.
`original_run_safe` and `mutant_run_safe` cover all correctly arity-matched
completed runs at every fuel.

`Rust/LookupStackRefinement.lean` exports `certified_run_stack` for the retained
original source execution with the same full cost/readback/allocation growth.
`lookup_stack_total` composes all represented native inputs at sufficient fuel
with actual success, recursive stack/spatial/frame certificates, final exclusive
ownership, independent typed first-hit readback, old-memory preservation,
exact events/allocation growth and the instruction envelope. Existing totality
supplies success rather than assuming acceptance implies progress.

## Validation

The main 3,807-job build, all fourteen Lean suites, native WP example, seven
Python frontend tests and 338-endpoint audit pass. Thirty-four new audited
closures stay within `propext`, `Classical.choice`, `Quot.sound`; new modules
have no warnings. Existing source provenance/regeneration evidence is unchanged.

`Tests/LookupStack.lean` is in Lean CI. Explicit fragments write into never
allocated or already dead storage and still return the expected Boolean under
the old reset-only interpreter; both fail the new checker. Other cases cover
valid reallocation, repeated deallocation, move/uninitialized reads, conditional
moved drops, call arity, branch-specific dead storage, early return, generic Box
and actual copy's recursive theorem. These are model instruction fragments,
not newly compiled Rust mutations or complete lifetime-checked LLBC crates.
Both actual retained source programs pass the full kernel certificates.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/LookupStack.lean)
(cd proofs && lake env lean Tests/LookupSpatial.lean)
(cd proofs && lake env lean Tests/LookupTypePreservation.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
```

The concrete storage-certificate module took about four minutes to build
locally because its kernel reductions read the complete retained inputs.
Keep the live Lake session and wait for its result; an observation timeout is
not a failed build. Subsequent unchanged builds reuse its artifact.

## Remaining W06-C3 obligations

Normal local storage/initialization discipline is now checked against both
retained source programs and proved sound in the supported interpreted fragment.
This is a logical allocation-status semantics with heap-only shared pointers.
It does not model physical stack addresses or establish borrow-region binding,
outlives relations, mutable borrowing, freeing or failed/unwind execution.
Official typed LLBC/Rust primitive adequacy remains open. In particular this
does not turn the earlier lifetime-erased type reader into a Rust borrow checker.

Next establish shared-borrow lifetime/source adequacy for the immutable lookup
fragment, then extend as needed to insertion, concatenation, memo evaluation/core
and public wrappers. Physical stack/heap space, allocator work and CPU time
remain separate from the retained instruction/event currencies. W06-C3,
SRC-01, MEM-04 and the full planning objective remain open.
