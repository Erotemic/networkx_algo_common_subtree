# Checked intermediate lookup frame safety: 2026-11-16

Baseline: `aa57d78`. This advances W06-C3 from
[exclusive returned ownership](lookup-return-ownership.md) to explicit
certificates for intermediate local clobbers, moves, callee ownership profiles
and return cleanup. It concerns completed normal executions of the existing
addressed interpreter. It is not official typed LLBC/Rust, lifetime, failure/
unwind or spatial-ownership adequacy.

## Concrete local conditions

`Rust/LookupFrameState.lean` defines `Plain` values that contain no owned Box
constructor, including tuples/aggregates of plain values and shared pointers.
Shared pointers do not own their referents. `Plain.footprint` and
`disposable_no_owned` prove their owned-occurrence list is empty, for any memory.
This is an independent structural property of the actual value, not a flag
that is assumed trustworthy.

A finite `State` abstracts every local as empty, definitely non-owning, or
potentially owning. `StateRep` relates this to **all** concrete local indices,
including actual emptiness outside the finite list. Potential ownership is
conservative and does not assert exclusive address identity. Moves empty their
source; copying or borrowing yields a non-owning result. An aggregate's flag
is conservative; a tuple is non-owning only if all components are non-owning.

The checker rejects a reset or overwrite when its destination may still own
data. For assignment/call it checks the destination **after** operand moves,
so transferring a local into itself is handled correctly. Conditional moved
drops require an empty slot. Returns require the expected result class in slot
zero and only empty/non-owning values in every other slot.
`return_frame_disposable` shows that moving slot zero to the caller then leaves
no owned value in the departing frame.

## Executable analysis and soundness

`Rust/LookupFrameChecker.lean` implements the analysis. `verify` threads the
exact local states through both arms using a continuation, rather than joining
different ownership states unsoundly. Early returns check their frame and skip
the common continuation. All fallthrough states must satisfy that continuation.
Move availability, destination bounds and helper arities are checked. Ordinary
helpers require non-owning arguments; Box construction accepts one moved or
non-owning value. This is an ownership profile, not a complete type signature.

`Rust/LookupFramePrimitives.lean` proves the rules against actual heap primitive
execution. `operand_sound`, `operands_sound` and `rvalue_sound` establish the
flag/value relation and complete post-environment invariant. `store_spec`
identifies the actual clobbered value as disposable. Read validity, pointee
typing and storage allocation/liveness remain the interpreter's and later
source simulation's obligations. Acceptance alone does not prove a successful
run or make an invalid copy/borrow read valid.

`Rust/LookupFrameExecution.lean` defines `Guarded`, a concrete execution
certificate. It records the actual action, intermediate memory/environment,
complete cost, safety of the actual clobber, and every callee occurrence.
At return it records cleanup of the whole non-result frame. `Guarded.erases`
proves this is an execution of the unchanged heap interpreter with exactly
the same result, memory and full cost. `verify_sound` constructs the certificate
and output/state invariant from successful checked execution. Its callee
premise is local and is subsequently discharged, not left as a whole-program
safety assumption.

`Rust/LookupFrameCalls.lean` discharges it by fuel induction. `RunSafe` contains
the guarded body and recursive callee certificates at every depth; Box is the
existing fresh allocation primitive. `run_sound` proves both result class and
recursive frame safety for every completed run whose arguments satisfy the
ownership profile, for all fuels. `RunSafe.erases` preserves actual execution.

`original_checked` and `mutant_checked` kernel-check every ordinary helper body
of the actual normalized programs. Twenty empty padding slots give a finite
analysis environment large enough for their local IDs; this is not a physical
stack-size or runtime claim. `original_run_safe` and `mutant_run_safe` apply the
generic soundness theorem. No native-evaluation proof oracle is used.

## Public composition and nonvacuity

`Rust/LookupFrameRefinement.lean` exports:

- `lookup_safe`: every completed lookup on three shared-pointer arguments
  has recursive frame-safety evidence, without a sufficient-fuel premise.
- `certified_run_safe`: the retained original source-control certificate
  composes with the frame proof and addressed realization, preserving the same
  complete cost, represented result, old memory and allocation growth.
- `lookup_guarded`: for arbitrary represented native table/query inputs and
  established sufficient fuel, an execution exists with independent first-hit
  readback, typed output, intermediate frame safety, exclusive returned Box
  ownership, old-memory preservation, exact event counts and the instruction
  envelope. The earlier totality theorem supplies existence; the frame checker
  is not used to assume it.

The actual interpretation and all production/generated source remain unchanged.
These are proof certificates, not additional runtime checks with unpriced work.
The cost-mutant still passes frame safety: an extra comparison is a valid local
ownership transition while violating its old comparison budget. The resource
and frame obligations remain distinct.

## Validation and semantic countermodels

The 3,785-job build, all ten Lean suites, native WP example, seven Python
reifier tests and 210-endpoint audit pass. Twenty new audited closures stay
within `propext`, `Classical.choice`, `Quot.sound`; new modules have no warnings.
See [`PROOF_STATUS.md`](../../../../proofs/PROOF_STATUS.md).
`Tests/LookupFrame.lean` is registered in existing Lean CI. Handwritten instruction
fragments return the expected Boolean under the old interpreter while resetting,
overwriting or abandoning a live owned local; all fail the new certificate.
Other cases cover a valid moved return, a repeated move, passing ownership to a
borrow-only helper, safely clearing a non-owning tuple, early return, and an
owned/non-owned branch pair followed by a shared reset. These are explicit
instruction-fragment countermodels, not claimed compiled Rust mutations or
complete typed LLBC crates. Both real generated programs pass their kernel
certificates; the existing real extra-comparison mutation remains tested.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/LookupFrame.lean)
(cd proofs && lake env lean Tests/LookupHeap.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Main pins, Rust, generated code/JSON and extraction tooling are unchanged.
The earlier full pinned regeneration remains the source-provenance baseline.

## Remaining W06-C3 obligations

Normal completed local resets/overwrites now discard no owned Box; conditional
moved drops see empty slots; moves are tracked, callee ownership profiles hold,
and non-result locals own no Box at return. This closes those local guard and
cleanup obligations in the declared model.

The flag analysis does not prove disjoint spatial ownership among every live
local/heap object. The prior result proves exclusive returned ownership, not
that whole intermediate spatial invariant. Source field/type declarations still
need a checked correspondence; stack allocation/liveness, borrow lifetimes,
mutable memory, official typed LLBC/Rust primitive simulation and failure/unwind
paths remain open. The heap interpreter still has no freeing operation.
Insertion, concatenation, memo evaluation/core and separate public wrappers are
retained W06-C3 work. No physical peak-space, allocator-work or CPU-time theorem
follows from these certificates. SRC-01, MEM-04, APP-01 and the full planning
objective remain active.
