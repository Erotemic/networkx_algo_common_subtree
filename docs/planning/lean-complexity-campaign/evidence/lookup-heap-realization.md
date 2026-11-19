# Addressed lookup memory realization: 2026-11-16

Follow-up: [exclusive returned ownership](lookup-return-ownership.md) now proves
duplicate-free complete fresh Box ownership for generated lookup/copy outputs.
Intermediate frame/destruction and source/lifetime adequacy below remain open.

Baseline: `158a33a`. This is the next partial W06-C3 delivery after the
[source-control certificates](lookup-source-certificates.md). It implements
and proves a memory realization for the read-only fragment. It does not close
official typed LLBC/Rust adequacy, unique ownership, destruction or the full
memo evaluator/source-cost theorem.

## Concrete representation and primitive proofs

`Rust/LookupHeapMemory.lean` distinguishes `Cell.shared Pointer` from
`Cell.owned Nat`. Shared pointers name a heap cell plus an inline field path;
owned pointers name a separate Box cell. Reads check address and field bounds.
The finite `Represents`/`RepresentsFields` relation connects these addressed
values to existing immutable snapshots. It permits shared aliases. A dangling
pointer cannot represent a snapshot; cyclic pointer structure cannot have
a finite representation proof. No validity premise is imposed on unreachable
warm heap cells.

`alloc` picks the previous heap length and appends exactly one cell.
`alloc_fresh` proves freshness, exact readback and growth by one;
`alloc_rep` connects that operation to the snapshot Box constructor.
`Represents.mono` and `read_extends` preserve all existing represented values
and reads under heap extension. `Extends.eq_of_length` identifies unchanged
memory when no new cells were allocated.

`Rust/LookupHeapTyping.lean` gives independent field signatures for word,
table, entry, result, option and tuple constructors, with the actual `u32`
bound for the numeric payload. `Typed` checks represented cell shapes and
pointer referents; it is not defined as existence of a snapshot.
`Represents.typed` proves the typing transfer. Native `encodeWord`,
`encodeResult`, `encodeTable` and `encodeOption` all meet these signatures.
This types reachable represented values, not arbitrary unreachable heap cells.

`Rust/LookupHeapPrimitives.lean` implements local reads and invalidating moves,
Copy-eligible scalar/shared-pointer reads, guarded fields, dereferences,
aggregate assembly, discriminants and shared address construction. `locate`
follows actual pointers; it does not decode a complete immutable snapshot and
run the old interpreter. Its correctness includes the readback property of
the address it computes. Shared borrows of stack-only places are rejected.
`heapBorrow` recognizes places that cross a pointer dereference; such successful
locations have a heap address. All address expressions of both actual generated
programs meet this criterion (`program_borrows`/`mutant_borrows`).

`locate_spec`, `borrow_spec`, `operand_spec`, `operands_spec`, `rvalue_spec`
and `scrutinee_spec` construct successful concrete primitive executions from
represented successful snapshot executions, preserving values, moves and
complete environments. New allocation cannot invalidate earlier shared aliases.

## Calls, control, costs and actual lookup

`Rust/LookupHeapExecution.lean` independently executes normalized instructions
against memory and locals. The call interface passes and returns the heap;
complete source costs compose at every actual instruction/call. Only Box creation
grows memory. `action_spec` and `exec_spec` compose the proved primitive rules,
including short circuit, early return and common continuation behavior.
`run_spec` discharges the local callee contract by fuel induction for arbitrary
bodies whose borrows remain in this heap fragment. It is not an assumed
whole-program resource bound or representation law.

Its guarantee is constructive: each represented successful snapshot call yields
a successful addressed call with the **same complete `Cost`**, represented
return, preserved old memory, and

```text
after.length = before.length + cost.events.allocations.
```

`Rust/LookupHeapRefinement.lean` connects both concrete retained source programs
through their earlier kernel certificates (`certified_run_spec` and
`certified_mutant_spec`). It also proves:

- `copy_spec`: sufficient-fuel copying returns a typed represented word with
  the existing exact copy/Box counts and fresh-cell growth.
- `compare_spec`: sufficient-fuel comparison returns the existing equality
  answer/count and leaves the entire memory exactly unchanged. Both arguments
  may point to the same cell or share substructure.
- `lookup_spec`: for every represented table/query and the established sufficient
  fuel, an actual addressed lookup succeeds, returns a typed representation of
  independent `findResult`, preserves old cells, and has the existing exact
  event vector, allocation growth and `steps ≤ 256 * events.units` envelope.
  Cache soundness or unique keys are not needed for this contract.
- `lookup_all_runs`: every returned result/cost at that sufficient fuel satisfies
  the same contract, by deterministic execution. This theorem retains the fuel
  premise; it makes no separate claim about arbitrary below-threshold executions.

The earlier `LookupEvents.sound_unit_bound` composes with these exact events
under `TableSound` to recover the same readable lookup envelope. Without that
premise an oversized stored witness still has to be copied and charged.

`Rust/LookupHeapInputs.lean` constructs layouts for every native word/result/
entry/table, proves their representation and preservation of existing memory,
and establishes `inputs_exist` for every table/query. These are input-layout
constructions, not an uncharged conversion executed inside the lookup contract.
Initial representation setup remains outside lookup's work account.

## Validation

The 3,776-job build, all nine Lean suites, native WP example, seven existing
Python reifier tests and 175-endpoint audit pass. All 23 new closures stay
within `propext`, `Classical.choice`, `Quot.sound`; new modules have no warnings.
See [`PROOF_STATUS.md`](../../../../proofs/PROOF_STATUS.md).
`Tests/LookupHeap.lean` exercises actual generated programs and memory primitives:
double dereference through Box, shared field address/readback, invalid address/
field/variant, rejected stack borrowing, repeated move, rejected owned Copy/live
drop, aliased full comparison, fresh copied children, and an oversized cache hit
whose copied children have fresh addresses. The original empty lookup and real
Rust extra-comparison mutant both return `None`, with comparison counts zero
and one respectively. These use kernel decisions, not native proof oracles.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/LookupHeap.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Main pins, production Rust, generated source/snapshots and extraction tooling
are unchanged. No Rust behavioral change needs a new extraction. The pinned
full regeneration passed at the baseline commit.

## Remaining source obligations

Memory here is immutable apart from fresh allocation. Storage reset invalidates
locals; it does not free heap objects. `Represents` does not assert unique Box
ownership, distinct owned subtrees, absence of unreachable allocations or a
Rust lifetime discipline. The next obligation is a proved ownership/frame
invariant for the actual generated functions, including safe resets, moves,
return escape and conditional destruction. Stack borrows and mutation will need
their own extension for the memo core. The retained JSON type declarations also
need a checked field-layout/type correspondence to these signatures.

The list implementing the logical store is not claimed constant-time memory;
the theorem preserves declared source currencies. Allocator implementation,
physical layout/bytes, allocation failure, unwinding, stack exhaustion, logical
versus peak live space, and CPU/Lean/Cargo runtime are not conclusions.
The official LLBC/Rust source-primitive simulation, insertion, concatenation,
memo evaluation and named public core/wrappers remain W06-C3 requirements.
This delivery advances the explicit address/type/read/Box-allocation part;
SRC-01, MEM-04, APP-01 and the full planning objective remain open.
