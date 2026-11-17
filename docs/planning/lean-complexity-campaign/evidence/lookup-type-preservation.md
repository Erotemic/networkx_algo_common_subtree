# Operational lookup type preservation: 2026-11-16

Follow-up: [framed intermediate ownership](lookup-spatial-ownership.md) now
establishes separation across live locals, temporaries and recursive suspended
caller frames on completed normal paths. Stack/borrow/lifetime and official
source adequacy remain open. The preservation milestone and its historical
next steps are recorded below.

Baseline: `304edc1`. This advances the
[checked lifetime-erased source types](lookup-source-typing.md) to successful-run
operational type preservation for the actual addressed interpreter. The proof
uses the independent `Heap.Typed`/`FieldsTyped`/`Shape` judgments and the checked
static constraints. It does not assume a snapshot result is typed to establish
that result's type.

## Primitive preservation

`Rust/LookupTypePrimitives.lean` defines `EnvTyped`: every occupied local has
its declared type. Empty slots are allowed. A shared pointer's typing contains
both a valid actual read and the recursively typed referent. Owned pointers
similarly contain their actual cell and its typing. Finite typing derivations
do not accept dangling or cyclic reachable pointers; exclusive address identity
is a separate property.

`typed_mono` and `fieldsTyped_mono` preserve types when the memory extends old
cells. Local clear/store and memory extension preserve `EnvTyped`.
`projection_fields` relates the static field signature and runtime variant
guard to the independent actual constructor's field types.

`locate_typed` proves a successful place read returns its inferred type and
that its optional address actually reads that same cell. The latter fact is
necessary for `borrow_typed`; a type annotation alone cannot justify the
created reference. Operand/list/rvalue proofs track all invalidating moves,
preserve the complete remaining local typing and construct aggregate types
from independent `Shape`. Scrutinee evaluation preserves remaining locals.

## Control and recursive calls

`Rust/LookupTypeExecution.lean` defines a local `CallsTyped` contract. It
requires typed argument cells and a matching callee signature, and concludes
typed output and old-memory preservation for a successful call.
`action_typed` uses this contract and `ActionConstraints` to prove complete
post-environment typing. `exec_typed` consumes `CodeConstraints`; it handles
both branches, common continuations and early returns. Fallthrough retains
`EnvTyped`; a return has the declared output type. The proofs apply to the
unchanged successful execution and leave its entire cost intact.

The source reader's `Definition` now also retains its checked return/argument
local prefix as a proof field. `TypeReader.check_boundaries` exports it alongside
each helper's body constraints. Concrete original/mutant certificates are
kernel-checked again with this stronger reader; no JSON changed.

`Rust/LookupTypeCalls.lean` proves initial argument-local typing from that
prefix, fresh allocation typing and `run_typed`. The last theorem discharges
`CallsTyped` recursively by fuel induction. Ordinary functions use checked
body/prefix witnesses; generic Box uses exactly its single operand type and
the actual new cell/address. No whole-program preservation premise is left
open. `original_run_typed` and `mutant_run_typed` cover every helper and every
fuel in the two actual programs, including Box.

`Rust/LookupTypeRefinement.lean` composes this with the existing retained-source
control and addressed simulation. `certified_run_typed` and
`certified_mutant_typed` construct actual addressed runs with typed output,
independent snapshot readback, old-memory preservation, exact allocation
growth and the source execution's complete cost. Their output type follows
from the new recursive preservation theorem, independently of snapshot
correctness or an assumed result type.

## Validation and boundaries

The main 3,794-job build, all twelve Lean suites, native WP example, seven
Python frontend tests and 252-endpoint audit pass. Twenty-seven new audited
closures stay within `propext`, `Classical.choice`, `Quot.sound`. New modules
have no warnings. No production/generated semantics, Rust, JSON, dependency
pins or extraction tooling changed.

`Tests/LookupTypePreservation.lean` is in Lean CI. A typed word input with
duplicated owned aliases satisfies the actual copy contract; a separate
kernel evaluation establishes the run succeeds and allocates distinct children.
The suite also applies the recursive theorem to generic Boolean Box and actual
mutant lookup with aliased queries. It checks scope boundaries: static types
permit an uninitialized return that fails dynamically, a statically typed
field of the wrong current variant fails dynamically, and clearing a live
owner passes type checking but fails frame checking. These are instruction
fragments and concrete model inputs, not new compiled Rust mutations.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/LookupTypePreservation.lean)
(cd proofs && lake env lean Tests/LookupSourceTypes.lean)
(cd proofs && lake env lean Tests/LookupFrame.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
```

The result is **preservation for successful runs**. Static checking alone does
not imply initialization, successful variant reads, sufficient fuel or progress.
Existing native-input totality and frame-safety theorems retain their own
premises. `EnvTyped` constrains reachable values, not every unused heap cell.
Type preservation allows shared aliases and duplicated owned aliases; it does
not supply intermediate spatial ownership or a destructor/lifetime semantics.

Next establish that spatial invariant and stack/borrow adequacy, then official
typed LLBC/Rust primitive correspondence. Insertion, concatenation, memo
evaluation/core, wrappers and remaining local source costs are retained work.
Mutable memory, freeing, failed/unwind execution and physical peak-space/
allocator/CPU costs are not proved here. W06-C3, SRC-01, MEM-04 and the full
planning objective remain open.
