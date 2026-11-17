# Checked lifetime-erased lookup source types: 2026-11-16

Baseline: `39e2219`. This advances W06-C3 from
[normal local frame safety](lookup-frame-safety.md) to kernel-checked source
declaration layouts, nested annotations and static type constraints. Both
complete, retained pinned Charon extractions are checked against their own
existing normalized bodies. Their JSON, Rust, generated code, extraction tools
and dependency pins are unchanged.

## Independent rules and soundness

`Rust/LookupSourceTypes.lean` implements recursive type equality and constructor,
projection and callee signatures over the existing `Heap.Ty`. `same_eq` and
`sameList_eq` prove equality checking sound. `constructorFields_sound` and
`constructorFields_complete` identify exactly the existing independent
`Heap.Shape` relation. The source checker does not redefine that relation to
match the JSON.

`Rust/LookupTypedCode.lean` infers place/operand/rvalue types from fixed local
declarations and checks assignments, calls, returns and every control branch.
Copies are restricted to Boolean, u32 and shared-reference values. Generic Box
construction takes one value and returns its owned type; ordinary calls must
match their helper signature. `aggregate_shape` connects the actual inferred
operand types to independent constructor signatures. `checkAction_sound` and
`checkCode_sound` produce explicit `ActionConstraints`/`CodeConstraints`.
These are static constraints, not operational type-preservation theorems.
The preceding frame checker separately handles move availability and local
initialization/ownership classes.

## Retained source checks

`Rust/LookupTypeReader.lean` reads the supported lifetime-erased type forms,
checks declaration identities and generic instances, and validates eight
concrete layouts: both variants of word, table and Option, plus entry and
result records. Field names, order, positional status, variant IDs and enum
discriminant encodings are checked. Option's parameter is instantiated with
the result type. Tuple and Box builtin identities are checked; Box is the
opaque one-parameter declaration. `layoutCheck_sound` and `layouts_sound`
connect the actual parsed field types to `Heap.Shape`.

`Rust/LookupTypeAnnotations.lean` checks:

- Ordinary parameter/result signatures and all declared local types, including
  their return/argument prefix and safe, nonvariadic Rust ABI.
- Every nested place annotation, operand/literal type, unit pointer metadata,
  aggregate generic instance, call generic instance and switch key type.
- The generic opaque Box constructor's input, output and inherent self type.
- Supported unwind drop-place annotations, without assigning unwind behavior.

Unsupported types, mutable references and unexpected generic arguments fail.
Reference regions are retained in the source input but deliberately erased by
this checker. Region binding, outlives/lifetime semantics and complete Rust
well-formedness are not established.

The resulting `Program` carries layout soundness, every definition's static
constraints and explicit coverage of all four ordinary helpers. `check_sound`
connects acceptance to a successful source read and those proofs.
`check_functions` uses the coverage field to rule out vacuous acceptance of an
empty helper list.

`Rust/LookupTypeCertificate.lean` uses `decide +kernel` for both actual source
inputs. `original_checked` and `mutant_checked` validate every check and equality
with the corresponding existing body. `original_functions` and
`mutant_functions` export constraints for every ordinary function;
`original_declarations` exports actual parsed layouts and their independent
shape witnesses. There is no native-evaluation proof oracle. Both programs
have eight layouts and four checked helpers; their local counts are 10, 15,
6 and 20 (23 for mutant lookup).

The extra-comparison mutant is well typed and passes these certificates. Its
failure of the original comparison budget remains a distinct checked result.
No additional runtime checks or resource charges have been introduced.

## Validation

The 3,790-job main build, all eleven Lean suites, native WP example, seven
Python frontend tests and 225-endpoint axiom audit pass. Fifteen new audited
closures stay within `propext`, `Classical.choice`, `Quot.sound`; the new modules
have no warnings. Main pins and production/generated semantics are unchanged;
the previous pinned regeneration is the source-provenance baseline.

`Tests/LookupSourceTypes.lean` is registered in Lean CI. Its source fragments
reject a false place annotation that the control reader accepts, a wrong
literal annotation, wrong Box identity/instance, unsupported scalar/mutability,
incorrect Option parameter, bad constructor field type/arity/variant and a
borrow-only helper called with an owned argument. A malformed word constructor
passes the frame checker but fails the independent type constraints. These
are explicit instruction/type fragments, not complete compiled Rust mutations
or lifetime-well-formed LLBC crates. The complete original and actual compiled
cost-mutant inputs pass the kernel certificates.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/LookupSourceTypes.lean)
(cd proofs && lake env lean Tests/LookupFrame.lean)
(cd proofs && lake env lean Tests/LookupHeap.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
```

## Remaining W06-C3 obligations

The field-declaration/static-annotation gap is closed for the supported
lifetime-erased lookup fragment. Next connect the checked constraints to
operational heap type preservation and establish spatial ownership among all
intermediate objects. Existing returned ownership and normal local cleanup
results do not establish that stronger spatial invariant.

Stack allocation/liveness, borrow lifetimes, mutable memory, freeing, failure/
unwind behavior and official typed LLBC/Rust primitive simulation remain open.
Insertion, concatenation, memo evaluation/core and public wrappers remain
required. These certificates do not imply physical space, allocator time or
CPU-time bounds. SRC-01, W06-C3, MEM-04, APP-01 and the full planning objective
remain open.
