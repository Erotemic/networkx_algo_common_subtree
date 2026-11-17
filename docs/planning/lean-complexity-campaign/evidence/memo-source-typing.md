# Memo source types, region scope and operational preservation: 2026-11-17

Baseline: `a18c72d`. Seven new modules extend the
[addressed memo primitive bridge](memo-heap-ownership.md) with checked source
layouts/signatures/annotations, static statement constraints, operational type
preservation, closed ordinary outputs and free/body region scope. The actual
retained extraction passes both type and region certificates in the kernel.
Guard/storage/spatial traces and dynamic shared-loan/lifetime interpretation
for these new helpers remain open; returned ownership alone does not supply them.

## Reusable checker and preservation interfaces

`LookupTypedCode` now has `checkActionWith`/`checkCodeWith` and independent
`ActionConstraintsWith`/`CodeConstraintsWith`, parameterized by a callee output
type map. Their soundness theorems are generic. The existing lookup API remains
the specialization at its original signatures, with the original accepted
operations and type rules. Constructor/projection signatures still use the
independent `Heap.Shape` relation.

`LookupTypeAnnotations.actionAnnotationsWith`/`statementAnnotationsWith` reuse
the existing nested place, operand, aggregate, metadata, key, scrutinee and
unwind-annotation readers with a supplied callee resolver/type map. Generic Box
instances are checked against actual operand types. The old lookup entry points
remain specializations; there is no copied memo primitive type parser.

`LookupTypeExecution.action_typedWith`/`exec_typedWith` preserve actual reachable
cell/local typing through addressed reads, moves, borrows, aggregates, calls
and control, given the independent constraints and local typed callee contract.
`CallsTypedWith` makes that contract explicit. The old operational lookup
interfaces specialize these theorems unchanged.

## Actual source certificates and the owned argument

`MemoSourceTypes` gives the independent memo signatures. Insertion takes a table
value followed by shared left/right words and a shared result; it does not take
a shared table or a Box of the table. Its result is a table value. Concatenation
takes two shared words and returns a word. Copy helpers retain their prior
signatures, and generic Box returns an owned payload of its single argument.

`MemoTypeReader` reads the complete retained memo extraction through the existing
control reader, independent field-layout checker, builtin Box signature checker
and shared annotation readers. It retains intrinsic argument/return prefix
proofs and independent static constraints for the exact normalized bodies.
Layouts include the actual known declarations retained in this extraction,
including the generic Option declaration. No Rust or extraction is changed.

`MemoTypeCertificate.original_checked` is a `decide +kernel` certificate over
the actual source JSON and generated normal forms. `original_boundaries` exports
all four ordinary helpers' checked prefixes and body constraints;
`original_declarations` exports independently meaningful layout witnesses.
No native proof oracle or Python type reifier is used.

| Helper | Signature value inputs | Signature regions | Body region count | Locals |
| --- | ---: | ---: | ---: | ---: |
| copy word | 1 | 1 | 19 | 10 |
| copy result | 1 | 1 | 10 | 6 |
| concatenate | 2 | 2 | 30 | 13 |
| insert | 4 | 3 | 33 | 15 |

## Operational preservation and ordinary result closure

`MemoTypeCalls.run_typed` discharges the local typed-callee contract by fuel
induction for the actual addressed memo interpreter, including generic fresh
Box allocation. The initial environment is typed using the actual checked
argument/return prefix. Insertion's owned table argument is retained as such;
no lookup all-shared input premise is substituted.

`original_run_typed` covers every function/fuel and every successful addressed
run on typed arguments matching the independent call signature. Its result is
typed and old memory is preserved. This is independent of native-value readback,
cache soundness, witness correctness and sufficient-fuel native totality.
`source_run_typed` additionally composes actual retained source execution and
addressed simulation, preserving the complete cost and exact allocation growth.

`MemoTypeRefinement.original_run_unborrowed` derives non-escaping ordinary output
from this operational typing and independent closed output layouts. It excludes
a shared reference hidden in an owned payload, not just a top-level reference.
Generic Box is explicitly excluded: it can legitimately contain a shared loan.
This result does not yet prove the dynamic validity/origin of every intermediate
shared reference in the new helper set.

## Source region binding and annotation erasure

`LookupRegionScope` now supplies `rootsWith`, `TreeWith`/`ForestWith` and
`scanWith`, parameterized by a declaration-ID-to-region-arity resolver. The same
structural coverage proof checks recognized reference/generic-region positions
in every JSON descendant, including unwind annotations. The original lookup
API remains its prior specialization. `TreeWith.mentions_bound` proves a
recognized descendant region is bound; this is not merely a Boolean root check.

`MemoRegionProgram` supplies actual memo declaration IDs and lifetime arities.
Insertion has four value inputs but three region parameters because its table
is owned. Canonical late-bound signature binders, empty explicit outlives/type
constraints, bounded free signature variables and bounded existential body
regions are checked. Body IDs may repeat and leave gaps after Charon unification;
they are bounded by the actual declared count, not required to be densely used.
Unsupported region forms, scope confusion and wrong call region arities fail.

Each definition retains its actual signature/body JSON, region-bearing input/
output/local types, exact erasure to the earlier checked types, inductive scope
proofs and full structural scope trees. The program also retains its typed
source program. `MemoRegionCertificate.original_checked` kernel-checks the
actual extraction; `original_program` exposes the successful read and exact
body coverage.

`scoped_bodies_typed` obtains the operational body constraints from these actual
parsed declarations. `scoped_source_run_typed` consumes those constraints while
retaining the successful region-bearing source read, actual addressed run,
independent output typing/readback, complete cost and allocation growth.
This composes source scope with operational typing; it does not interpret the
new helpers' region names as dynamically valid lifetimes. That requires the
subsequent shared-loan trace proof. The existing lookup retained-world erasure
interpretation remains separately proved and unchanged.

## Validation

The main 3,842-job build, all nineteen Lean suites, native WP example, nine Python
reifier tests and 484-endpoint axiom audit pass. The 23 added audited closures
stay within `propext`, `Classical.choice`, `Quot.sound`; new modules have no
warnings. Existing lookup type, storage, frame, spatial, loan and region results
still compile and their suites pass against the generic interfaces. Shared
`leanq` inspected `scoped_source_run_typed` and `original_run_unborrowed`'s
elaborated statement closure (615 records), confirming the actual source read,
typed/represented runtime premises, completed source/heap runs, unchanged cost
and generic Box exclusion from ordinary output closure.

`Tests/MemoTypes.lean` is in CI. It checks moving the owned table, rejection of
copying/borrowing/Box-wrapping it as an insertion argument, rejection of a false
nested place annotation accepted by control parsing, four-value/three-region
call arities, out-of-bounds signature/body IDs, valid gapped body IDs, and
ordinary output closure without native readback premises. A generic owned Box
containing a shared reference fails the ordinary unborrowed-output claim.
A statically declared but uninitialized call fails execution, preserving the
boundary between type constraints and progress/storage discipline. Fragments
are explicit model/JSON cases, not new compiled Rust mutants; complete actual
source is separately kernel-certified.

Rust, generated code/JSON, tooling and pins are unchanged. The prior `63f929f`
full pinned regeneration and thirteen ordered Rust tests remain the unchanged
provenance/behavior baseline. Input conversion, source primitive interpretation,
compiler/runtime correspondence, physical provenance and unwind execution
retain their named boundaries.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/MemoTypes.lean)
(cd proofs && lake env lean Tests/LookupSourceTypes.lean)
(cd proofs && lake env lean Tests/LookupTypePreservation.lean)
(cd proofs && lake env lean Tests/LookupRegions.lean)
(cd proofs && lake env lean BaselineAudit.lean)
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement SubtreeProofs.Rust.MemoSource.Types.scoped_source_run_typed \
  SubtreeProofs.Rust.MemoSource.Types.original_run_unborrowed \
  --root-module SubtreeProofs.Rust.MemoTypeRefinement
```

## Next required work

Do not repeat memo source type/annotation/static checking, operational typing,
ordinary output closure or binder scope. Next extend guarded local/storage and
intermediate spatial traces to the new signature profile, plus dynamic retained-
heap loans and the scoped lifetime/erasure interpretation. Insertion transfers
an owned table; its initial owner profile and old-plus-fresh return ledger must
remain explicit. Reuse the generic checker/annotation/preservation interfaces.

Then add the actual memo evaluator's owned-local borrows, checked arithmetic,
losing-candidate destruction and overflow/table returns, compose one public core,
and handle indexed/token/reconstruction wrappers, input/error policy, full work
and G3 adversaries. W06-C3, SRC-01, MEM-04, APP-01 and the full planning goal
remain open. A compiler/machine proof is separate from D12's accepted initial
source-operation endpoint, not an invented prerequisite for the memo pilot.
