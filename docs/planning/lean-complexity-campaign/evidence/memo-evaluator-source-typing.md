# Actual evaluator declarations and partial-local typing: 2026-11-17

Baseline: `02d5689`. Eight maintained modules check actual lifetime-erased types
for the complete nine-definition source profile and prove primitive preservation
of independently typed partial locals. This advances W06-C3. Recursive control/
callee discharge, addressed owners/storage/loans/regions and live destruction,
public maximum/wrappers and global resource obligations remain open. The full
planning goal remains open.

## Shared model and exact declarations

`Heap.Ty.option` and the independent `Shape.optionNone`/`optionSome` constructors
add parameterized options to the existing heap/snapshot type model. Existing
embedding-option encodings retain their original type and proofs. The shared
source type reader accepts the two actual option instances, embedding and u32;
other instances remain rejected by this source profile. The old lookup regional
reader explicitly rejects the expanded option type pending its regional adapter.
There is no second type universe, expression interpreter or source parser.

`SourceEvalTypes` supplies exact signatures for all eleven callable identities:
the nine ordinary functions, polymorphic Box creation and native checked u32
addition. Insertion and evaluation retain their owned table input. Evaluation
returns the option/table tuple; checked addition returns an option of u32.
Projected moves infer types along owned routes and reject traversal through
shared references. Copying remains restricted to scalar/shared types, and u32
literal bounds are checked. Aggregates use their declared destination type,
which determines the parameter of an otherwise ambiguous empty option.

`SourceEvalTypedCode` checks all retained source-control arms, including source
storage markers, live drops, fake reads and the explicit undefined-behavior
leaf. `ExprConstraints.aggregate` carries an independent `Heap.Shape` witness;
less-than requires two u32 operands and a Boolean destination. Static acceptance
of an undefined-behavior leaf does not make it a successful execution or prove
it unreachable. The executor still rejects it.

`SourceEvalTypeAnnotations` reuses shared place, metadata, switch-key, layout
and type readers. Its syntax adapter checks projected moves, literal/scalar
annotations, less-than, aggregate generic instances, call destinations/arguments,
Box instances, unwind drop-place annotations and fake reads. Unwind execution
remains outside the normal source semantics. Drop-glue identities and drop-place
types are retained; generic destructor-instance typing/semantics still belongs
to the addressed live-destruction adapter.

`SourceEvalTypeReader` retains the exact definitions returned by the existing
whole-program source reader. Its alignment proof equates the entire definition
list, including code, function identity and local count. Local declarations
must have the source count and exact return/argument prefix. The generic Option
declaration is checked at **both** actual instances: checking only its embedding
instance would miss an erroneous hard-coded embedding field at the u32 instance.
Both instances carry independent Shape witnesses.

`SourceEvalTypeCertificate.original_checked` kernel-checks all nine actual
bodies against `SourceEval.Certificate.original.body`. `original_boundaries`
provides actual-body constraints and typed return/argument prefixes for every
ordinary function, including the 113-local evaluator and seven-local public
maximum. `original_declarations` exposes both option layout witnesses and exact
typed/source definition-list alignment. No native proof oracle is used.

## Operational partial-local primitives

`SourcePartialTyping.SlotTyped` permits an empty slot at its declared type and
otherwise preserves constructor shape, field types, scalar width and typed
shared referents/owned payloads. Its field-list relation preserves positions
and length. This is an initialization-compatible type invariant, not proof that
a slot is initialized or its shared referent remains alive in addressed memory.

`SlotTyped.materialize` produces the existing independent `SnapshotTyped`
relation. `SlotTyped.get` and `read` use independently typed projections;
`SlotTyped.take` proves that a successful field move returns a typed complete
value and leaves a typed partial value of the original type. Holes, sibling
fields, constructor tags and Box shells remain represented. Shared snapshots
can be read but cannot be moved through. Existing exact destructor-work and
move/sibling theorems remain unchanged.

`SourcePartialTypeLocals` connects split places to the shared place-type rules
and proves local read/move/store/clear preservation. `LocalsTyped` constrains
declared slots; static source bounds independently exclude other accesses.
`SourceEvalTypePrimitives.operand_typed`, `operands_typed`, `expression_typed`
and `action_typed` compose these invariants through actual expanded-profile
primitives, including projected moves, references to constructed local values,
less-than and live-drop clears. Call typing is an explicit successful-callee
contract, not an assumed parent result or global work allowance. These proofs
retain the successful execution's complete cost unchanged.

This increment stops before recursive control/callee discharge and addressed
interpretation. Snapshot typing of a newly constructed local borrow does not
establish its storage lifetime, exclusive owner ledger or dynamic loan validity.
A clear that preserves partial typing alone does not justify dropping a value
still borrowed elsewhere. Those obligations remain required.

## Validation and next consumer

`Tests/SourceEvalTypes.lean` consumes actual evaluator/public-entry constraints
and generic primitive preservation. Independent counterexamples distinguish
u32 options from embedding options, reject out-of-range scalars and moves
through shared references, and retain legal scalar copies. A live partial tuple
move preserves the independently typed remaining table. Existing lookup/memo
source, typing, region and safety suites remain in the regression set.

Reproduce:

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceEvalTypes.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Shared `leanq` inspection of `original_boundaries`, `action_typed` and
`SlotTyped.take` exports 752 unique declaration records with no unknown
references. The statements retain actual source bodies, independent type
relations and an explicit local typed-callee contract.

Validation passes:

- Full maintained library: 3,898 jobs; new modules have no warnings.
- All 30 maintained Lean suites, the native WP example and nine Python tests.
- 706 distinct audited endpoints, including 31 new endpoints; axiom closures
  stay within `propext`, `Classical.choice`, `Quot.sound`.
- Shared statement export: 752 unique declarations and no unknown references.
- `git diff --check`; Rust/generated inputs and pins remain unchanged.

Local logs: `/var/tmp/subtree-eval-typing-final-build.log`,
`/var/tmp/subtree-eval-typing-regression.log`,
`/var/tmp/subtree-eval-typing-axioms.log`, and
`/var/tmp/subtree-eval-typing-statements.{json,log}`. The expanded actual type
certificate is also recorded in `/var/tmp/subtree-eval-typing-options.log`.

Production Rust, generated extraction data, execution semantics, source-control
parsing and toolchain pins are unchanged. The earlier full regeneration/thirteen ordered Rust tests
at `6137120` remain the source provenance baseline.

Next consume these primitive theorems in shared source-control induction and
nesting-fuel callee discharge, with explicit Box/checked-add typing and typed
initial locals. Then extend addressed partial values, caller-local loans,
owner/storage/spatial traces and parsed region interpretation. Reuse the full
functional evaluator/native correspondence and completed helper chains; do not
re-extract the body or replace these types with `Legacy.Bounded`. Continue public
maximum and separate wrappers, error policy/G3/global resources and the rest of
the planning program. No complete C3, physical allocation/free, wall-time or
production asymptotic claim follows from this milestone.
