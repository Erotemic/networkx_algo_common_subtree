# Actual recursive typing and source region binding: 2026-11-17

Baseline: `f1fe947`. Six new maintained modules connect the checked actual
nine-definition types to complete recursive source execution and retain the
actual region-bearing signatures/locals. The existing independent partial-local,
heap type/shape and region models are reused and extended. Whole-profile
snapshot type preservation and static region binding now compose with actual
JSON/native evaluator totality. Addressed partial moves, owners/storage/local
loans/destructor interpretation, public core/wrappers and global resources remain
open. This does not close W06-C3 or the full planning program.

## Successful control and recursive calls

`SourceControlSpecification.selectSource_spec` supplies a generic postcondition
rule for the existing source dispatch. `SourceEvalTypeExecution` reuses the
existing old-to-expanded operand map for Boolean scrutinees, proves state typing
through switches and early returns, and composes the preceding partial-local
primitive theorems in `exec_typed`. Both branches and the continuation retain
their checked constraints. The existing control interpreter and cost composition
are unchanged.

`SourceEvalTypeCalls.initial_typed` places independently typed arguments in the
actual partial-local initial state, using the checked return/argument prefix;
unused declared slots remain typed holes. Checked-add results are typed at
`Option<u32>` on both success and overflow. Box creation preserves its arbitrary
payload type, including shared references. Ordinary signatures are taken from
the existing type certificate rather than inferred from native outputs.

`run_typed` discharges recursive call typing by induction on nesting fuel for
all well-typed bodies and arguments. Its actual-program instance,
`original_run_typed`, covers all nine ordinary definitions and both intrinsics
at every fuel. The statement has no remaining typed-callee hypothesis, cache
soundness, word/score consistency, native-refinement assumption or global cost
allowance. It constrains successful runs; it does not assert totality of arbitrary
checked programs. A well-typed body that falls through without returning is an
explicit counterexample in the tests.

`SourceEvalTypeRefinement.original_exec_typed`, `original_result_typed` and
`original_execute_typed` expose these results for actual recursive callbacks,
whole runs and the retained JSON reader/executor. Every theorem uses the original
successful execution and its complete cost. No new interpreter or cost-erasure
simulation is introduced.

The shared deep `Borrow.Closed` relation now handles parameterized options.
`output_closed` covers every non-Box result, including the evaluator's nested
option/table tuple and checked addition. `original_represented_output_unborrowed`
uses the existing independent heap representation and `typed_unborrowed` theorem
to show that a represented ordinary result has no shared reference, even inside
owned payloads. Its heap representation is an explicit hypothesis; it does not
construct a full addressed evaluator execution or prove fresh/exclusive owners.
Polymorphic Box is excluded because it can retain a shared-reference payload.

`Evaluator.evaluate_typed`, `evaluate_total_typed` and `evaluate_source_typed`
compose this actual source type preservation with the preceding universal
functional/native theorem. All finite native queries and arbitrary warm tables,
inconsistent cached witnesses/scores, overflow and propagated failure remain in
scope, with exact returned tables and full costs. The earlier independent
consistency/memo specification keeps its original sound-cache/width hypotheses.
No functional evaluator proof is repeated or specification weakened.

## Actual region annotations and binders

The existing regional type model now supports parameterized options through
erasure, scope, renaming, substitution, attachment and retained-world value
interpretation. `LookupRegionReader.attach` accepts the scalar-option local type
instead of rejecting the expanded profile. Existing erasure equivalence and
scoped substitution lemmas continue to cover all constructors.

`SourceEvalRegionProgram` reuses shared annotation attachment and exhaustive JSON
descendant scanning. It retains the type-checked source definition, scoped
signature inputs/output, scoped local types and raw signature/body syntax for
every ordinary function. Region-bearing local erasure agrees with the actual
checked local declarations. Source definition lists, including code and local
counts, align with the existing whole-program reader.

The reader checks canonical late-bound signature region binders, body-region
bounds at every descendant (including unwind/fake-read metadata), and exact
callee region arities. Value and region arities remain distinct:

| Function | Value inputs | Signature region inputs | Retained body regions | Locals |
| --- | ---: | ---: | ---: | ---: |
| choose_longer | 2 | 0 | 3 | 6 |
| memo_insert | 4 | 3 | 33 | 15 |
| memoized_common_embedding | 3 | 2 | 247 | 113 |
| maximum_common_embedding | 2 | 2 | 15 | 7 |

The body counts are retained extraction data, also exposed by the compiled
reader diagnostic. `SourceEvalRegionCertificate.original_checked` kernel-checks
all nine actual bodies against the existing actual body map.
`original_program` exposes every retained scoped definition and its exact
signature region arity. `original_mentions_bound` reuses the shared descendant
theorem to cover every recognized region-use position in signatures and bodies.

This is binding/erasure, not dynamic lifetime validity. The old immutable-heap
borrow-route restriction is not imposed on constructed-local borrows, nor is its
safety theorem silently transferred. A well-bound shared reference inside an
option can still fail an arbitrary lifetime valuation; this false neighbor is
tested. A stronger framed interpretation of active locals, suspended callers,
owned allocations and source loans remains required.

## Consumers, validation and remaining work

`Tests/SourceEvalTypeExecution.lean` consumes recursive actual-program typing,
actual JSON/native totality and typed error results. It checks maximal-u32
overflow, deep closed outputs, the shared-reference Box exception and the
preservation/totality distinction. `Tests/SourceEvalRegions.lean` consumes actual
evaluator declarations and checks scalar-option attachment, value/region arity
confusion, nested out-of-bounds regions, zero-region primitives and the
scope/lifetime distinction. Both suites are in maintained CI.

Reproduce:

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceEvalTypeExecution.lean)
(cd proofs && lake env lean Tests/SourceEvalRegions.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Validation passes:

- Full maintained library: 3,904 jobs; no new-module warnings.
- All 32 maintained Lean suites, native WP and nine Python reifier tests.
- 734 distinct audited endpoints, including 28 new endpoints, with axiom
  closures within `propext`, `Classical.choice`, `Quot.sound`.
- Shared `leanq` inspection of `original_run_typed`, `evaluate_source_typed` and
  the actual region `original_program`: 1,046 unique exported declarations,
  with no unknown references (the CLI reports 1,047 raw records).
- `git diff --check` passes; Rust/generated inputs and pins are unchanged.

Local logs: `/var/tmp/subtree-eval-recursive-typing-build.log`,
`/var/tmp/subtree-eval-recursive-typing-regression.log`,
`/var/tmp/subtree-eval-recursive-typing-axioms.log`, and
`/var/tmp/subtree-eval-recursive-typing-statements.{json,log}`.
The kernel region certificate is recorded in
`/var/tmp/subtree-eval-regional-certificate.log`; retained binder/local counts
are printed in `/var/tmp/subtree-eval-regional-read.log`.

Production Rust, generated input, source-control parsing/execution and pins are
unchanged. Full regeneration and thirteen ordered Rust tests at `6137120` remain
the unchanged source-provenance baseline. The accepted axiom baseline remains
`propext`, `Classical.choice`, `Quot.sound`; no native proof oracle is used.

Next reuse these complete source/type/region certificates and the existing
helper safety chains to interpret addressed partial tuples and owned-field
moves, caller-owned-local borrows, owner/storage/spatial traces and live
destruction (including destructor-instance typing/semantics). Snapshot typing
and parsed scope do not justify freeing a value still borrowed elsewhere. Then
compose public maximum, separate indexed/token/reconstruction wrappers,
input/error policy/G3 and full resource contracts. The remaining W04/W05,
MEM-04, application/research/software/release obligations are retained.
