# Derived typed call domains and recursive source refinement

Baseline: `823df34` on `Droschinsky-algos`. This increment removes the separate
native path-readiness premise from recursive evaluator refinement. Successful
physical execution remains a premise. W06-C3/SRC-01 and the full planning goal
remain open. Production Rust, generated code, existing interpreters, independent
source/native semantics, mathematical hypotheses and pins are unchanged.

## Successful helper reflection

The preceding helper contract used native argument shapes and sufficient depth
bounds to obtain a source execution, then matched it to the concrete helper.
Those bounds are sufficient for success, but are not necessary for correspondence
of an already successful run. For example, comparison can return on a constructor
mismatch before inspecting a deeper word.

`LookupHeapReflectionPrimitives.lean` proves the reverse primitive direction from
the existing exact `Heap.EnvRep`: `option_source`, `EnvRep.source`,
`locate_reflect`, `borrow_reflect`, `operand_reflect`, `operands_reflect`,
`rvalue_reflect` and `scrutinee_reflect`. Successful concrete execution constructs
a source value/state and their representation. Pointer locations reuse the old
forward theorem. No desired source value, native height or parent answer is an
input hypothesis.

`LookupHeapReflection.lean` defines the local `Heap.CallsReflect` contract and
proves `action_reflect` and `exec_reflect`. Source outcomes/costs match exactly;
old memory is retained. Conditional drops still require empty locals. Branch
selection, joins and early returns use the existing interpreters.

`SourceHeapDriverReflection.lean` proves `ReflectingDriver.reflect` by fuel
induction from the actual concrete zero case and concrete/source successor
equations. `Heap.run_reflect` and `MemoSource.Heap.run_reflect` instantiate it
on the existing lookup and memo drivers. The record adds no interpreter.
Both directions now use the actual body, arguments and same call-nesting fuel.

`SourceEvalHelperReflection.lean` exports:

- `Helpers.lookup_reflect`, `memo_reflect`: construct the old source execution
  from successful concrete helper execution, then reuse the completed mixed-
  world source/readback/retention contracts.
- `readable_number_source`, `boxNew_ready`, `checkedAdd_ready`: derive the
  intrinsic shapes/widths/positive-fuel conditions from actual readable packets
  and successful intrinsic execution.
- `callee_bounded_respects`: all six ordinary helpers and both intrinsics
  satisfy the complete existing `CallsRespect` source/cost/readable-output/
  well-formed-world/protected-byte contract from scalar-width-bounded input
  snapshots and successful execution. Native helper height bounds are absent.

The scalar-width premise remains essential. Older helper numbers range over
naturals, whereas expanded source scalar copies require `u32` width. Reflection
into the old source is not permission to ignore this embedding boundary.

## Deriving call input conditions from independent types

`SourceEvalTypeBounds.lean` proves `Heap.SnapshotTyped.bounded` and
`SnapshotFieldsTyped.bounded`. The actual independent type system therefore
supplies the old-to-expanded numeric domain. `Partial.LocalsTyped.forget` and
`Storage.Activation.forgetRefs_typed` preserve those same declared partial-local
types when a certified unused shared-reference view ends. Holes retain their
declared type; this typing fact does not replace owner or loan validity.

`SourceEvalTypedCalling.lean` defines `Derived.TypedReady` using only the actual
argument snapshot types and `Types.callOutput`. It contains no source execution,
expected result, fuel bound, desired post-state or parent answer.

Public endpoints:

- `Calling.readyAt_typed`: independent action constraints, the actual activation
  and actual operand execution derive that call's input domain.
- `readyFor_typed`: compose through actual instruction successes, selected
  control, joins and early returns. Use the existing local callee contract and
  independent source callee typing; retain physical frame/caller/world validity.
- `exec_typed_spec`: obtain the complete old source/cost/frame/caller/packet
  conclusion plus the independently typed outcome, without a supplied path-
  readiness premise.
- `fields_typed_length`, `invoke_typed_ready`: actual typed input arity and the
  parsed declaration's own local types, boundary and constraints construct entry
  readiness. The actual parsed declaration/count is retained.

The proof uses the already checked recursive source typing theorem for local
callee outputs. That theorem is independent of addressed success and native
correctness. It is not an assumed parent result. The existing `Calling.exec`,
primitive guards, `ReadyFor`, source specifications and costs are unchanged.

## Stronger recursive and native consumers

`SourceEvalTypedRecursive.lean` exports `Helpers.callee_typed_respects`, then
`Recursive.run_typed_respects` by fuel induction. Helper calls use reflection and
argument typing. Interpreted choice/evaluator/maximum calls use the actual parsed
declaration's type fields, derived entry readiness and existing guarded entry/
cleanup/caller-preservation theorems. The real post-argument suspended stack is
passed throughout.

`Recursive.original_typed_respects` specializes to the pinned actual program.
`original_typed_spec` retains the complete source result/cost, typed and readable
output, final world validity and protected caller bytes from typed readable
inputs and concrete success. No `Recursive.Ready` is supplied.

`original_evaluate_typed_refines` is the stronger native evaluator endpoint:

```text
well-formed world + valid callers + readable native query/table packets
+ alive protected addresses + successful actual recursive execution
  => exact existing native result/table and Evaluation/full-cost relation
     + readable output + well-formed final world + protected caller bytes
```

Native word/table typing discharges the entire input domain. Arbitrary warm
tables and overflow/failure outputs retain the existing native specifications;
optimality still needs the original sound-cache hypotheses. The earlier native
height-based `Recursive.Ready` and theorem remain reusable sufficient APIs, but
are not premises of the stronger endpoint. They are not asserted to be necessary
conditions of successful execution.

## Consumers and adversaries

`Tests/SourceTypedCalls.lean` compares a depth-three left word with an empty
right word. Its whole-left height bound fails at fuel one, but constructor
mismatch makes the actual concrete helper succeed. The test consumes the new
contract to retain the complete source cost, output typing/readability and all
protected input cells. Zero call fuel and zero ghost readback budget still fail.

A separate input stores score `2^32` in the older helper model. Concrete result
copy succeeds there, while the expanded source's actual score-copy operand
fails and independent `u32` snapshot typing rejects that number. The width
premise has not been removed or hidden.

A typed checked-add/control client produces 42 at thirteen source steps and
consumes `exec_typed_spec` without manually supplying readiness. It checks the
selected optional arm and skips undefined-behavior arms/join. The maintained
`Tests/SourceRecursiveCalls.lean` arbitrary-query/warm-table consumer is upgraded:
it no longer accepts a `Recursive.Ready` hypothesis and retains the native result,
exact `Evaluation` cost relation and protected bytes. Existing choice and strict
primitive-loan consumers remain. The complete cold empty/nonempty evaluator and
maximum executable regressions remain unchanged.

## Remaining scope

Selected call input conditions for the stronger conditional recursive/native
refinement now derive from independent types. Successful physical execution is
still explicit: prove adequate call/readback budgets and every guard, storage,
return and cleanup check on legal native executions. This needs global exclusive
Box ownership/transfer alongside shared reads and temporary packets, plus full
actual loan/region/destructor composition. Input typing and readable graphs alone
do not establish those properties. Shared query aliases and permitted insertion
aliases must remain allowed; global disjointness of all reads is not a substitute.

Public maximum/cold-table teardown proofs, wrappers/input policy, global time/
space, G3 and the other LV/Droschinsky/software/release/application targets remain.
The D12 source-operation boundary and explicit compiler/runtime/physical allocator
boundaries are unchanged. No source-operation count is promoted to production
time or physical allocator space. W06-C3 and the full planning objective stay open.

## Validation and reproduction

The root build passes 3,966 jobs. All 45 maintained Lean suites, native WP and
nine Python reifier tests pass. The focused suite was also rerun after adding
the width adversary. All seven new modules and that suite compile warning-free.
The 1,115-endpoint audit includes every one of the 33 new public theorems and
retains only `propext`, `Classical.choice` and `Quot.sound`. Shared `leanq`
statement inspection exports 1,139 unique declarations from the eight seeds
below, with no unknown references. This is the selected statement closure, not
a count of all library declarations. The inspected native signature contains
concrete success and no `Recursive.Ready` premise. VM cache setup/status confirms
all listed Lean/Rust caches remain bind-mounted over guest ext4.

Rust sources/generated artifacts did not change; the thirteen ordered Rust tests
passed at baseline `823df34`. This proof increment does not claim a new Rust run.

Reproduce from the repository root:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceTypedCalls.lean)
(cd proofs && lake env lean Tests/SourceRecursiveCalls.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
# Run every maintained Lean suite in .github/workflows/verification.yml.
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
python3 proofs/checks/test_lookup_source_reifier.py
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-reflection-statements.json \
  SubtreeProofs.Rust.LookupSource.Heap.run_reflect \
  SubtreeProofs.Rust.MemoSource.Heap.run_reflect \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.callee_bounded_respects \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.readyFor_typed \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.invoke_typed_ready \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.run_typed_respects \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_typed_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_evaluate_typed_refines
```

Machine-local evidence uses `/var/tmp/subtree-reflection-{full-build,regression,
axioms,tests,recursive-tests}.log` and
`/var/tmp/subtree-reflection-statements.json`.
