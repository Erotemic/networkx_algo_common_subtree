# Stable fuel and readback budgets for actual recursive execution

Baseline: `a56e701` on `Droschinsky-algos`. Four proof modules add 19 checked
public theorems. Increasing source-call fuel and ghost readback budgets preserves
every completed actual recursive run's exact world, returned packet and full
cost. Independently typed readable helper inputs now give one fixed pair of
sufficient bounds and one stable output for every larger pair of bounds.
Universal physical success for interpreted choice/evaluator/maximum remains
open, as do W06-C3/SRC-01 and the full planning goal.

## Exact declarations and proof composition

`SourceHeapFuel.lean` defines `LookupSource.Heap.CallsExtend` as pointwise
extension of completed actual helper runs. `Heap.{action_extends,
selectBranch_extends,exec_extends}` preserve exact locals/cells, appended memory
and complete costs through existing old helper actions and selected control.
`Heap.run_fuel_enlarge` and `MemoSource.Heap.run_fuel_enlarge` establish fuel
extension for arbitrary bodies in both unchanged actual helper interpreters.
These laws require neither native shapes nor a source-answer, safety or owner
premise; they assume only the smaller actual run succeeded.

`SourceHelperFuel.lean` lifts this through existing `Helpers.finish` and all
eight helper/intrinsic dispatch cases with `finish_extends` and
`execute_fuel_enlarge`. Box and checked-add retain their actual argument shapes
and scalar-width checks. Together with the preceding readback-budget law, this
proves `typed_stable_bounds`:

```text
independent typed readable actual helper arguments, well-formed initial world
  => exists minimumFuel minimumBudget final packet cost,
       every fuel >= minimumFuel and budget >= minimumBudget
       returns exactly (final, packet, cost).
```

The helper selector remains `Recursive.interpreted function = false`. It covers
six ordinary helpers and two intrinsics, excluding interpreted choice/evaluator/
maximum. No expected result, successful execution or supplied native height is
an input to the existence theorem. The preceding helper totality result supplies
the first run; exact fuel/readback extension makes both thresholds uniform.

`typed_owned_stable_bounds` additionally retains final readable output, world
validity, protected caller bytes, a complete output footprint, the complete
unique/classified/live output/actual-caller/external owner frame and coverage of
every live Box. Every larger pair of bounds has that identical final world and
packet, and the matching pinned source run with the same full cost. Valid actual
callers, initially live protected addresses and initial complete input/global
owner resources remain explicit. Shared read aliases remain permitted.

`SourceCallingExtension.lean` defines `Derived.CallsExtend` over the existing
actual callee signature. `Derived.call_extends` preserves one-pass argument
extraction, the actual post-argument suspended caller, callee result and guarded
result store. `Calling.{instruction_extends,exec_extends,invoke_extends,
guardedInvoke_extends}` retain selected control, certified reference views,
actual parsed entry and checked return cleanup. They reuse the shared control
executor's extension theorem rather than introducing another interpreter.

`SourceRecursiveBudget.lean` proves `Recursive.{run_budget_enlarge,
original_budget_enlarge,run_fuel_enlarge,original_fuel_enlarge,original_enlarge}`.
Fuel induction composes all actual helper cases and interpreted recursive calls.
The two `run_*` laws support arbitrary parsed programs; no program alignment,
independent input types, native height, readiness or ownership premise is needed
to retain an already successful run. `original_enlarge` jointly enlarges both
bounds for the actual pinned program, preserving the entire returned triple.
It does not manufacture an interpreted run from missing physical permissions.

Neither nesting fuel nor ghost readback depth is production work. The complete
source cost is unchanged by increasing either. Rust, generated Charon/Aeneas
files, interpreters, mathematical/source specifications, hypotheses, costs and
pins are unchanged.

## Consumers and validation

`Tests/SourceHelperCalls.lean` upgrades its independently typed insertion consumer
to fixed joint thresholds, with query/result references aliasing its owned table.
`Tests/SourceRecursiveCalls.lean` proves that the actual completed parsed choice
run at fuel one and readback zero is identical at every larger pair of bounds.
That run includes losing Box destruction, checked callee root closure and a
suspended caller with a transitive aliased scalar/reference graph.

The 3,996-job root build and both affected consumer suites pass. All four new
modules compile without warnings. The 1,289-endpoint audit includes all 19 new
theorems and retains only `propext`, `Classical.choice` and `Quot.sound`. Eight
selected `leanq` statement seeds cover 1,070 unique declarations with zero unknown
references. This is selected statement coverage, not a whole-library export.
All seven build-cache mounts remain guest-local ext4.

No fresh whole-suite/native-WP/Python/Rust or runtime execution run is claimed.
The immediately preceding eight-case runtime/helper/typed/recursive checks remain
evidence at `a56e701`; the full 47-suite/native-WP/nine-Python run remains evidence
at `d49f638`, and the thirteen ordered Rust tests at `823df34`.

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceHelperCalls.lean)
(cd proofs && lake env lean Tests/SourceRecursiveCalls.lean)
(cd proofs && lake env lean BaselineAudit.lean)
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-recursive-budget-statements.json \
  SubtreeProofs.Rust.LookupSource.Heap.run_fuel_enlarge \
  SubtreeProofs.Rust.MemoSource.Heap.run_fuel_enlarge \
  SubtreeProofs.Rust.SourceEval.Addressed.Helpers.typed_owned_stable_bounds \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.exec_extends \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.guardedInvoke_extends \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.run_budget_enlarge \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.run_fuel_enlarge \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_enlarge
```

Machine-local logs: `/var/tmp/subtree-recursive-budget-{root-build,helper-tests,
recursive-tests,axioms,statements}.log` and
`/var/tmp/subtree-recursive-budget-statements.json`.

## Remaining forward proof

Apply uniform helper totality and exact recursive extension in a forward
physical-success proof for legal native inputs/warm tables. Derive actual
storage/move/write/drop/return/close permissions from complete owner resources,
computed loans and certified reference views, without assuming a desired parent
execution. Combine finitely many local sufficient bounds using extension.
Interpret dynamic parsed-region binders/destructor instances under the explicit
source-operation boundary. Complete native public maximum/cold-table teardown,
wrappers/input policy, global resources/G3 and the other planning obligations.
The extension laws and finite regression cases do not replace these requirements.
