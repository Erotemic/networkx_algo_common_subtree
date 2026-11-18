# Certified ending of unused shared-reference views

Baseline: `57deada` on `Droschinsky-algos`. W06-C3/SRC-01 and the full planning
objective remain open. Production Rust, generated artifacts, independent source
and native semantics, hypotheses and toolchain pins are unchanged.

## Resource view and exact source equivalence

The preceding [recursive-calls report](memo-evaluator-recursive-calls.md)
exposed an actual cache-hit failure: evaluator local 6 retained a shared table
reference after its final use, so moving the table from local 3 was blocked.
Its storage-dead marker occurs later. Stored pointer bits and an active shared
reference view need separate lifetimes.

`SourceEvalLoanObservations.lean` proves agreement of reads, operands, expressions,
actions and scrutinees when their actual places avoid one local. A write/reset
synchronizes that local. Drops count as observations because their complete
source destructor cost depends on its initialization mask. Fake reads are
conservatively treated as observations too.

`SourceEvalLoanEndings.lean`, namespace `SourceEval.LoanEnding`, defines
`endsBeforeObservation slot code`. It requires the local to be reset before any
observation, or a return that observes only local zero. A bare `done` fails the
predicate because its complete next-state is observable. Switches require both
branches to end the view; the analysis conservatively ignores the outer join.
Reads through fields/dereferences still observe their root local. Parsed region
binder IDs are never interpreted as statement times.

Public endpoints:

- `exec_congr`: two source states agreeing outside such a local have exactly
  equal complete source execution outcomes and costs, for arbitrary callees.
- `forget_source`: the finite batch update has that same exact equivalence.
- `forget_boxes`: each local's owned Box count is unchanged.
- `forget_observed`: every local failing the ending predicate retains its exact
  initialization mask.
- `forget_nil`, `forget_cons`: equations for the actual finite batch update.

Only a top-level `shared` mask may be cleared. Owning masks and all other value
forms remain. The result is an active resource view, not a claim that the stored
pointer cell was physically overwritten or its storage retired. The independent
original source state is retained by the complete equivalence theorem rather
than being replaced by a modified source semantics.

## Validity, aliases and control integration

`SourceActivationLoanViews.lean` exports `Frame.forget_shared`, `Frame.forget`
and `Activation.forgetRefs_{valid,source,identity,boxes,observed}`. The prepared
view remains valid in the same world, with the same frame, local count and root
bindings. It changes no memory, classes or storage liveness. Other references
retain their full transitive read/loan graphs, including aliases through the
stored pointer cell of an ended view. Existing move, write, destructor, storage
retirement and return-escape guards remain strict.

`Calling.schedule` annotates each actual action with its remaining source code;
`loanInstruction` prepares the certified view and invokes the existing
instruction primitive. The existing `Control.execWith` still handles switches,
joins and early returns. `Calling.exec_spec` composes the equivalence with each
existing instruction theorem, preserving its original complete source/cost
conclusion. `Calling.exec_preserves` similarly retains actual suspended caller
bytes/classes/liveness. Recursive callee/readiness/native refinement conclusions
remain checked with their existing explicit conditions.

`Prepared` forces the finite scan to finish before installing its function-valued
state. Returning a function directly lets Lean's compiler eta-expand the scan
and repeat all prior scans on every later local read, causing exponential runtime
in the executable ghost model. The compiled `prepare` takes three arguments and
is called before the state field is installed. This representation choice adds
no production source events; the existing C2 source-operation boundary remains.

## Consumers

`Tests/SourceLoanEndings.lean` checks a complete guarded Box move, return and
actual storage-dead cleanup with the old pointer cell initially still live.
It consumes `Calling.exec_spec` to recover the original full source result/cost
and final validity. Direct low-level movement remains rejected while its loan
is present. Later direct use, later destructor observation, an owning reset and
a still-used indirect alias retain their guards and reject the conflicting run.
The alias case keeps the complete transitive `[3, 0, 1]` loan list even after
local 6's own view ends. The existing numeric call/readiness consumer is adapted
to the certified prepared activation without changing its result or costs.

The expanded `Tests/SourceRecursiveExecution.lean` also runs the original
one-pair/one-pair cold query through both actual parsed evaluator and maximum.
The evaluator returns score 1 at fuel 16 / budget 128 with 2,615 source steps
and five solver calls. Maximum returns the same native witness at fuel 17 with
2,704 steps and five solver calls. These executions now succeed. The test
compares the complete returned source values (including the evaluator table)
and every cost field, not only those observations. All six original caller
cells remain byte-for-byte unchanged and live. Every new live address belongs
to the returned output's owner list, so no callee stack root or discarded table
owner remains live. This is executable evidence, separate from the universal
kernel-checked conditional refinement theorems.

## Remaining scope

This is a conservative certificate for ending unused shared-reference resource
views. It does not establish universal native input readiness, sufficient fuel/
readback budgets, successful physical checks on every actual path, global
exclusive ownership/transfer, complete dynamic region interpretation or full
Rust destructor/unwind adequacy. Public maximum/cold-table teardown, wrappers
and input policy, global time/space, G3 and the other planning work remain.
No source-operation theorem is promoted to production wall time or physical
allocator behavior. C3 and the full planning objective stay open.

## Validation and reproduction

The root build passes 3,959 jobs. All 44 maintained Lean suites, native WP,
nine Python source-reifier tests and thirteen ordered Rust tests pass. The
expanded audit checks 1,082 distinct endpoints, including all 27 new public
theorems, with only `propext`, `Classical.choice` and `Quot.sound`. Shared
`leanq` statement inspection exports 1,243 unique declarations from eight seeds,
with no unknown references. Inspected signatures retain the universal complete
source equivalence and the explicit readiness/success conditions of recursive
native refinement. Build warnings are existing library warnings; the three new
modules and focused test suite are warning-free. VM cache status confirms every
listed Lean/Rust cache is bind-mounted over guest ext4; Cargo uses the mounted
standalone ordered crate target and has no target-dir override.

Reproduce from the repository root:

```bash
dev/setup-build-caches.sh
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceLoanEndings.lean)
(cd proofs && lake env lean Tests/SourceCallingProgram.lean)
(cd proofs && lake env lean Tests/SourceRecursiveExecution.lean)
(cd proofs && lake env lean BaselineAudit.lean)
# Run every maintained Lean suite in .github/workflows/verification.yml.
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
python3 proofs/checks/test_lookup_source_reifier.py
cargo test --locked --manifest-path rust/crates/verified_ordered_core/Cargo.toml
leanq --project proofs statement --root-module SubtreeProofs \
  --out /var/tmp/subtree-loan-statements.json \
  SubtreeProofs.Rust.SourceEval.LoanEnding.exec_congr \
  SubtreeProofs.Rust.SourceEval.LoanEnding.forget_source \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.Activation.forgetRefs_valid \
  SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage.Activation.forgetRefs_boxes \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.exec_spec \
  SubtreeProofs.Rust.SourceEval.Addressed.Calling.exec_preserves \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_respects \
  SubtreeProofs.Rust.SourceEval.Addressed.Recursive.original_evaluate_refines
```

Machine-local logs are `/var/tmp/subtree-loan-{full-build,regression,axioms,rust}.log`
and `/var/tmp/subtree-loan-statements.json`. An additional temporary diagnostic
reuses `Control.execWith`, `Calling.schedule` and existing instruction primitives;
it is not a maintained interpreter or parser. The maintained runtime regression
is the reproduction of the repaired nonempty behavior.
