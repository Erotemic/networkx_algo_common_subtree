# Universal actual evaluator/native agreement: 2026-11-17

Baseline: `04ddb6b`. Nine maintained modules establish complete functional
correspondence for the actual memo evaluator, with exact path-cost composition.
All finite native words and warm tables are supported, including arbitrary
cached witnesses and scores, overflow, every early error return and the exact
returned table. Source/native functional correspondence is now complete for this
core function. Whole-profile typing/regions/owners/storage, local borrows and
addressed destruction, public maximum/wrappers and global resource claims remain
open. This does not close W06-C3 or the full planning program.

## Shared control and fuel

`SourceControlExtension` proves successful-execution extension for the shared
`Control.execWith`, polymorphically in state, outcome, work and handlers. The
expanded-profile `SourceEvalDeterminism` reuses it for statement/control/call
extension. `run_extends` preserves the same result and entire cost at larger
nesting fuel for every body and argument list, including malformed intrinsic
arguments. `run_unique` proves successful values/costs independent of chosen
fuel. There is no copied control interpreter or assumed final work allowance.

## Every actual path

`SourceEvalFailures`, `SourceEvalContractFailures` and `SourceEvalSuccess` prove
all recursive paths against the complete body already identified with the
actual 113-local source. `SourceEvalPathCost` packages local syntax/destruction
and the *complete* costs of precisely the executed callees. It introduces no
new evaluator or global cap. Existing seven helper and scalar proofs are reused.

Let `H`, `T` and `M` be destructor work of the heads witness, tails witness and
new matched candidate; `Q_L`, `Q_R` that of the two contracted-query words; and
`D_L` that of the returned left-deletion witness. Constants in the last column
mean visits with zero Boxes. These are local costs, excluding callee costs and
the evaluator-entry charge:

| Path | Syntax steps | Local destruction |
| --- | --- | --- |
| Heads recursive result `None` | 156 | 3 |
| Tails recursive result `None` | 208 | `H + 5` |
| Subtotal checked-add overflow | 238 | `H + T + 5` |
| Matched-root checked-add overflow | 260 | `H + T + 5` |
| Left-deletion recursive result `None` | 373 | `M + Q_L + 11` |
| Right-deletion recursive result `None` | 449 | `M + Q_L + Q_R + D_L + 13` |
| Successful final choice/insertion | 525 | `Q_L + Q_R + 13` |

`pathCost` adds syntax steps and local destructor visits to all executed callee
work steps, retaining their complete events, destruction and evaluator-call
currencies. The evaluator entry adds one step and one solver call. The
`destroyed` fields are diagnostic components already included in work steps;
they are not a second bill to add to `work.steps`.

Failure after constructing the matched candidate charges its two fresh Boxes
and contained witness structure even though the native value result is `None`.
The successful path moves candidates into the actual two choice calls and
retains their established losing-value costs. Returned tables are never replaced
with a cold/empty approximation on any failure path.

## Source/native recursive composition

`Evaluation` pairs an actual expanded-profile run, with its complete cost, and
successful translated-native execution returning the same native result/table.
`SourceEvalFailureRefinement` and `SourceEvalSuccessRefinement` discharge lookup,
concatenation, Box, both checked adds, choice and insertion from their existing
actual-program contracts. Recursive premises refer to completed *smaller* query
calls with their actual output tables and costs. They do not assume the parent
result or a global runtime bound.

`SourceEvalTotal.evaluate_total` discharges every recursive premise by
well-founded induction on the sum of the independent Dyck semilengths of the
query words. Heads, tails and either contracted query strictly decrease this
measure, independently of cache contents. Successful child fuels and the local
helper depth requirements are combined using fuel extension. Fuel is a call-
nesting bound and is not counted as execution work.

`evaluate_source` binds totality to the actual retained JSON reader.
`evaluate_refines` covers every completed source run at any fuel, not just the
chosen witness fuel. `evaluate_stable` fixes one result/table/complete cost for
all sufficiently large fuels; `Evaluation.unique` supplies uniqueness.

No cache-soundness, score/word consistency or small-cache-witness premise is
needed for totality, error policy or source/native agreement. Overflow remains
a successful program result `None` with its exact table; it is distinct from
source-model execution failure due to insufficient fuel or invalid operations.

`evaluate_consistent` separately consumes the existing native
`memoized_common_embedding_refines` theorem under its original sound-cache and
input-width hypotheses. It retains the independently specified witness/score,
sound output table and exact numeric memo-table correspondence with `memoLcs`.
No recurrence or optimality specification is replaced with source execution.

## Verification and remaining work

`Tests/SourceEvalRecursion.lean` constructs genuine source/native runs for both
checked-add overflow exits with maximal inconsistent cached scores, unchanged
warm tables, thirteen destructor visits and three solver calls. It propagates
one of those failures through another recursive level using fuel extension,
retaining the exact table with sixteen visits and four calls. Universal
consumers cover all finite native inputs/tables, stable full costs, and the
existing independent consistency/memo specification under its stated hypotheses.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceEvalRecursion.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Validation passes:

- Full maintained library: 3,890 jobs; all new modules have no warnings.
- All 29 Lean suites, native WP example and nine Python reifier tests.
- 675 distinct audited endpoints, including thirty new endpoints, with axiom
  closures within `propext`, `Classical.choice`, `Quot.sound`.
- Shared `leanq` statement inspection of `evaluate_total`, `evaluate_refines`
  and `evaluate_consistent`: 837 unique declaration records in the exported
  payload, with complete actual source/native/cost statements and the original
  specification hypotheses only where required.
- `git diff --check` passes. Production Rust, generated data, source-control/
  frontend implementations and pins are unchanged.

Local logs: `/var/tmp/subtree-eval-recursion-{full-build,regression,axioms}.log`,
`/var/tmp/subtree-eval-total.log`, `/var/tmp/subtree-eval-success.log`,
`/var/tmp/subtree-eval-contract-failures.log` and
`/var/tmp/subtree-eval-recursion-statements.{json,txt}`. The preceding `6137120`
full pinned regeneration and thirteen ordered Rust tests remain the unchanged
source-provenance/behavior baseline. The resume handoff now indexes the earlier
reports rather than repeating their full milestone history.

This is functional correspondence and exact local/callee cost composition in
the declared snapshot/partial-local source-operation model. It does not price
execution of the Lean interpreter, prove physical drop glue/compiler/allocator
behavior, establish peak residency or discharge whole-evaluator typed addressed
safety. Complete the actual local type/region/storage/owner/loan/destruction
traces, compose the public maximum entry point and separate wrappers, then the
remaining representation/global resource and G3 obligations. D12's scoped
source-operation route remains in force; no whole-compiler gate is invented.
W04, MEM-03/04, SRC-01/C3 and application resource targets remain open.
