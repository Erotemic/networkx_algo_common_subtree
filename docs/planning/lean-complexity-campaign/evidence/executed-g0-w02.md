# Executed reconnaissance and actual lookup inventory

Baseline: `0cdd643` (2026-11-14). This follow-up includes the later software,
uniform-family mathematics, production integer-helper proof and optional arlib
experiment. It supersedes neither the delivered survey nor its historical
checksums. **G0 is partially executed; G1 and SRC-01 are not complete.** Main
Lean/Mathlib/Aeneas pins and production algorithms remain unchanged by this audit.

## Declaration/build decisions

Exact revisions, file hashes, types and commands are in
[executed-g0-w02.json](executed-g0-w02.json). The selected source files were read;
no whole-project axiom audit was run.

| Capability | Actual declaration / premises | Executed evidence / disposition |
| --- | --- | --- |
| Opcode/value realization | arlib `ExactRealizes`: separate `correct` representation postcondition and `cost_eq` tally equality, universally under `Pre`; `bind` composes them through an explicit intermediate relation; `steps_eq` transfers every `CostModel` | Pinned module and `Realization.Scan` compile under the project toolchain. Direct reuse candidate; do not recreate this certificate. `Pre` must have admissible states for a nonvacuous application. |
| A complete RAM scan | arlib `ScanRealization.realizes`: represented buffer, key representation, fuel equal to length and word-width premise; preserved input, correct membership and `3+5*fuel` unit RAM bound | Compiles. Reusable scan/representation proof patterns, **not** the structural memo lookup: its keys are scalar words, with no witness copy. |
| Nondeterministic timed composition | Lax62 `NRest`, `returnT`, `spec`, `consume`, `bindT`; `Pw.bindT_assoc` at `ℕ∞`, and `bindT_assoc_acost` for currencies | Unmodified `ACost`, `NREST.Basic` and `NREST.Pw` compile against Lean/Mathlib 4.35. Upstream declares 4.33 and a different Mathlib pin. This is a narrow current-toolchain compatibility check, not an upstream-pin/full-codegen build. |
| Timed/data refinement to IR | Lax62 `Cash.spec_of_hnRefine`, `exists_bigStepB_of_hnRefine`, `computesInTime_of_spec` | Source inspected, not compiled here. Requires representation, IR execution/bounds and harness hypotheses; neither applies automatically to Aeneas definitions. EndToEnd explicitly leaves its example-twin/independent-spec proofs open. Keep as competing pilot. |
| Existing WP engine | Lean 4.35 `Std.WP.EStateM.wpInst`, `EStateM.of_run_eq_wp` | [StdWPWorksheet](../../../../proofs/experiments/resource_cost_audit/StdWPWorksheet.lean) compiles using actual memo types and `findResult`. `open Std.WP` enables the assertion instances. The worksheet expresses a result/counter contract; it does not make the counter adequate. Reuse the WP engine. |
| Deep machine execution/cost | order-maintenance `OM.Machine.exec`, `Examples.sumProg_spec`; `flatten_sim` | Original pinned 4.35 environment shares exact Mathlib/dependency commits with this project. Machine examples build. `exec` counts selected syntax operations; `flatten_sim` states a factor-five cost inequality under representation, non-error, peak and free-memory premises. Flat source inspected; its build was deliberately interrupted because it imports application `Impl.PeakWord`, then the narrow examples target passed. No flat/whole-application build claimed. |
| Annotation interchange | CSLib `TimeM`, `time_bind`, `ret_bind` at the exact source linked from current API docs | Source/API inspected, not built. The API explicitly leaves annotation/execution adequacy external. Reuse candidate for representation, not a source-cost certificate. |
| Certifying extraction precedent | Forster/Kunze `computableTime.extTCorrect : computesTime ...`; arrow case requires bounded `redLe` plus the logical relation for every encoded input | Pinned source inspected; MIT; static Coq 8.8.2 artifact, not built (no Coq executable). Its extraction/reduction relation is useful design precedent, not a Lean/Rust adapter. |

Both arlib realization modules are imported by `Arlib.Computation`; the inspected
Lax modules are imported by `Lax62Proofs`; `OM` imports machine examples and
`FlatRun`. No absence claim follows from the limited public search. A Lean issue
about older `vcgen` import boundaries was found; the installed 4.35 declarations,
not that older issue, determine this worksheet. Public search did not establish
that any candidate already covers this repository's Rust-to-events boundary.

## W02: the same actual source for every candidate

Source: `verified_ordered_core/src/lib.rs`, `words_equal`, `copy_word`,
`copy_result`, `memo_lookup`; pinned generated `VerifiedOrderedCore.lean`.
Independent result contract: `Rust.MemoizedOrderedSolver.findResult`, selecting
the **first** structurally equal key, including arbitrary duplicate keys.
`memo_lookup_correct` already proves actual extracted value/termination
correspondence. `TableSound` is unnecessary for first-hit lookup; it is necessary
when deriving that a cached witness has the independently optimal meaning.

| Source work | Event occurrence / required contract |
| --- | --- |
| Each table match, including final `Empty` on a miss | One lookup-node packet: discriminant/read/branch/call-return bookkeeping. The packet's primitive implementation and price must be justified, not silently free. |
| `words_equal(left, entry.left)` | Recursive comparison-node packets; both constructors are inspected, Pair heads compare first and tails only after a head hit. A whole structural equality is not one RAM instruction. |
| Right key comparison | Executed only after left equality. Preserve the two short-circuit levels; the earlier single pair-key comparison count is only a coarse request count. |
| Lookup hit | `copy_result` reads the score and traverses/copies the complete result word. Rust allocates two Boxes per Pair. Returning the stored witness by semantic value does not account for its copy. |
| Lookup miss continuation | Only the remaining table is scanned. No suffix work after a hit. |
| Insertion / surrounding evaluator | Three structural copies, entry/rest Boxes, candidate concatenations and recursive evaluator requests are additional work; lookup adequacy alone excludes them. |

Let `t` be initial table length, `L,R` query Pair counts, `h` indicate a hit,
and `W` its returned word Pair count (zero on a miss). A precise proposed
**call/constructor-packet** envelope is

```
lookup nodes       <= t + 1
word compare nodes <= t * ((2*L + 1) + (2*R + 1))
copy-word nodes     = h * (2*W + 1)
copy allocations    = h * 2*W
```

These are proposed source-event obligations, **not newly proved resource
theorems**. Query-size comparison bounds use short-circuit structural traversal;
they do not require stored keys to be small. Copy size cannot be omitted: an
arbitrary unsound table can hold an arbitrarily large witness. Under `TableSound`
the existing independent common-embedding bound can constrain `W`. Prices for
field access, scalar copy, branching, call/return and allocation must either be
inside justified packets or separately charged. This is a declared source
operation model, not a hardware time or allocator bound. Finite recursive inputs
are the extraction domain; heap/stack exhaustion is not modeled by the existing
functional theorem. No new numerical-size premise is required merely for lookup.

Mandatory cases for G1: empty table, miss, first/last hit, duplicate first hit,
left-key mismatch avoiding an expensive right key, equal long keys, early head
mismatch avoiding tails, and a large returned witness. The actual lookup/word
scans are recursive traversals; do not replace them with an unrelated toy loop.

## Omitted-work experiment and the source boundary

The optional arlib module now proves `extra_scan_cost` and
`extra_scan_exceeds_singleton_budget`. Repeating its scan preserves the result,
doubles exact key-comparison cost, and already exceeds the original singleton
one-comparison budget. These are compiled counterexamples **inside the charged
model**, not a Rust-mutation/source-adequacy certificate.

The pinned Aeneas CLI was also tested on the actual ordered-core LLBC with
`-backend lean -use-fuel`. It exits 1 with `The Lean backend doesn't support the
-use-fuel option`; `src/Main.ml` contains that explicit check. No generated file
or production source was changed. Do not infer a total-work bound from generic
recursion fuel even on backends that support it: sequential work needs additive
accounting, not merely a recursion-depth budget.

The existing arlib lookup remains a charged first-hit twin over the mathematical
table. The Std worksheet remains a contract-expression check. Neither establishes
that actual Rust structural comparisons, copies and control flow emit all
charged events. All candidates therefore still need the **same** event/source
adequacy obligation. G1's stop condition applies: do not expand a generic memo
library on top of value equality alone. Next is a bounded source-to-events pilot
for these four actual functions, with an extra source scan forcing a changed
adequacy/bound obligation. No backend has been selected on proof-script size.
