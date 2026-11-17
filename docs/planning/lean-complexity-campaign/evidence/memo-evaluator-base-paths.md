# Actual evaluator body and universal base paths: 2026-11-17

Baseline: `5dc7c6f`. Four `SourceEval{Body,BodyCertificate,Base,BaseRefinement}`
modules make the entire evaluator control reviewable and establish universal
native agreement for cache hits and empty-query executions. This supplies the
base cases for full evaluator composition; recursive pair/pair success, overflow
and propagated failure paths, their full resources and addressed safety remain
open. No planning gate is closed by this increment alone.

## Complete actual body identity

`SourceEvalBody` retains the complete actual 113-local body in named control
segments for lookup/hit/miss, empty cases, recursive heads/tails, both additions,
both contracted queries, final choice/insertion, failure paths and cleanup.
Straight-line segments use ordinary `List.foldr Control.Tree.step`, with the
existing source-control interpreter. All switches, drops, partial moves, scalar
calls, metadata and the undefined-behavior leaf remain represented.

`Evaluator.actual_body` kernel-checks whole-body equality with
`SourceEval.Certificate.original.body .evaluate`. The initial proposed term was
printed from the existing Lean reader using standard Lean deriving/Repr; there
is no new JSON parser or trusted external normalizer. The kernel identity,
rather than that rendering step, establishes the connection. The existing
`Certificate.original_read` and `original_execute` continue to bind the complete
retained source to execution.

## Execution and native contracts

`cache_hit_exec`, `empty_left_exec` and `empty_right_exec` prove complete outcomes
and costs for arbitrary callee interpretations given their relevant completed
lookup/insertion executions. `empty_exec` combines both empty-query cases.
Callee costs are retained in full; no supplied global work cap is assumed.

`cache_hit_source` discharges lookup with the existing actual-program helper
theorem at its established sufficient nesting fuel. Any first hit returns the
copied cached witness and the exact original table. `empty_source` discharges
lookup and insertion: a miss with either query word empty returns the zero/empty
witness and prepends exactly its new entry to the input table, preserving the
old suffix. The left-empty branch takes precedence when both words are empty.

`cache_hit_native` and `empty_native` reuse the translated native evaluator's
actual equation and the existing native lookup/insertion theorems.
`empty_source_total` combines both outcomes for every native warm table and
every query with at least one empty word, with sufficient helper nesting fuel.
It retains actual expanded-program success, native agreement, exact returned
witness/table, one local destructor visit, zero locally destroyed Boxes and one
evaluator call. `source_of_exec` supplies the entry-charge composition bridge;
it is consumed by the proved branch contracts rather than used as a
substitute for them.

No cache-soundness, score/word consistency or small cached-witness assumption is
added. Empty queries can return an unsound cached witness with a maximal `u32`
score and a nonempty word. The cache-hit theorem preserves that behavior.
Optimality remains governed by the existing separate sound-cache hypotheses.

## Complete declared costs

Let `L` be the old complete source lookup cost and `I` the insertion cost from
the completed helper contracts. The new exact cost constructors give:

| Path | Work steps including evaluator entry | Events | Destructor visits / Boxes | Evaluator calls |
| --- | --- | --- | --- | --- |
| Cache hit, any query | `67 + L.steps` | `L.events` | `1 / 0` | `1` |
| Miss, left word empty | `129 + L.steps + I.steps` | `L.events + I.events` | `1 / 0` | `1` |
| Miss, left pair and right empty | `134 + L.steps + I.steps` | `L.events + I.events` | `1 / 0` | `1` |

The extra five steps in the last path are the additional source tag test. The
local destructor visit consumes either the moved-out optional shell on a hit
or the empty optional node on a miss. Complete table/witness values occur in
the returned tuple; local Box destruction is zero in these paths. These remain
snapshot/partial-local declared operation currencies, not a claim of physical
memory ownership, drop-glue instruction adequacy, allocator safety or wall time.

## Validation and next work

CI imports the new API and runs `Tests/SourceEvalBase.lean`. It covers a
first-hit duplicate-key cache with an inconsistent maximal score and nonempty
witness on empty queries; a cold empty/empty run with exact events
`(lookup=1, compare=0, copy=3, allocation=2, result-copy=1)`; and a universal
consumer binding actual JSON execution to native agreement for all base inputs.

```bash
dev/setup-build-caches.sh --status
(cd proofs && lake build)
(cd proofs && lake env lean Tests/SourceEvalBase.lean)
(cd proofs && lake env lean BaselineAudit.lean)
```

Validation passes:

- Full library: 3,881 jobs; actual whole-body kernel identity: 83 seconds.
- All 28 Lean suites, native WP example and nine Python reifier tests.
- 645 distinct audited endpoints, including eleven new endpoints, with axiom
  closures within `propext`, `Classical.choice`, `Quot.sound`.
- Shared `leanq` statement inspection of `cache_hit_source` and
  `empty_source_total`: 838 unique declaration records in the exported payload,
  retaining actual source/native execution, depth and branch conditions,
  arbitrary native table/witness inputs and complete cost components.
- New modules have no warnings; `git diff --check` passes. Closed simplification
  avoids exploring unknown match arms; accepted base proofs build in nine seconds.

Local logs: `/var/tmp/subtree-eval-body-cert.log`,
`/var/tmp/subtree-eval-base-{full-build,refinement,regression,axioms}.log`
and `/var/tmp/subtree-eval-base-statements.{json,txt}`. Rust/generated artifacts,
frontend/executor implementations and all pins remain unchanged. The preceding
`6137120` full regeneration and thirteen Rust tests remain the unchanged
provenance/behavior baseline.

Next prove the recursive pair/pair cases using the seven completed helper
contracts and the scalar/checked-add bridge, with exact output tables on every
early failure/overflow. Establish the required whole-profile typing, region,
owner/storage, local-borrow and addressed live-destruction simulation. Then
compose the public maximum entry point and separate indexed/token/reconstruction
wrappers, input policy and G3. W04, MEM-03/04, SRC-01/C3 and application resource
claims remain open under D12's explicit scoped source-operation boundary.
