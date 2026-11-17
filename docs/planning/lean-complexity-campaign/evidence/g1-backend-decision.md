# G1 backend decision at the operational C2 boundary

Date: 2026-11-16. Baseline: `584dcc9` plus this Lax62/native-signature increment.

**Decision:** use Lean's installed `Std.WP` with the existing operational
interpreter for the next deterministic C2 contracts. Keep arlib and Lax62 as
optional, checked interoperability pilots. This delivers the G1 route-selection
decision at an explicit C2 boundary. **G0's remaining reconnaissance, SRC-01/C3,
the full memo/source adapter and all application runtime endpoints remain open.**
This decision does not complete the research program or replace its source and
complexity obligations with an easier model-level result.

## Same program, domain, specification and resources

All three use `LookupSource.Program.body`, generated from the four real Rust
functions `copy_word`, `words_equal`, `copy_result`, `memo_lookup`. Structural
comparison is the same recursive scan, not a separate scalar/list example.
The independent lookup answer is `MemoizedOrderedSolver.findResult`; comparison
returns `decide (left = right)` and copying preserves the independent input value.

Inputs are all represented finite native words/tables, including duplicate keys.
The sufficient-fuel hypotheses are the original `wordHeight`/`lookupDepth`
inequalities; fuel controls nesting, not work. No `TableSound` premise is needed
for the first-hit answer or the exact packet contract. Oversized cached witnesses
remain in the copy count. The shared source proofs give success on every such
input at sufficient fuel, plus deterministic value/cost uniqueness.

Resources are the original instruction/access steps and five distinct packet
counts: lookup nodes, structural comparisons, word-copy nodes, Box creations and
result copies. All candidates retain these counts and the same proved
`256 * events.units` instruction envelope. The currencies are not summed into
a word-RAM, allocator or hardware-time claim. With `TableSound`, the existing
`LookupEvents.sound_unit_bound` supplies the common readable envelope

```text
256 * (t * (2*L + 2*R + 3) + 4*min(L,R) + 3),
```

where t is actual table length and L/R are query Pair counts. This is the
already-proved operational-model envelope, not a new Rust runtime theorem.

| Candidate | Executed implementation and checked resource connection | Public contract / composition |
| --- | --- | --- |
| Native Std.WP | `ResourceCostAudit.LookupSourceWP.call` executes the original interpreter; `call_wp_iff` equates successful WP contracts with actual successful operational runs and their complete accumulated costs | `lookup_wp`, `compare_wp`, `copy_wp`, `copyResult_wp`; `bind_run` preserves prior work and result-dependent second-call arguments; installed WP sequencing/consequence remain available |
| Charged arlib | `ArlibSpike.SourceExecution.action/execute/run` interpret the generated syntax using charged primitives and bind; `run_observe` proves exact successful values and all six currencies for arbitrary bodies/fuel | `lookup_spec`, `compare_spec`, `copy_spec`, `copyResult_spec`; `observe_bind` transfers exact sequencing from upstream charged bind |
| Lax62 timed | `LaxSpike.SourceExecution.action/execute/run` use upstream `NRest.bindT`, `consume`, `returnT`; `run_exact` equals the encoded source interpretation; `run_success` supplies exact singleton behavior and `nofailT` | The four `*_spec` results use upstream `NRest.spec` and `≤`; `encode_bind` reuses upstream consumption/bind laws, including `bindT_consume` and currency continuity |

The arlib/Lax interpreters do not compute the old whole source run inside a
free return and attach its final cost afterward. Their syntax-directed primitive,
branch and callee costs are composed during interpretation. Exact correspondence
is proved separately from the existing source budget. The native route reuses
that established interpretation directly rather than maintaining another one.

## Mandatory cases, adversary, termination and errors

The existing `Tests/LookupSource.lean` cases cover empty input, miss, first hit,
last hit, duplicate first hit, left mismatch skipping the right key, an early
head mismatch skipping tails, full structural equality and oversized witness
copy. The source tests passed in the preceding baseline validation; all thirteen
source-pilot hashes still match. Native WP equivalence and both universal backend
correspondence proofs transfer those same cases without imposing key uniqueness.

Every candidate rejects the existing actual source edit
`let _ = words_equal(left, left);` on empty lookup input while preserving its
`None` answer. The original comparison budget is zero and the mutant executes
one comparison. Lax additionally proves the original meets the same successful
specification and the mutant fails it with *all other resource budgets unbounded*.
This rejects the comparison component, not necessarily the slack aggregate bound.

All supported successful inputs have the original constructive termination/fuel
certificate. Unsupported or insufficient-fuel executions are outside these
success contracts. Native WP rejects its error branch; arlib's successful
observation erases a failing run's tally; Lax maps failure to NREST's top, which
cannot refine a successful specification. Failure-path work is unspecified in
all three. No nondeterministic-totality claim about arbitrary user programs is
inferred from the Lax API: these generated computations have exact singleton
semantics on their supported inputs.

## Compatibility, proof burden and exact unselected machine routes

All candidates build under unchanged Lean 4.35.0/main dependency pins. Arlib is
`8d08f89a6d05c5e8368e91659bd6e117fbb74c4e`. Lax62Proofs is
`0503df0eaf4e41104b9a3aa31e3e028b5adf7a0e`, with transitive word-RAM packages
at `9394e531cc51cb67a0214bca3f9264dfe97ba5c7`. Every overlapping dependency
revision equals the main manifest. Arlib and Lax62 are Apache-2.0; Std.WP is part
of the pinned Lean distribution. Lax's three selected timed modules build
unmodified despite its original Lean 4.33 pin. Its full original-toolchain and
codegen builds are not claimed.

The following are precise missing obligations, not evidence that those libraries
cannot solve the problem:

- **Arlib RAM:** inspected `ExactRealizes` requires a `Charged Op` computation,
  a `RAM w` program, a `RamState w` representation precondition, result/final-state
  correctness, and exact opcode tallies. Our six source currencies and immutable
  `Value` snapshots supply none of those RAM representations or a justified
  source-to-opcode price exchange. The charged pilot is not `ExactRealizes`.
- **Lax IR/RAM:** inspected `Cash.spec_of_hnRefine` requires an actual `Ir.Com`,
  `hnRefine`, represented initial/final assertions, bounded state/execution,
  cost cashing and result readout. `computesInTime_of_spec` additionally needs
  an IMP program/layout, a reasoning specification, input bounds and word-fit
  hypotheses. The imported NREST modules do not discharge these obligations
  for our generated `Code`/references. Cash/codegen source was inspected, not
  newly built or instantiated. The timed pilot is not an IR compilation proof.

For the selected C2 target, neither optional machine conversion adds an established
source guarantee over the native route. Both optional candidates require another
interpreter correspondence proof; native WP reuses the existing one and brings
no new dependency. This is the reason for the choice. It is not a framework-wide
ranking or a proof-script-size score. Cached builds show the optional adapters
elaborate in seconds; there was no controlled elaboration benchmark, so no speed
claim is made. Iris is not added for this read-only fragment; future shared-heap
ownership work must make its own backend decision.

## Validation and reproducibility

From the repository root, after configuring VM caches:

```bash
(cd proofs && lake env lean experiments/resource_cost_audit/LookupSourceWP.lean)
(cd proofs/experiments/arlib_cost && lake build)
(cd proofs/experiments/lax62_cost && lake build)
```

These pass and print the final theorem signatures and axiom closures. Optional
builds pass 3,781 and 3,490 jobs respectively; the latter compiles only its source
dependency chain, not every unrelated main theorem. New adapter modules have no
linter warnings. Existing upstream legacy/deprecation warnings are retained.
All printed endpoints use only the accepted `propext`, `Classical.choice`,
`Quot.sound` baseline. The main library and its four example suites passed in
the preceding baseline run; no production source, main manifest or generated
module changed. Current sources match all thirteen original pilot hashes.

Local evidence is in `/var/tmp/subtree-g1-native-signatures.log`,
`/var/tmp/subtree-g1-arlib-build.log`, `/var/tmp/subtree-g1-lax62-build.log`.
The source `#check`/`#print axioms` commands reproduce the relevant evidence
without retaining local caches or logs. This increment needs no regeneration:
all Rust/generated-source inputs are unchanged.

## W04/W05 boundary and named W06-C3 obligations

W04/W05 may now use deterministic native computation plus installed Std.WP for
the generic finite memo request/cache contracts. Their C1 interpreter theorems
and C2 operational adapters must remain separately named. Recover the existing
LV counters, preserve exact small-input cases, and exercise an unrelated client
and two representations before claiming generic completion. Do not import the
experimental arlib/Lax implementations into production merely to reuse a wrapper.

**W06-C3 remains active and unproved.** Its next source-specific obligations are:

The [actual evaluator body/base increment](memo-evaluator-base-paths.md)
kernel-checks complete control and establishes universal cache-hit and
empty-query source/native paths, preserving arbitrary warm storage, exact
returned tables and complete local/callee costs. Recursive pair/pair, error/
overflow, whole-profile typed addressed safety and core/wrappers/G3 stay open.
The 3,881-job build, all 28 Lean suites, native WP, nine Python tests and
645-endpoint axiom audit pass. Shared statement inspection covers 838 unique
declaration records.


The [actual owned-choice increment](memo-owned-choice.md) kernel-checks its
source body, proves universal source/native first-on-ties choice, and accounts
for losing-value destruction with exact structural work. This adds the seventh
ordinary helper contract. Addressed live destruction, the actual evaluator/core
and wrappers/G3 remain next; SRC-01/C3 is still open.
The 3,877-job build, all 27 Lean suites, native WP, nine Python tests and
634-endpoint axiom audit pass. Shared statement inspection covers 706 records.


The [expanded evaluator helper bridge](memo-evaluator-helper-bridge.md) now
kernel-checks the actual six-helper body identities and reuses recursive native
and addressed safety results at unchanged fuel/full work. It adds neither
destruction nor evaluator calls on those successful helper runs. Numeric-width
premises are explicit and hold for native values. Whole-evaluator typing,
local-borrow/destruction and functional/resource composition, public core,
wrappers and G3 remain required; SRC-01/C3 remains open.
The 3,873-job build, 26 Lean suites, native WP, nine Python tests and
624-endpoint axiom audit pass. Shared statement inspection covers 1,239 records.


The [complete evaluator source-profile increment](memo-evaluator-source-profile.md)
now kernel-reads all nine actual bodies and binds the source to full primitive
execution, including partial moves, scalar/checked-add operations, live drops,
metadata and public-core table destruction. Common control/frontend semantics
are reused. Next bridge completed helpers and compose whole-program typing,
regions, addressed local borrows/destruction, ownership/storage and universal
functional/resource correspondence. Native guards are not those universal
proofs. Validation is in progress; the same D12 boundary remains explicit.

The [actual evaluator partial-local increment](memo-evaluator-partial-locals.md)
inspects the real pinned evaluator/core extraction and proves partial moves,
sibling/Box-shell preservation, declared drop-work transfer and local frame
facts. Next consume them in actual normalization/execution with arithmetic,
metadata/unreachable paths, local addressed borrows and full safety/cost
composition. The primitives do not by themselves certify evaluator execution.
The 3,858-job build, 24 suites, native WP, nine Python tests and
572-endpoint axiom audit pass.

The [memo loan/region increment](memo-loan-regions.md) now composes actual
helper runs with typed shared-loan traces, ordinary reference-free outputs and
actual parsed region annotations in retained-world lifetimes. Native endpoints
retain all preceding source/heap, storage, guard/spatial, returned-owner and
complete-cost conclusions plus stable caller loans. Next actual evaluator/core
with owned-local borrows, arithmetic, destruction/errors, then wrappers and G3.
The same D12 source-operation boundary remains explicit. The 3,855-job build, 23 suites, native WP, nine Python tests and
552-endpoint axiom audit pass.

The [memo storage increment](memo-stack-initialization.md) retains actual source
live/dead markers and declaration counts, kernel-checks storage/initialization,
and discharges recursive storage contracts with unchanged costs. Native totality
composes those traces with prior typing, ownership, local guards and spatial
frames. Dynamic shared loans/lifetime interpretation remain next, followed by
actual evaluator/core, wrappers and G3 adversaries. The 3,850-job build, 21 suites, native WP, nine Python tests and
531-endpoint axiom audit pass.

The [memo guard/spatial increment](memo-spatial-ownership.md) now proves actual
recursive local guards and intermediate owner separation, retaining insertion's
owned argument and all suspended caller frames. Native source/heap/readback/
returned-owner/cost endpoints compose these traces. Normal storage allocation/
initialization and dynamic loan/lifetime interpretation remain next, followed
by actual evaluator/core, wrappers and G3 adversaries. Final ownership and
owner-safe `.scope` are not substitutes for those remaining obligations.

The [memo typing/scope increment](memo-source-typing.md) now kernel-checks actual
layouts/signatures/nested annotations/static constraints and free/body binders,
proves recursive operational typing and ordinary output closure, and composes
with the parsed region-bearing program. Insertion's owned table and distinct
value/region arities are preserved. Guard/storage/spatial and dynamic loan/
lifetime traces for these functions remain required before evaluator/core and
wrappers; scope metadata alone is not a dynamic lifetime proof.

The [addressed memo primitive follow-up](memo-heap-ownership.md) now composes
source and heap runs, independent typed readback, exact allocation growth and
returned ownership. Insertion's actual tail retains the original table, with
complete old-plus-fresh occurrence accounting and external frames preserved.
Intermediate source/type/guard/storage/spatial/loan/region invariants for these
new functions remain required, followed by actual evaluator/core, wrappers and
G3 adversaries. This advances items 2--3 without closing full C3.

The [actual memo primitive bridge](memo-source-primitives.md) now retains and
kernel-normalizes insertion/concatenation, composes source/native independent
outputs and explicit copy/Box events, and reuses polymorphic control semantics.
This begins item 3 below. Addressed safety for these new helpers, the actual memo
evaluator/core, wrappers and G3 adversaries remain required. Their source
control certificates do not transfer lookup's heap/loan invariants by themselves.

Current follow-up: the [scoped interpreted lookup pilot](lookup-region-erasure.md)
composes checked source control/types, addressed reads/moves, owner separation,
local storage, typed immutable loans and a region-erasure equivalence with native
success/readback and unchanged costs. This advances items 1--2 for the named
lookup source-operation model. Charon/data import and primitive/runtime adequacy
remain explicit boundaries; D12 accepts this initial endpoint without requiring
a whole-compiler theorem. Next implement item 3 for the actual memo operations,
then wrappers and item 4. Full C3 is not closed by lookup alone.

Follow-up: the [source-control certificates](lookup-source-certificates.md)
now validate both retained lookup extractions and prove control/result/cost
preservation in the declared snapshot primitive model. The external Python
control reifier is no longer trusted for those concrete normalizations.
This advances item 1 below; typed primitive/heap adequacy and items 2--4 remain
required. The full C3 claim remains unproved.

1. A checkable source/reification relation for the pinned LLBC fragment, with
   semantic preservation for every supported statement and rejection of unsupported
   ones. Hashes and Python regression tests alone do not prove this relation.
2. A representation/simulation for actual typed shared references, local moves,
   owned Box values and their allocation events; immutable snapshots alone do not
   discharge heap, aliasing or lifetime obligations.
3. Composition with the actual memo evaluator, insertion, concatenation and one
   public core entry point, including all normal work and explicit input/error
   policy. Then handle indexed/token/reconstruction wrappers separately.
4. Preserve the extra-scan/clone, omitted-comparison/materialization, stale-cache
   and rejected-input adversaries required by G3. Do not transfer functional
   equality into a cost theorem without event/primitive adequacy.

These are retained requirements of the full objective. Neither the backend
decision nor a future generic C1/C2 memo theorem closes SRC-01, MEM-04 or APP-01.
