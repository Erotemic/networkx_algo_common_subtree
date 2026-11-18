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

The [addressed partial primitive follow-up](memo-evaluator-addressed-partials.md)
now preserves concrete owner identities through source field moves/Box creation
and selects partial destruction addresses with exact original work. Complete
owner frames, logical liveness and guarded-address premises remain distinct.
This extends the completed source/type/region foundations toward C3. It does not
construct full addressed evaluator execution, addressable caller-local borrows
or Rust destructor/allocator interpretation. Those remain required before the
public core/wrappers/global-resource/G3 endpoint.


The [recursive typing/region follow-up](memo-evaluator-recursive-typing.md)
now discharges actual recursive type contracts and retains scoped signatures/
locals for all nine source definitions, with exhaustive binder/call-region
checks. Actual source/native totality and deep ordinary-output closure compose
at unchanged full costs. Addressed partial moves, framed caller-local loans,
owner/storage/spatial/destructor interpretation remain required before the
public core/wrappers/global-resource/G3 endpoint. Bound region IDs are not a
dynamic lifetime interpretation; full C3 remains open.


The [whole-profile type increment](memo-evaluator-source-typing.md) now checks all
nine actual declarations/control trees and both Option layouts, with independent
partial-local read/move/expression/action preservation. Recursive control/callee
composition, addressed owners/storage/local loans/regions and destruction remain
required, followed by public core/wrappers and resources/G3. Static acceptance
and snapshot preservation do not establish caller-local borrow lifetime safety.


W04/W05 may now use deterministic native computation plus installed Std.WP for
the generic finite memo request/cache contracts. Their C1 interpreter theorems
and C2 operational adapters must remain separately named. Recover the existing
LV counters, preserve exact small-input cases, and exercise an unrelated client
and two representations before claiming generic completion. Do not import the
experimental arlib/Lax implementations into production merely to reuse a wrapper.

**W06-C3 remains active and unproved.** Its next source-specific obligations are:

The [universal evaluator increment](memo-evaluator-native-totality.md) now
proves all native-input actual source/native results and tables, including
recursive failures and both overflows, with exact local/callee costs and stable
completed work across sufficient fuels. Independent consistency/memo results
retain their original premises. Whole-profile typed addressed safety, public
core/wrappers and global resources/G3 remain; SRC-01/C3 is still open.
The 3,890-job build, all 29 Lean suites, native WP, nine Python tests and
675-endpoint axiom audit pass. Shared statement inspection covers 837 unique
declaration records.


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

The [local storage/reference-graph increment](memo-evaluator-local-storage.md)
adds live classified stack roots, transitive shared graphs and concrete initialized
local borrows. Actual source address/Box/drop contracts preserve retained caller
frames under explicit resource conditions. This advances item 2; complete
addressed operation/control/call traces, initialization/mutation conflicts and
dynamic region/destructor composition still precede items 3--4 and C3 closure.

The [guarded frame-write increment](memo-evaluator-frame-writes.md) now preserves
transitive read graphs and complete owner ledgers across unrelated writes. Actual
source scalar assignments and storage markers retain existing storage identities
and caller resources; initialized nonowning references can end storage without
losing Boxes. This advances item 2. Full RHS/move/frame/control/callee traces and
dynamic region/destructor composition remain required before C3 closure.

The [addressed RHS/assignment increment](memo-evaluator-addressed-rhs.md) now
executes all operand/RHS forms and destination initialization, with incremental
metadata, actual pointer graphs and independent source/cost correspondence.
Reverse simulation consumes physical move permissions rather than an addressed
parent result. This advances item 2; actual frame/loan/owner/control/callee and
region/destructor traces remain required before C3 closure and public/wrapper G3.

The [computed inventory increment](memo-evaluator-derived-inventories.md) now
derives bounded local/caller read/owner/loan resources and remaining contexts.
One-pass assignment consumes no supplied guard or post-RHS frame premise and
preserves exact suspended caller inventories. This advances item 2; full actual
initial/control/callee, ownership/spatial and region/destructor composition still
precede C3 closure and the public/wrapper G3 program.

The [initial-frame/storage/action increment](memo-evaluator-storage-actions.md)
now constructs parameter roots from actual parsed layouts and composes successful
non-call storage/drop/assignment sequences at unchanged costs. Drop guards both
stack initialization roots and exact unique classified Box owners. This advances
item 2; ordinary/intrinsic calls, switches/returns, complete branch check success,
global exclusive transfer and dynamic regions/destructors remain before C3.

The [addressed control increment](memo-evaluator-addressed-control.md) now reads
actual retained tags, executes boolean routing/early returns through the shared
control engine, and extracts live concrete output packets at unchanged costs.
The actual choice bridge reuses the checked source body and native tie rule.
Item 2 still requires ordinary/intrinsic calls, universal physical check success,
exclusive transfer and callee storage/returned-loan/region/destructor closure.

The [mixed-world helper-call increment](memo-evaluator-helper-calls.md) reuses
six concrete ordinary executors and both intrinsics, with actual output readback,
Box-suffix/owner-ledger lifting and one-pass argument/callee/store composition.
Native input shapes and fuel bounds discharge the local call contract. Item 2
still requires control/recursive integration, choice/evaluator/maximum service,
all-path readiness/check success and full ownership/storage/region/destructor
composition; this is not C3 closure.

The [calling-entry follow-up](memo-evaluator-calling-entry.md) now composes calls
with shared source routing, passes the actual post-argument suspended stack,
constructs frames from parsed declaration counts and checks zero-owner/output-
escape cleanup before retiring all remaining callee roots. Actual parsed choice
retains its native tie rule and full entry/body cost. Recursive dispatch and
whole-run protected caller preservation, universal readiness/physical success,
exclusive transfer and dynamic regions/destructors still require composition;
the source-operation boundary and full remaining goal are unchanged.

The [recursive-calls follow-up](memo-evaluator-recursive-calls.md) now proves
whole-run caller-byte retention and the recursive callee source/cost contract
for actual parsed choice/evaluator/maximum. Native choice readiness is closed;
evaluator refinement retains input readiness and physical success. A cold empty
run executes fully. A nonempty cache-hit run identifies the next operational
loan-activity gap at `assign 12`: a stored reference outlives its last use under
the current all-initialized-reference guard. Interpret loan endings, then derive
universal readiness/physical success and global owner/region/destructor closure.
C3, production resource adequacy and the full planning goal remain open.

The [certified loan-ending follow-up](memo-evaluator-loan-endings.md) now ends
unused shared-reference resource views based on actual continuation avoidance/
reset, retaining exact original source outcomes/costs and stored pointer bits.
Observed references, owners and other indirect aliases retain their guards.
Both previously failing nonempty evaluator/maximum probes now pass complete
source value/cost and caller/live-output checks. Item 2 still requires universal
native readiness, budgets/physical success, global exclusive transfer and dynamic
region/destructor composition. C3, production resource adequacy and the full
planning goal remain open.

The [derived typed-call follow-up](memo-evaluator-typed-calls.md) reflects actual
successful concrete helper runs to source at the same fuel and full cost.
Independent actual source types discharge scalar width and selected call input
conditions. The stronger recursive/native evaluator theorem no longer takes
`Recursive.Ready`; successful physical execution remains explicit. Short-circuit
success beyond the old sufficient height bound and the necessary u32 boundary
are checked. Item 2 still requires adequate budgets and every physical check,
global exclusive transfer and actual region/destructor composition. C3 and the
full planning/resource goal stay open; the source-operation boundary is unchanged.

The [exact owner-packet follow-up](memo-evaluator-owner-packets.md) derives complete
physical owner partitions through extraction/RHS packets and guarded assignment,
exact checked Box retirement, then actual callee input, return and successful
stack closure resources. Shared
reads may alias; initial unique/live Box ownership and coverage remain explicit.
Item 2 still requires callee output/fresh/retired transfer, whole recursive owner
invariants, adequate budgets/every physical check and dynamic regions/destructors.
No C3/resource/full-goal closure or changed source-operation boundary follows.

The [owner-lifecycle follow-up](memo-evaluator-owner-lifecycle.md) composes actual
parameter entry/storage with complete non-call action-sequence ownership and
source Box destruction counts. Removed Box identities are unique, initially live
and finally dead; actual final active/caller/external owners retain full live-Box
coverage. Item 2 still requires concrete callee output transfer, selected calling
control/full-recursive owner invariants, budgets/every physical check and dynamic
region/destructor interpretation. No C3/resource/full-goal closure follows.

The [global recursive ownership follow-up](memo-evaluator-global-owners.md)
composes exact successful helper ledgers, independent typed profiles, complete
actual calls, selected control, parsed entry/close and recursive dispatch. The
native evaluator now retains its full result/table/cost and protected-byte
refinement alongside complete output/actual-caller/external ownership and
coverage of every live Box. Initial ownership and concrete success stay explicit.
Item 2 still requires adequate budgets/every physical check and dynamic parsed
region/destructor-instance interpretation. C3, production resource adequacy and
the full planning goal remain open; D12/source-operation boundaries are unchanged.

[Typed helper totality and sufficient budgets](memo-evaluator-helper-totality.md) now derives actual
success for all eight helpers/intrinsics from independently typed readable input
packets. Sufficient fuel and ghost readback thresholds require no supplied native
height, expected output or successful run. Larger readback budgets preserve the
identical world/packet/full cost; source agreement and complete output/caller/
external ownership compose. Interpreted choice/evaluator/maximum physical success,
dynamic regions/destructors, public teardown/wrappers/resources/G3 and the other
planning targets remain open. The full goal is active.
The 3,992-job build and all four affected helper/typed/recursive/runtime suites
pass, including five new warm-cache/overflow/failure paths with complete owner
and cleanup checks. The 1,270-endpoint audit includes 27 new theorems with only the accepted axiom baseline;
eight selected statement seeds cover 828 unique declarations with no unknown
references. Full-suite/native-WP/Python/Rust evidence is inherited, not rerun here.

[Stable recursive fuel and readback budgets](memo-evaluator-stable-budgets.md) now preserve every
completed actual run's exact world/packet/full cost at all larger bounds.
Independently typed helper inputs give fixed joint sufficient thresholds, a stable
output and complete owner resources. Interpreted physical success and all other
planning obligations remain open. The 3,996-job build and two affected consumers
pass; 19 new theorems bring the accepted-baseline audit to 1,289 endpoints.
Eight selected statement seeds cover 1,070 unique declarations with no unknown
references. Broader regression evidence is inherited from the preceding commits.

[Forward storage, drop and cleanup permissions](memo-evaluator-forward-permissions.md) now construct actual
runs from complete owner resources and independent live-loan/root permissions.
Read inventories partition into owners/loans/stack roots, and scans are canonical.
Fresh roots and preserved callers derive loan bounds; the pinned choice's closed
local types eliminate its active loans. Forward assignments/moves/returns,
complete interpreted execution and all other planning obligations remain open.
The 4,005-job build and affected lifecycle consumer pass. The 1,333-endpoint audit
includes 44 new theorems with only the accepted axiom baseline. Ten selected
statement seeds cover 958 unique declarations with no unknown references.

[Constructed recursive helper and choice calls](memo-evaluator-call-totality.md) now compose actual
argument extraction, callee execution and checked result storage from independent
local source steps, types, ownership and selected loan permissions. Choice runs
through recursive dispatch with one fuel; whole helper calls have fixed joint
sufficient fuel/readback bounds and stable final state/full cost. Shared helper
aliases remain permitted; choice constrains only transferred owners versus actual
post-argument suspended loans. Evaluator/maximum all-path scope/loan discharge,
recursive budget composition, dynamic regions/destructors and the other planning
targets remain open. The 4,022-job build and five affected suites pass, including
all eight recursive runtime cases. The 1,401-endpoint audit includes 18 new
theorems with only the accepted axiom baseline. Eight selected statement seeds
cover 1,125 unique declarations with no unknown references. The full goal is active.

[Constructed native evaluator entry and lookup prefix](memo-evaluator-native-prefix.md) now derives
all physical permissions for the actual parsed 113-local entry and first eleven
instructions through lookup/result storage. Native graph structure and preserved
old caller reads permit shared query/table aliases, including queries inside a
table-owned Box. Fixed sufficient fuel/readback thresholds retain one final
machine with protected caller bytes and complete ownership/coverage. Retirement
of lookup temporaries, every branch/recursive return/closure, public maximum,
dynamic regions/destructors and the other planning targets remain open.
The 4,035-job build and five affected suites pass, including all eight recursive
runtime cases. The 1,465-endpoint audit includes 64 new theorems with only the
accepted axiom baseline. Ten selected statement seeds cover 1,097 unique
declarations with no unknown references. The full goal is active.

[Complete right-contraction failure dispatch](memo-evaluator-right-failure.md)
now constructs the whole original parent body, guarded return and checked
dispatch/closure when left contraction succeeds and right contraction returns
None. Four smaller `NativeTotalFresh` contracts and independent native head/
tail/subtotal/root/left success and right-failure equations remain explicit.
Actual failure packing retains its right-cleanup suffix; the real join drops
the owned right query85 and held left witness81. Exact mask counts derive zero
owners in still-bound81 before outer left cleanup retires it and drops the held
left query71 and candidate64. All six cleanup joins and parameter return execute.
Complete ownership/coverage, allowed old query/table aliases, protected reads,
source/native agreement, None-result provenance and exact world/packet/full cost
at larger sufficient bounds survive. Every pair/pair success/failure constructor
is now available from its explicit smaller contracts; universal induction remains.
The 4,340-job library build and all eleven affected Lean suites pass. All
thirteen runtime cases pass; the new owned right-failure case checks 4,252 source
steps/seven solver calls, complete source/addressed value/table/cost equality,
caller guard bytes/liveness and full owner coverage.
The new kernel consumer discharges all four contracts with proved empty-input/
minimal-pair instances. Both queries borrow inside the old table; cleanup retires
a two-owner right query, two-owner left witness and six-owner candidate. Returned
None/table owns eighteen cells with complete coverage and stable larger bounds.
All 2,116 audited endpoints retain the accepted axioms; six new theorems in five
new proof modules are included. Eight statement seeds export 1,347 unique records
without unknown references. Thirteen Rust tests and nine Python checks pass.
CI now includes fifty-five suites; this checkpoint freshly ran the eleven
affected suites, not the full fifty-five. See the evidence report for exact commands.
Next assemble universal pair/pair `NativeTotalFresh` induction. Dynamic regions/
destructors, public maximum/cold-table teardown, wrappers/input policy/resources/
G3 and every other planning requirement remain open. No full SRC-01/C3 or
production resource closure is claimed; the full goal stays active. Earlier
[left failure](memo-evaluator-left-failure.md), root/subtotal overflow, head/tail failure and successful-parent endpoints remain checked.

[Helper owner provenance and constructive concatenation cleanup](memo-evaluator-owner-provenance.md)
now derives descendant-owner freshness from the actual helper allocation ledger.
Copy/lookup/concatenation helpers receive no owned input cells; every result Box
lies beyond the incoming heap. Guarded storage retains the exact packet owner
list. The native concatenation endpoint derives provenance relative to the
original heap and constructs its guarded owned-word drop while retaining legal
original query/table/caller aliases. Canonical inventories, closed reference
preparation and checked anchored-machine advances preserve established provenance.
Insertion/`boxNew` remain outside this fresh-output class because they transfer
owned descendants. The existing `NativeTotal` contract is unchanged.
The 4,218-job build and seven affected Lean suites pass, including eight runtime
cases. All 1,882 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,002 unique declarations with no unknown references.
Thirteen Rust tests and nine Python checks pass. Nonempty table-owned cache
aliases exercise fresh copy/lookup results and full derived storage; a parsed
nonempty concatenation derives and drops all four result Boxes; actual insertion
retains an old input owner, checking the freshness boundary.
The parent frontier remains the checked seventeen-checkpoint right-result scope.
Recursive witness provenance through complete evaluator execution, payload/
field transfers and choice still needs proof; helper provenance alone does not
supply it. Both optional joins, successful right payload transfer, general owned
cleanup, overflow exits, insertion, remaining parent returns and full pair/pair
induction remain. Dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and the remaining planning targets stay open.
The full goal remains active.

[Actual right recursion and complete right-result scope](memo-evaluator-right-scope.md) now
constructs all remaining twenty-one right-region instructions and the full
36-instruction prefix through seventeen stable checkpoints from parsed entry.
Original left-query view 91 and fresh right-word views 93/92 remain separate;
actual preparation ends 93, the call consumes 91/92/94, and original loan
origins are restored before physical retirement. Native option/table 88/89,
empty bound payload 95, both owned queries, held left witness, matched candidate,
exact original aliases and complete ownership/coverage persist. Every future
parent root at index 96 or above is unbound. Both actual contraction calls and
their complete costs are exposed. The fourth smaller `NativeTotal` premise is
explicit; the right result/table are derived. No physical parent success,
expected right post-frame/result, cache soundness or witness freshness is assumed.
The 4,214-job build and six affected Lean suites pass, including eight runtime
cases. All 1,871 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,312 unique declarations with no unknown references.
Thirteen Rust tests and nine Python checks pass. Three new consumers discharge
all four smaller calls with proved empty contracts: all seventeen checkpoints
with table-owned aliases; a two-Box left witness/six-Box candidate through right
cleanup; and cold head/left/right insertions reaching the actual right switch.
Both optional joins, successful right payload transfer, recursive witness
provenance/general owned cleanup, overflow exits, choice, insertion, remaining
parent returns and full pair/pair induction remain. Dynamic regions/destructors,
public maximum/cold-table teardown, wrappers/input policy/resources/G3 and the
remaining planning targets stay open. The full goal remains active.

[Successful-left payload and actual right-query concatenation](memo-evaluator-right-concatenation.md) now
constructs all fifteen initial right-region instructions through thirteen stable
prefix checkpoints from parsed entry. The owned left witness moves through
scratch 82 into 81; original right child reborrows execute concatenation into
85 and retire 86/87. The matched candidate, native table, exact original query
aliases and complete ownership/coverage persist; all future parent roots at
index 88 or above are unbound. Native append, helper events and the full actual
concatenation call cost are identified. Smaller head/tail/left `NativeTotal`
and independent native success/addition equations, including native left
success, remain explicit. No physical parent success/post-frame, cache soundness
or recursive witness freshness is assumed.
The 4,204-job build and six affected Lean suites pass, including eight runtime
cases. All 1,859 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,306 unique declarations with no unknown references.
Thirteen Rust tests and nine Python checks pass. Three new consumers cover all
thirteen checkpoints with table-owned repeated aliases, actual transfer of a
two-Box left witness beside a six-Box candidate, and a four-Box right query.
Right argument/fresh-view setup, right recursion and its remaining twenty-one
instructions, both optional joins, recursive witness provenance/owned cleanup,
overflow exits, choice, insertion, remaining parent returns and full pair/pair
induction remain. Dynamic regions/destructors, public maximum/cold-table
teardown, wrappers/input policy/resources/G3 and all other planning targets
stay open. The full goal remains active.

[Complete actual left contraction result scope](memo-evaluator-left-scope.md) now reaches the
real optional-result switch through twelve stable prefix boundaries and exposes
the composed sixty-instruction matched/left-contraction prefix. All eleven
instructions 49–59 retire moved arguments, extract option/table into 74/75,
clean the moved tuple, retire ended view/output roots and open payload 81.
Actual continuation preparation ends view 78; moved/ended masks restore the
strictly original loan family before physical stack retirement. Complete
ownership/coverage, exact queries, matched candidate, owned word 71 and native
left output survive. Every future parent local at index 82 or above is unbound.
Generic fresh-write memory preservation includes already retired cells; parent
root-change certificates cross actual calls. Smaller head/tail/left `NativeTotal`
and independent native head/tail/score successes remain explicit; no successful
physical parent run, expected post-frame, expected left result, cache soundness,
recursive witness freshness or global alias ban is supplied.
The 4,195-job build and six affected Lean suites pass, including eight runtime
cases. All 1,849 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,311 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Three added kernel
consumers discharge all smaller contracts with proved empty cases: repeated
table-owned aliases derive all twelve checkpoints/full sixty-instruction prefix;
a six-Box matched candidate survives real cleanup; and cold recursive insertion
reaches native fields 74/75 and empty bound payload 81 at the actual switch.
Successful-left payload extraction, right concatenation/views/call, both left/
right joins, recursive witness provenance/owned cleanup, overflow exits, choice,
insertion, remaining parent returns and full pair/pair induction remain. Dynamic
regions/destructors, public maximum/cold-table teardown, wrappers/input policy/
resources/G3 and every other planning target stay open. The full goal is active.

[Constructed actual left contraction call](memo-evaluator-left-recursion.md) now reaches its native
recursive return through eleven stable actual prefix boundaries from parsed
entry. Four argument instructions reborrow the original right query into 79
and move the owned table from 42 into 80; the actual evaluator call consumes
77/79/80 and stores its native optional/table output in 76. The retained argument
checkpoint exposes one fixed actual call and complete call cost at every larger
shared helper bound pair. Complete ownership/coverage, exact original queries,
owned word 71, matched candidate, scalar holes and original/fresh loan provenance
persist. The explicit third recursive premise is universal `NativeTotal` for
the strictly smaller concatenated-left request. No successful physical parent
run, expected post-callee frame, expected left result, cache soundness, recursive
witness freshness or global alias ban is supplied.
The 4,185-job build and six affected Lean suites pass, including eight runtime
cases. All 1,833 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,304 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Three new consumers
discharge all smaller contracts with proved empty cases: table-owned repeated
aliases derive all eleven prefixes and exact-cost call; a six-Box matched
candidate survives real recursion; and a cold external-alias parent executes
a contraction miss that inserts a second native table key.
Instructions 49–59 still require moved-argument retirement, result/table
extraction, fresh-view ending, moved-tuple cleanup and payload opening before
the actual left-result switch. Left/right contraction branches, recursive
witness provenance/owned cleanup, overflow exits, choice, insertion, remaining
parent returns and full pair/pair induction remain. Dynamic regions/destructors,
public maximum/cold-table teardown, wrappers/input policy/resources/G3 and every
other planning target stay open. The full goal remains active.

[Constructed fresh owned-word views](memo-evaluator-owned-word-loans.md) now reaches actual references
78/77 to concatenated word 71 through nine stable prefix boundaries from parsed
entry. All five setup instructions construct result/reference storage, borrow
the owned word and reborrow through the first reference. `AnchoredLoanMachine`
retains strict pre-entry bounds for original query loans and separate precise
support for fresh word loans. The word's actual read footprint contains its
Box owners and own stack root; other selected stack roots remain available
for moves/stores/retirement. Complete owner uniqueness also separates this
anchor from other locals' owners, leaving original-query destructor obligations
explicit. Exact native queries, matched candidate, updated table and original
origins persist. Smaller head/tail `NativeTotal` and independent native successes
remain explicit; no successful physical parent run, cache soundness, recursive
witness freshness or global alias ban is supplied.
The 4,177-job build and six affected Lean suites pass, including eight runtime
cases. All 1,820 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,293 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. New table-owned alias
and nonempty four-Box consumers discharge smaller contracts with proved empty
cases, derive all nine prefixes/result-root permission and separate matched
candidate owners from the fresh-loan anchor.
Right argument 79, table argument 80, the left contraction call and anchored
call preservation/cleanup remain. Recursive witness provenance/owned cleanup,
overflow exits, both contraction joins, choice, insertion, remaining returns
and full pair/pair induction remain. Dynamic regions/destructors, public maximum/
cold-table teardown, wrappers/input policy/resources/G3 and every other planning
target stay open. The full goal remains active.

[Constructed left-query concatenation](memo-evaluator-left-concatenation.md) now reaches owned appended word
71 through eight stable actual prefix boundaries from parsed evaluator entry.
All nine concatenation instructions construct original child reborrows, execute
the unchanged helper, retire moved argument roots and retain the matched
candidate, table, total and all seven exact original query/view snapshots.
Generic mask preservation supports actual calls and suffix preparation; exact
native append, structural helper events and complete concatenation call cost
are identified. Both native contraction requests strictly decrease the independent
Dyck-word induction measure. Smaller head/tail `NativeTotal` and independent
native success equations remain explicit; no successful physical parent run,
cache soundness, recursive witness freshness or global alias ban is supplied.
The 4,168-job build and six affected Lean suites pass, including eight runtime
cases. All 1,788 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,309 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Two additional kernel
consumers discharge smaller contracts with proved empty cases: table-owned
repeated aliases derive all eight prefixes, and two nonempty concatenation
operands produce a four-Box owned word with complete external/table ownership.
Fresh references to word 71 and their selected loan permissions, both contraction
calls, recursive witness provenance/owned cleanup, overflow exits, choice,
insertion, remaining returns and full pair/pair induction remain. Dynamic
regions/destructors, public maximum/cold-table teardown, wrappers/input policy/
resources/G3 and every other planning target stay open. The full goal is active.

[Constructed owned matched witness](memo-evaluator-matched-scope.md) now
constructs the first thirty actual successful-root-score instructions through
matched candidate 64: total extraction, two real Box allocations, owned pair-word
assembly, score attachment and all moved-out temporary cleanup. The parsed
`Evaluator.entry_pair_matched_scope_complete` retains seven actual prefix
boundaries at shared sufficient bounds, complete original-loan machinery,
native candidate, scalar-only head/tail masks and fresh concatenation storage.
Smaller head/tail `NativeTotal` and independent native score successes stay
explicit; no physical parent success, cache soundness, witness freshness or
global alias ban is supplied. Generic Box/aggregate constructions transfer
complete owners through the unchanged actual helpers and checked stores.
The 4,158-job build and six affected Lean suites pass, including eight runtime
cases. All 1,757 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,301 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Table-owned alias
consumers discharge both smaller contracts with proved empty cases: one derives
all seven prefixes; another uses nonempty cached witnesses and constructs a
candidate with six owned Boxes, preserving complete ownership and coverage.
Retaining exact query/view snapshots through the matched prefix, concatenation,
fresh query-loan tracking, both contraction calls, recursive witness provenance/
owned cleanup, overflow exits, choice, insertion, remaining returns and full
pair/pair induction remain. Dynamic regions/destructors, public maximum/cold-table
teardown, wrappers/input policy/resources/G3 and every other planning target
remain open. The full goal stays active.

[Constructed root-score arithmetic and native switch](memo-evaluator-root-score-scope.md) now
constructs all twelve actual root-score instructions after successful subtotal:
scalar payload copying, subtotal/temporary retirement, fresh total/result storage,
checked addition of the literal one and argument cleanup. The parsed endpoint
`Evaluator.entry_pair_root_score_scope_complete` retains all six actual prefix
boundaries, both owned witnesses, the updated table, native subtotal and exact
root-score result/overflow. `Calling.Prefix.shape` derives activation count and
untouched-root support across actual calls without extra readiness assumptions.
Smaller head/tail `NativeTotal` and independent native success equations remain
explicit; no physical parent success, cache soundness or alias ban is assumed.
The 4,148-job build and six affected Lean suites pass, including eight runtime
cases. All 1,744 audited endpoints retain the accepted axiom baseline; eight
statement seeds resolve 1,295 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Kernel consumers derive
root-score `Some 1` with table-owned query aliases, and root overflow from a valid
maximum-width subtotal with distinct cached head/tail scores and explicit external
query ownership. Both recursive contracts are discharged by proved empty cases.
Matched-witness construction, concatenated contraction queries and fresh query
loan tracking, recursive witness freshness/owned cleanup, overflow exits, both
contraction calls, choice, insertion, remaining returns and full pair/pair
induction remain. Dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and every other planning target stay open.
The full goal remains active.

[Constructed subtotal arithmetic and actual result switch](memo-evaluator-subtotal-scope.md) now
constructs all fifteen score-prefix instructions after native head/tail success:
owned tail extraction, both scalar score copies, actual checked addition and
argument retirement. `Evaluator.entry_pair_score_scope_complete` connects parsed
entry and all five common/miss/head/tail/score prefix boundaries at shared
sufficient bounds, retaining both owned witnesses, the updated table and the
actual subtotal discriminant. Native-width result/overflow and complete cost
are identified by source reflection. Smaller head/tail `NativeTotal` contracts
remain explicit. `original_checked_add_operands_complete` also supports the
literal operand needed by the subsequent root-score addition.
The 4,140-job build and six affected Lean suites pass, including eight runtime
cases. All 1,730 audited endpoints use only the accepted axiom baseline; eight
statement seeds resolve 1,314 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python checks pass. Two kernel consumers
use proved empty-input contracts with table-owned query aliases: a head miss/
tail hit yielding subtotal zero, and warm maximum-width scores selecting overflow
without cache soundness or a successful physical parent premise.
Root-score arithmetic, recursive witness freshness/owned cleanup, overflow exits,
contractions, choice, insertion, remaining parent returns and full pair/pair
induction remain open. Dynamic regions/destructors, public maximum/cold-table
teardown, wrappers/input policy/resources/G3 and every other planning target
remain. The full goal stays active.

[Complete tail scope and owned-drop support](memo-evaluator-tail-scope.md) now
constructs all twenty-four tail-prefix instructions through the actual tail-result
switch: argument retirement, native optional/table extraction, moved-output
cleanup and fresh payload storage. `Evaluator.entry_pair_tail_scope_complete`
connects parsed entry and all four actual prefix boundaries at shared sufficient
bounds. The successful-tail path additionally moves its owned witness into 47
through the first six score instructions, retaining the owned head witness.
`OriginalLoanMachine.drop_fresh` constructs nonzero owned drops from explicit
selected-owner freshness, preserving original loan origins; deriving that
freshness for recursive witnesses remains open. No caller alias ban or successful
physical parent premise is added. Full pair/pair induction remains open.
The 4,133-job build, six affected Lean suites (including eight runtime cases),
1,719-endpoint axiom audit, eight elaborated statement seeds (1,302 unique
records, no unknown references), thirteen ordered Rust tests and nine Python
checks pass. A repeated table-owned alias consumer discharges both smaller
contracts using proved empty-input totality and reaches the actual tail switch.
Score arithmetic, recursive witness freshness and owned cleanup, overflow,
contractions, choice, insertion and remaining parent returns are still open,
as are dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and every other planning target.
The full goal remains active.

[Complete head failure and constructed tail recursion](memo-evaluator-head-failure-tail-call.md) now
constructs the entire selected head-failure invocation, including routing,
output/temporary cleanup, return, checked closure, complete ownership and stable
exact world/packet/full cost. The successful-head path also reaches the actual
tail recursive call through fourteen instructions, retaining the owned head
embedding, native queries/views and tail output. Both paths use explicit
universal contracts for strictly smaller requests; full pair/pair induction is
open. `Evaluator.head_failure_total` and
`Evaluator.entry_pair_tail_prefix_complete` record these endpoints. A repeated
table-owned alias consumer discharges both smaller contracts with proved empty
base cases and exercises a head miss followed by a tail hit.
The 4,127-job build and six affected Lean suites pass, including all eight
runtime cases. All 1,710 audited endpoints retain only the accepted axiom
baseline; ten statement seeds cover 1,321 unique declarations with no unknown
references. Thirteen ordered Rust tests and nine Python checks pass.
Tail result/argument cleanup, owned-witness destructor loan provenance, score
and contraction/choice/insertion paths, other parent returns and full pair/pair
induction remain. Dynamic regions/destructors, public maximum/cold-table teardown,
wrappers/input policy/resources/G3 and all other planning targets stay open.
The full goal remains active.

[Constructed pair/pair head recursion and result scope](memo-evaluator-head-scope.md) now
constructs parsed entry, common lookup, miss setup and all twenty-six actual
head-prefix instructions, including the recursive call, result/table extraction,
temporary retirement and head-result inspection. The explicit induction premise
is universal totality for the strictly smaller head query pair; no global
pair/pair instance or parent return is assumed. `Rust.SourceEval.Evaluator.entry_pair_head_scope_complete` retains native queries/Box-field views, fresh
payload/return storage, complete ownership, original loan origins and stable
prefix worlds at every larger helper bound pair. A repeated table-owned alias
consumer discharges the smaller contract using proved empty-input totality.
The 4,112-job build and six affected Lean suites pass, including all eight
recursive runtime cases. All 1,686 audited endpoints retain only the accepted
axiom baseline; ten statement seeds cover 1,322 unique declarations with no
unknown references. Thirteen ordered Rust tests and nine Python checks pass.
Selected head failure/tail recursion, overflow/contraction/choice/insertion,
parent return/closure and full pair/pair induction remain. Dynamic regions/
destructors, public maximum/cold-table teardown, wrappers/input policy/resources/
G3 and every other planning obligation remain open. The full goal stays active.

[Complete actual evaluator empty-query miss execution](memo-evaluator-empty-totality.md) now
constructs parsed entry, lookup, all eleven miss-setup and 47 empty-branch
actions, native insertion, both empty routes, return and checked closure.
`Rust.SourceEval.Evaluator.empty_miss_total` derives the empty witness/inserted
table, readable output, complete ownership/coverage and one exact final world,
packet and full cost at every larger fuel/readback pair. Original query-tuple
loans and temporary embedding views permit legal query/table/caller aliases;
no successful physical run, cache soundness or global owner/loan disjointness
is assumed. The 4,093-job build and six affected Lean suites pass, including
eight recursive runtime cases and two whole-invocation table-alias consumers.
Thirteen ordered Rust tests and nine Python frontend regressions pass.
All 1,652 audited endpoints retain only the accepted axiom baseline; ten
statement seeds cover 1,314 unique declarations with no unknown references.
Pair/pair recursion/overflow/failure, dynamic regions/destructors, public
maximum/cold-table teardown, wrappers/input policy/resources/G3 and every other
planning obligation remain open. The full goal remains active.

[Constructed evaluator miss setup and native word routing](memo-evaluator-miss-setup.md) now
constructs all eleven miss-setup instructions after parsed native entry and the
common lookup prefix. Exact shared-pointer copies assemble tuple 13, whose loans
are proved to originate below the pre-entry memory bound; all temporary roots
retire. `Rust.SourceEval.Evaluator.entry_miss_setup_complete` retains complete
ownership, native inputs/tuple, fresh empty return storage and stable prefix
worlds at every larger helper fuel/readback pair. Both actual word inspections
and native routing check. A table-owned repeated-query-alias consumer passes.
The 4,072-job build and six affected Lean suites pass, including eight recursive
runtime cases. All 1,599 audited endpoints use only the accepted axiom baseline;
ten statement seeds cover 1,109 unique declarations with no unknown references.
Thirteen ordered Rust tests and nine Python frontend regressions pass. Empty-
branch insertion/return, pair/pair recursion/overflow/failure, public maximum,
dynamic regions/destructors and the remaining planning targets stay open.
The full goal remains active.

[Complete actual evaluator cache-hit execution](memo-evaluator-cache-hit-totality.md) now
constructs parsed entry, lookup, all twenty hit actions, return and checked closure
from independent native readable packets and complete ownership. Query-loan
origins derive selected fresh stack-root permissions while permitting queries
inside table-owned Boxes. `Rust.SourceEval.Evaluator.cache_hit_total` returns the
cached result and unchanged native table, complete output/caller/external owner
resources, and one exact final world/packet/full cost at every larger fuel/readback
pair. No cache soundness or successful physical run is assumed. The 4,061-job
build and five affected suites pass, including eight recursive runtime cases and
a whole-invocation table-alias consumer. All 1,559 audited endpoints use only the
accepted axiom baseline; ten statement seeds cover 1,326 unique declarations with
zero unknown references. Thirteen ordered Rust tests and nine Python frontend
checks pass. Empty-query misses,
pair/pair recursion/overflow/failure, public maximum, dynamic regions/destructors
and the remaining planning targets stay open; the full goal remains active.

[Complete common evaluator prefix and native lookup routing](memo-evaluator-common-prefix.md) now
constructs actual parsed entry and all fourteen common instructions through
lookup-temporary retirement, followed by actual native hit/miss inspection.
The checked scope retains the independent lookup answer, ended table view 6,
fresh empty return storage, original caller bytes and complete ownership/coverage.
Shared query/table/caller aliases remain allowed. Branch bodies, recursive
budget composition, return/closure, public maximum, dynamic regions/destructors
and the other planning targets remain open. The 4,042-job build and five affected
suites pass, including all eight recursive runtime cases and new warm-alias/cold-
caller consumers. The 1,480-endpoint audit includes 15 new theorems with only the
accepted axiom baseline. Ten selected statement seeds cover 1,085 unique
declarations with no unknown references. The full goal remains active.
