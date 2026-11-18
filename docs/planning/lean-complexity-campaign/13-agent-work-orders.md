# 13. Bounded work orders

## Shared handoff rules

These orders are implementation assignments for the campaign, not work already completed by this overlay. Every agent starts from a named Git/source baseline, reads the relevant existing declarations and reports exact changes. Preserve independent specifications and generated-code boundaries. Cython is evidence of intent, not a correctness oracle.

Use the current toolchain unless the assignment explicitly owns an isolated compatibility experiment. Do not modify unrelated manifests, rewrite retired Lozano code, invent hidden constant-time axioms or add process-only source-text tests. Report a missing source or theorem as a blocker rather than filling it with an assumption that contains the desired result.

The standard handoff contains: target IDs; baseline/pins; exact declarations and signatures; sources/locators; model level; proof/build commands and results; assumptions/axioms; consumer; counterexample or adversarial case; changed paths; and remaining obligations. A documentation claim that a theorem exists must point to its actual declaration.

## W01. Declaration-level reuse audit

**Own:** a new audit report and machine-readable updates under this campaign's evidence area. No production code changes.

**Read:** L02--L05, L14, R14; current local library audit and `proofs/VERIFICATION.md`.

**Task:** inspect the actual definitions and exported statements for cost composition, totality, realization, primitive contracts, memo support and asymptotic envelopes. Trace each selected declaration to its imported premises. For Lax62, distinguish the general refinement stack from example functional-specification backlog. For arlib, inspect `ExactRealizes` and its RAM interpretation. For L14, inspect the cost-preserving translation and allocation model.

**Deliver:** a row per capability with exact source revision/declaration/type, claim level, reusable fragment, license, build status, compatibility issue and decision. Include negative findings scoped to searched modules. Add contemporary overlapping work found in maintainers' public channels.

**Acceptance:** each proposed implementation target is classified as direct reuse, adapter, genuine new statement, local algorithm work or unresolved. No global absence claim follows from a search miss.

## W02. Actual lookup operation inventory

**Own:** a source/model inventory and a narrowly scoped experimental module/package; no source rewrite.

**Read:** `verified_ordered_core/src/lib.rs`, generated extraction modules, `Rust/MemoizedOrderedSolver.lean`, `Paper2004/MemoizedDynamicProgram.lean` and their exact types.

**Task:** map each lookup/scan operation to the candidate resource model, including structural equality, loop control, early exit and returned representation. Identify translation primitives and the independent postcondition. State source size and failure premises.

**Deliver:** an exact proposed lookup bound, one actual loop bound, a source-event correspondence design and an extra-scan counterexample. Identify what is proved versus trusted at the source boundary.

**Acceptance:** the first pilot uses existing source rather than a surrogate algorithm and has no unknown operation priced at zero.

## W03. Competing backend pilots

The [executed G1 decision](evidence/g1-backend-decision.md) now compares all
three over the same generated source fragment and selects native Std.WP at C2.
The optional arlib/Lax interpreters have exact value/cost correspondence and
source-mutation rejection. Their RAM/IR realization obligations and W06-C3
remain open; no machine/source claim is inferred from the comparison.

**Own:** separate standalone/worktree experiments for the same W02 task. Each candidate has its own manifest and no main-repository dependency changes.

**Task:** instantiate the task in arlib, in the selected timed-refinement route, and through a thin `Std.WP`/cost adapter. Keep input domain, independent result specification and operation model comparable. Audit the new order-maintenance stack for a reusable translation component before writing one. Add Iris only for a demonstrated ownership need.

**Deliver:** buildable theorem/consumer artifacts, printed assumptions, omitted-operation failure, imports and compatibility report. Compare semantic coverage before proof-script size.

**Acceptance:** the integration owner can select a route using concrete evidence. Failed candidates report the exact blocker and retained reusable pieces. No framework-wide ranking is required.

## W04. Checked core statements

**Depends on:** selected semantic boundary from W01--W03.

**Own:** proposed generic statement file and statement review, isolated from completed production theorems while any proof placeholders remain.

**Task:** translate D1--D4 and D7--D8 into checked signatures using actual backend types and declarations. Include multi-root/warm-cache/repeated-request cases. Make totality and error semantics explicit. Produce a small typed client showing that a local recurrence and cache contract fit.

**Deliver:** checked signatures, theorem dependency graph, provenance classification and false-neighbor examples. Record any substantive change to the mathematical dossiers rather than weakening a statement.

**Acceptance:** no undefined placeholder interface conceals the main proof; every future premise is either upstream, an earlier target, or a concrete local obligation.

## W05. Generic memo theorem and two clients

**Executed partial delivery:** [native memo core and exact scope](evidence/memo-interpreter.md).
Interpreter correctness/once-only expansion/exact requests and finite envelopes
compile; list/array contracts and the LV body fit. The
[LV follow-up](evidence/memo-lv-correspondence.md) closes exact old-evaluator
value/table/counter correspondence and warm D-product bounds. The
[unrelated minimum-edit client](evidence/memo-edit-distance.md) now also
compiles with both representations. The [whole-run follow-up](evidence/memo-work-envelopes.md)
now derives primitive budgets and weighted/native-WP envelopes with cache setup.
Remaining work is local input/body/key/materialization cost and source realization,
including the named W06-C3 requirements.
W04's other interfaces and W06-C3 remain retained work.

**Depends on:** W04; source adapter work continues alongside.

**Own:** MEM-01/02/03 and generic tests/examples; local LV adapter in an agreed path.

**Task:** prove the interpreter's correctness, cache preservation, unique expansion, exact request accounting and priced resource bound. Recover the existing LV counters and prove edit-distance or another approved unrelated instance. Instantiate two representation contracts.

**Deliver:** public API, exact and envelope corollaries, two clients and a comparison of removed versus retained client proof work.

**Acceptance:** no tree-specific import in generic modules; no assumed global runtime bound; no loss of existing small-input constants; changed cache representation changes the cost without changing the combinatorial proof.

## W06. Source-to-cost bridge

[Caller preservation and recursive addressed dispatch](evidence/memo-evaluator-recursive-calls.md)
now retain stored caller bytes through guarded actions, selected control,
parsed entry and cleanup, and compose the actual recursive choice/evaluator/
maximum dispatcher at unchanged source costs. Native choice readiness is
discharged; evaluator refinement retains explicit input readiness and
physical success. A cold empty evaluator runs completely. A real nonempty
cache-hit path exposes the next lifetime gap: local 6 remains initialized
after its last use and the current guard blocks moving its borrowed table.
Interpret active loan endings, then finish universal readiness/success,
exclusive transfer, dynamic regions/destructors and the remaining public
core/wrappers/resources/G3. W06-C3 and the full planning goal stay open.
The 3,956-job build, all 43 Lean suites, native WP, nine Python tests and
1,055-endpoint axiom audit pass. Shared statement inspection covers 1,225 unique
declarations from six seeds with no unknown references.


[Calling control, parsed entry and checked return cleanup](evidence/memo-evaluator-calling-entry.md)
now compose the existing helper call step with the shared switch/return engine. Callees receive
the actual post-argument activation and suspended stack. Selected-path input
readiness, source outcomes/full costs and caller validity are checked; cleanup
rejects remaining owners or escaping output/caller references and retires all
remaining bounded stack roots. Actual parsed choice retains its native tie rule
and complete cost through entry and cleanup. Recursive program dispatch, whole-
run protected caller preservation, universal readiness/physical success and
global exclusive ownership/dynamic region/destructor composition remain open,
then public maximum/wrappers/resources/G3. W06-C3 and the full goal stay open.
The 3,951-job build, all 41 Lean suites, native WP, nine Python tests and
1,030-endpoint axiom audit pass. Shared statement inspection covers 1,124 unique
declarations from five seeds with no unknown references.

[Concrete helper calls in the mixed world](evidence/memo-evaluator-helper-calls.md)
now execute six existing ordinary helpers and both intrinsics over actual stack/
Box prefixes. Output metadata comes from concrete readback; one-pass caller
argument moves, retained contexts and result storage preserve source costs and
caller resources. Native argument/fuel readiness discharges the local callee
contracts. Wiring this step into control/recursive entry, choice/evaluator/
maximum service, all-path readiness/check success and global ownership/storage/
region/destructor closure remain required, then public core/wrappers/resources/
G3. W06-C3 and the full planning goal stay open.
The 3,946-job build, all 40 Lean suites, native WP, nine Python tests and
1,007-endpoint axiom audit pass. Shared statement inspection covers 914 unique
declarations with no unknown references.

[Addressed switches, return packets and actual choice](evidence/memo-evaluator-addressed-control.md)
now read concrete retained tags after partial moves, execute boolean routing and
early returns through the shared source-control engine, and preserve exact
source results/costs and active/caller/packet validity. The actual choice bridge
reuses the checked source body and native tie rule. Ordinary/intrinsic calls,
universal physical check success, global exclusive transfer and callee storage/
region/destructor closure remain required, then public core/wrappers/resources/
G3. W06-C3 and the full planning goal stay open.
The 3,937-job build, all 39 Lean suites, native WP, nine Python tests and
962-endpoint axiom audit pass. Shared statement inspection covers 920 unique
declarations with no unknown references.

[Initial activations and executable storage/drop actions](evidence/memo-evaluator-storage-actions.md)
now construct argument frames from parsed local counts, derive storage/drop
contexts and compose successful non-call sequences with actual source execution
and unchanged complete costs. Drop protects stack roots as well as unique,
classified Box owners; reopening a local gets fresh storage. Calls, switches/
returns, actual branch check success, global owner/spatial and dynamic region/
destructor composition remain required, then public core/wrappers/resources/G3.
W06-C3 and the full planning goal stay open.
The 3,933-job build, all 38 Lean suites, native WP, nine Python tests and
949-endpoint axiom audit pass. Shared statement inspection covers 456 unique
declarations with no unknown references.

[Computed frame resources and assignment](evidence/memo-evaluator-derived-inventories.md)
now derive complete finite read/owner/loan inventories from actual roots/masks,
extract remaining contexts and preserve suspended caller inventories. Assignment
computes its own guards and post-RHS context while executing the RHS once, with
actual source/cost/frame correspondence. Initial/control/callee, exclusive owner/
spatial and dynamic region/destructor traces remain required, then public core/
wrappers/resources/G3. W06-C3 and the full planning goal stay open.
The 3,929-job build, all 37 Lean suites, native WP, nine Python tests and
929-endpoint axiom audit pass. Shared statement inspection covers 313 unique
declarations with no unknown references.

[Executable addressed RHSs and assignment](evidence/memo-evaluator-addressed-rhs.md)
now implement every operand/RHS constructor with actual cells/pointers and
incremental initialization metadata. Forward and reverse simulation preserve
source results/masks and concrete graphs; moves retain partial frames and check
physical root permissions. One-pass guarded assignment computes its RHS graph
and initializes the existing destination at unchanged source cost. Full actual
frame/loan/owner/control/callee and region/destructor traces remain required,
then public core/wrappers/resources/G3. W06-C3 and the full goal stay open.
The 3,925-job build, all 36 Lean suites, native WP, nine Python tests and
888-endpoint axiom audit pass. Shared statement inspection covers 283 unique
declarations with no unknown references.

[Guarded in-place writes and storage lifecycle](evidence/memo-evaluator-frame-writes.md)
now preserve concrete read/owner graphs across unrelated mutations. Actual
scalar assignments update existing stack roots at unchanged costs; storage
markers retain caller resources and reject protected/dead/wrong-class roots.
Storage-dead also handles the actual still-initialized nonowning references,
without losing Box owners. Full RHS/move/context/control/callee traces and
region/destructor composition remain required, then public core/wrappers/
resources/G3. W06-C3 and the full planning goal stay open.
The 3,918-job build, all 35 Lean suites, native WP, nine Python tests and
867-endpoint axiom audit pass. Shared statement inspection covers 245 unique
declarations with no unknown references.

[Addressable local storage and retained reference graphs](evidence/memo-evaluator-local-storage.md)
now give actual source address expressions concrete pointers into initialized
partial locals. Classified stack roots and Box owners are distinct; transitive
shared graphs derive caller read guards. Box creation and guarded destruction
retain the same caller frame and costs. Full addressed execution, initialization/
mutation conflict checking, active/suspended frame traces and dynamic region/
destructor composition remain required, then public core/wrappers/resources/G3.
W06-C3 and the full planning goal stay open.
The 3,914-job build, all 34 Lean suites, native WP, nine Python tests and
830-endpoint axiom audit pass. Shared statement inspection covers 278 unique
declarations with no unknown references.

**Addressed partial primitives:** [moves, Boxes and logical destruction](evidence/memo-evaluator-addressed-partials.md)
now reuse existing heap cells/full representations/footprints with initialized
source masks and complete owner lists. Concrete identities partition on field
moves, Box shells remain, fresh allocation preserves frames, and partial
traversal selects exact owners/work. Actual source move/Box/drop costs compose.
Reuse these primitives and the completed type/region/native/helper certificates.
Next complete addressed operation/control/callee simulation, addressable local
storage, active/suspended caller frames and real loan-derived guarded addresses,
then destructor-instance interpretation and public core/wrappers/resources/G3.
Raw stored-data readback is not liveness; owner separation does not protect
shared targets by itself. Full W06-C3 remains open.
The 3,910-job build, all 33 Lean suites, native WP, nine Python tests and
780-endpoint axiom audit pass. Shared statement inspection covers 275 unique
declarations with no unknown references.


**Recursive evaluator types and regions:** [actual recursive preservation and binding](evidence/memo-evaluator-recursive-typing.md)
now discharge every typed callee contract, including Box/checked add, and retain
scoped source signatures/locals with exhaustive region-use/call-arity checks for
all nine bodies. Actual JSON/native totality composes with independently typed
outputs and unchanged full costs. Do not repeat static/recursive snapshot typing,
region binding, helper proofs or evaluator functional correspondence. Next
addressed partial moves/owners/storage/spatial/local loans/regions/destruction,
including destructor-instance semantics, then public maximum/wrappers/input
policy/global resources/G3. Snapshot preservation and well-bound regions do not
supply dynamic local-loan safety; full W06-C3 remains open.
The 3,904-job build, all 32 Lean suites, native WP, nine Python tests and
734-endpoint axiom audit pass. Shared statement inspection covers 1,046 unique
declaration records with no unknown references.


**Evaluator source types:** [actual declarations and partial-local preservation](evidence/memo-evaluator-source-typing.md)
now check all nine source profiles, both actual Option layouts, complete nested
annotations and static constraints. Partial reads/owned field moves and expanded
operands/expressions/actions preserve independent declared types. Next shared
control induction, typed initial locals and recursive Box/checked-add/ordinary
callee discharge. Then addressed owners/storage/spatial/local loans/regions/live
destruction, public maximum/wrappers/input policy/global resources/G3. Do not
repeat source extraction, the new static certificate, partial-type primitives
or the completed functional evaluator/native correspondence. No full C3 closure.
The 3,898-job build, all 30 Lean suites, native WP, nine Python tests and
706-endpoint axiom audit pass. Shared statement inspection covers 752 unique
declaration records.


**Universal evaluator:** [actual source/native totality](evidence/memo-evaluator-native-totality.md)
now discharges all recursive success/failure/overflow cases for every finite
native query and warm table, retaining exact tables, full callee/local costs and
fuel-independent completed work. The independent consistency/memo refinement is
reused under its original sound-cache/width assumptions. Do not repeat evaluator
functional correspondence, primitive extraction or the seven helper proofs.
Next actual whole-profile types/regions/owners/storage/local borrows/addressed
live destruction, then public maximum, wrappers/input policy/global resources/G3.
No physical allocator or complete W06-C3 claim follows.
The 3,890-job build, all 29 Lean suites, native WP, nine Python tests and
675-endpoint axiom audit pass. Shared statement inspection covers 837 unique
declaration records.


**Evaluator base paths:** [the complete body/base increment](evidence/memo-evaluator-base-paths.md)
now kernel-checks all 113-local control and proves actual-program/native
cache-hit and either-empty-query totality, with arbitrary warm storage and
scores, exact output tables and complete source/helper/drop/call currencies.
Do not re-extract the body or reprove the seven helpers. Next recursive head/
tail and contracted-query cases, both checked-add failures and final choice/
insertion; compose exact native/overflow/table/cost behavior plus whole-profile
types/regions/owners/storage/local borrows/live destruction before core/wrappers/G3.
The 3,881-job build, all 28 Lean suites, native WP, nine Python tests and
645-endpoint axiom audit pass. Shared statement inspection covers 838 unique
declaration records.


**Owned choice:** [actual source/native choice](evidence/memo-owned-choice.md)
now consumes a kernel body certificate, retains the first on equal scores and
charges the losing witness's exact logical destructor work. The native API has
no word/score consistency premise. Reuse it with the preceding six helpers;
whole-evaluator typing/regions/owners/storage/local borrows/live destruction,
functional/error/table/resource correspondence and public core/wrappers/G3
remain required. No physical deallocation or full W06-C3 claim follows.
The 3,877-job build, all 27 Lean suites, native WP, nine Python tests and
634-endpoint axiom audit pass. Shared statement inspection covers 706 records.


**Expanded helper reuse:** [the checked bridge](evidence/memo-evaluator-helper-bridge.md)
identifies all six actual helper bodies with their earlier profiles and transfers
successful runs at identical nesting fuel/full work, with zero new destruction
and solver-call currency. Universal native contracts and completed addressed
owner/storage/spatial/typing/loan/region results compose with the expanded source
program. Do not reprove helper algorithms or their safety traces. Next evaluator
whole-program typing/regions/owners/storage/local borrows/destruction and universal
functional/overflow/table/resource correspondence, then public core/wrappers/G3.
The numeric-width premise is necessary and holds for every native input.
The 3,873-job build, 26 Lean suites, native WP, nine Python tests and
624-endpoint axiom audit pass. Shared statement inspection covers 1,239 records.


**Actual evaluator source follow-up:** [complete profile execution](evidence/memo-evaluator-source-profile.md)
now retains and kernel-reads all nine actual bodies/signatures/bounds/coverage,
including 113 evaluator locals and the public entry point. Partial moves,
scalars/checked add, live drops, tags and metadata use shared control/frontend
semantics; complete work is retained. Actual-program guards cover empty/nonempty
and overflow/table behavior. Next bridge helper refinements and compose whole
program typing/regions/owner/storage/addressed safety and universal functional/
resource correspondence, then separate wrappers/G3. Full W06-C3 stays open.
The 3,865-job build, 25 suites, native WP, nine Python tests, thirteen Rust
tests, full regeneration check and 592-endpoint axiom audit pass.

**Actual evaluator follow-up:** [partial-local foundations](evidence/memo-evaluator-partial-locals.md)
now support projected moves, preserved siblings/Box shells, exact transfer of
declared destructor work, unrelated locals and whole-local destruction. Pinned
inspection confirms these are actual evaluator/wrapper needs. Next consume
these primitives in checked normalization/execution, with scalar/checked-add,
metadata/unreachable control, local addressed borrows and full safety/cost
composition, then core/wrappers. This is not an evaluator source certificate;
W06-C3 remains open. The 3,858-job build, 24 suites, native WP, nine Python tests and
572-endpoint axiom audit pass.

**Memo loan/region follow-up:** [typed shared loans and source-region interpretation](evidence/memo-loan-regions.md)
now compose actual helper runs, parsed scoped declarations and retained-world
lifetime witnesses. Kernel route/type/body/scope checks and fuel induction cover
recursive contracts. Ordinary outputs are reference-free; Box preserves payload
loans. Insertion retains owned-table transfer and aliased key/witness loans.
Native endpoints retain storage/guard/spatial/returned-owner/full-cost results
and all typed caller loans. Next actual evaluator arithmetic, owned-local borrows,
destruction/errors, public core and wrappers. Full W06-C3 remains open; the
scoped model is explicit. The 3,855-job build, 23 suites, native WP, nine Python tests and
552-endpoint axiom audit pass.

**Memo storage follow-up:** [normal allocation/initialization traces](evidence/memo-stack-initialization.md)
now retain distinct live/dead markers and exact actual local declaration counts.
Generic checker soundness and fuel induction cover initialized reads, allocated
writes, moved-empty slots, normal frame closure and all recursive calls. Native
endpoints retain prior source/heap, typing, guard/spatial, returned-owner and
full-cost guarantees. Next dynamic loans/lifetime interpretation for these
helpers, then actual evaluator/core and wrappers. Logical storage alone does
not prove loan validity; W06-C3 remains open. The 3,850-job build, 21 suites, native WP, nine Python tests and
531-endpoint axiom audit pass.

**Memo guard/spatial follow-up:** [recursive intermediate owner traces](evidence/memo-spatial-ownership.md)
now cover clobbers, moved drops, return cleanup and complete owner lists across
locals, temporaries and suspended callers. Insertion uses its owned-table
profile; initial enumeration retains that owner. Kernel checks and fuel induction
discharge actual recursive contracts. Native endpoints retain prior source/heap/
readback/cost/returned-owner guarantees. Next normal storage/initialization and
dynamic loans/lifetimes, then actual evaluator/core and wrappers. `.scope`
owner guards are not storage liveness; W06-C3 remains open.

**Memo typing/scope follow-up:** [actual source certificates and preservation](evidence/memo-source-typing.md)
now check declaration layouts, nested annotations, argument/return prefixes,
static bodies and free/body region scope. Recursive operational type preservation
and ordinary output closure compile for the new helper set. Insertion retains
its owned input and three lifetimes for four value arguments. Shared checkers
and proofs accept explicit callee maps. Next guarded local/storage/spatial and
dynamic loan/lifetime traces, then actual evaluator/core and wrappers. Scope
is not dynamic liveness; W06-C3 remains open.

**Addressed memo follow-up:** [actual heap layouts and owner transfer](evidence/memo-heap-ownership.md)
now realize the certified memo primitives with full source costs and exact
allocation growth. Concatenation owns its fresh output; insertion preserves
the old table cell under its new tail Box. Its complete occurrence ledger adds
all new cells to the old list, preserving multiplicity and external owner
frames. Native typed readback and input inhabitation compile. Next independent
source/static/region checking and intermediate type/guard/storage/spatial/loan
traces for the new helper set, then actual evaluator/core and wrappers. Returned
ownership is not an intermediate trace proof; W06-C3 remains open.

**Memo primitive follow-up:** [actual insertion/concatenation](evidence/memo-source-primitives.md)
now have retained source, kernel normalization, successful native runs,
independent append/prepend and translated-Rust agreement, with explicit copy/
Box events. Existing control semantics/parser are polymorphic in callee targets.
Next extend addressed typing/ownership/storage/loans/regions to those bodies,
then actual evaluator arithmetic, owned-local borrows, losing-candidate drops,
overflow/table returns and one public core. Wrappers, input/error policy and G3
adversaries remain required. Source control alone does not imply heap safety;
W06-C3 stays open.

**Region follow-up:** [scoped lookup erasure](evidence/lookup-region-erasure.md)
checks actual source binders/uses/call arities and retains regional local types.
An independent shared-value interpretation is equivalent to typed loans under
an explicit immutable retained-world lifetime. Both source snapshots pass kernel
certificates; native lookup composes regional recursive traces with all prior
safety/readback/cost results. Next compose actual insertion, concatenation, memo
evaluation/core and wrappers, then input/error policy and G3 adversaries. Keep
the declared source/primitive and compiler/runtime boundaries explicit. D12's
initial source-operation endpoint does not require a whole-compiler proof.
Full W06-C3 remains open; do not duplicate the scoped lookup pilot.

**Shared-loan follow-up:** [typed retained-heap loans](evidence/lookup-shared-loans.md)
now prove actual shared-read validity through source-certified reborrows,
locals/temporaries and recursive calls. Ordinary results are borrow-free;
native lookup composes success, all prior safety and exact source currencies.
Both real programs pass kernel certificates without changing their input domain.
Next address source region/interpretation adequacy, then insertion,
concatenation, memo evaluation/core and wrappers. Dynamic loans are not a full
Rust borrow checker; W06-C3 remains open. Do not duplicate the completed loan
origin/preservation or result-closure proofs.

**Storage follow-up:** [normal local-storage lifetimes](evidence/lookup-stack-storage.md)
now distinguish allocation/deallocation, require initialized reads and allocated
writes, and produce recursive exact-cost traces on completed normal paths.
Both retained bodies and exact local counts pass kernel certificates. Next
address shared-borrow lifetime/source adequacy, then insertion, concatenation,
memo evaluation/core and wrappers. Physical stack addresses and borrow regions
are not modeled; W06-C3 remains open. Do not duplicate completed normal local
storage/initialization checking.

**Spatial follow-up:** [framed intermediate ownership](evidence/lookup-spatial-ownership.md)
now proves duplicate-free complete owned occurrences across live locals,
temporaries and all suspended caller frames for completed normal executions.
Recursive contracts are discharged for both real programs; actual traces retain
complete cost and native-input lookup has composed success/readback/ownership.
Next address stack storage/liveness, borrow/lifetime and official source
adequacy, then memo insertion/concatenation/evaluation and wrappers. W06-C3
remains open; do not duplicate completed intermediate separation.

**Operational typing follow-up:** [successful-run preservation](evidence/lookup-type-preservation.md)
now derives actual primitive/local/result types from the checked constraints.
Recursive call contracts, argument prefixes and generic Box are discharged for
both programs; source composition preserves complete cost. Next establish
intermediate spatial ownership, stack/borrow and official source adequacy.
Preservation is not initialization/progress or ownership uniqueness. W06-C3
remains open; do not duplicate the completed operational typing work.

**Source-type follow-up:** [lifetime-erased type certificates](evidence/lookup-source-typing.md)
now kernel-check actual retained field declarations against independent
`Heap.Shape`, nested annotations, signatures and all ordinary helper bodies'
static constraints in both programs. Next prove operational type preservation
from those constraints and intermediate spatial ownership, then stack/borrow
and official source adequacy. Lifetime regions are erased, and W06-C3 remains
open; do not repeat the completed declaration/annotation work.

**Local-frame follow-up:** [checked frame safety](evidence/lookup-frame-safety.md)
now validates moves, no-owned clobbers, empty moved drops, callee ownership
profiles and return cleanup for every completed normal run, with recursive
callee contracts discharged. Both original/mutant bodies pass and retained
source composition preserves full cost. Spatial ownership, stack/lifetime and
checked typed source adequacy remain open; this does not close W06-C3.

**Returned-ownership follow-up:** [exclusive returned regions](evidence/lookup-return-ownership.md)
now follow from exact generated copy/result-copy/lookup layout proofs. The
complete ownership-occurrence list is duplicate-free, covers every new Box,
has length equal to the allocation counter, and excludes old input cells.
Next prove intermediate frame/reset/move/destruction safety and checked source
typing/adequacy; returned reachability alone does not discharge these.

**Heap follow-up:** [addressed memory realization](evidence/lookup-heap-realization.md)
proves primitive and complete-call simulation, typed first-hit readback, exact
costs and fresh Box-cell growth for the immutable fragment. It constructs input
layouts and allows shared aliases. Next prove unique ownership/frame safety,
owned resets/destruction, JSON field typing and official source adequacy before
extending to memo insertion/evaluation and wrappers. This does not close W06-C3.

**Executed partial delivery:** [kernel-checked source-control certificates](evidence/lookup-source-certificates.md)
now validate both retained lookup JSON extractions against their normalized
programs and preserve complete outcomes/costs at every fuel. The real extra-work
mutant fails the original certificate and comparison allowance. This closes the
external Python control-reifier trust gap for those snapshots in the declared
primitive model. Typed heap/reference/move/Box adequacy, actual memo core and
wrappers remain required; W06-C3 and SRC-01 are not complete.

The [G1 decision](evidence/g1-backend-decision.md#w04w05-boundary-and-named-w06-c3-obligations)
retains a named W06-C3 package: checkable reification/source semantics, typed
heap/shared-reference/move/Box simulation, then the actual memo evaluator/core
and separate wrappers. Native C2 is the selected contract interface, not a
replacement for these adequacy obligations.

**Depends on:** W02/W03; starts before W05 is complete.

**Own:** SRC-01/MEM-04 and narrowly scoped source-generation/interpretation support, coordinated with existing Aeneas workflow.

**Task:** prove the selected event interpretation covers actual source control flow and primitives. Preserve existing functional specifications. Establish erasure separately from cost adequacy. Extend lookup/loop to the memo core, then one explicitly named wrapper.

**Deliver:** reproducible generation, source hashes, correspondence theorem, exact operation bound and explicit unsupported features. Include an extra-work mutation that forces a new resource obligation.

**Acceptance:** a reviewer can identify the exact C2/C3 boundary. A value-only twin proof is reported as incomplete for this assignment, even if it is independently useful.

## W07. Batch/repair abstraction

**Depends on:** stable SUB/WORK interfaces and real implementation inventory.

**Own:** BATCH-01/02 and an independent prepared-state client. Own AMO-03 only after demonstrating its necessity.

**Task:** identify baseline sharing, job occurrences, affected-job partition, workspace lifecycle and local repair contracts. Prove generic event composition and weighted charging. Exercise it with one matching family and one independent shared-work consumer.

**Deliver:** mathematical statement, backend realization, client proofs and a copy-per-job counterexample.

**Acceptance:** no double-spent baseline potential, no omitted restore/copy cost, no specialized matching assumption in the general theorem. Keep the result local if the claimed generality is not exercised.

## W08. Matching and schedule application audit

**Own:** local MATCH/SCHED/APP obligations; do not redesign the generic core during this assignment without an explicit interface proposal.

**Task:** map existing matching correctness endpoints to actual functions; determine the search/data-structure variant; prove or identify rectangular and repair cost obligations. For 2018, identify the implemented regime choice and oriented-table schedule. Preserve signed/forbidden/nonempty semantics.

**Deliver:** source-algorithm correspondence, matcher contracts, schedule producer/rank map, size/degree sum and remaining local proof census.

**Acceptance:** distinguish a paper existence result from the current implementation's result. Missing source optimization or correctness prerequisite remains a named blocker.

## W09. Space and asymptotic adapters

**Depends on:** stable execution/size interfaces and a chosen schedule.

**Own:** SPACE/ASY modules and rolling-row DP client.

**Task:** reuse existing occupancy-profile algebra, establish representation/lifetime link, and compose scratch/new-output peaks. Export uniform pointwise envelopes and Mathlib filter corollaries with explicit admissible domain. Check fixed-width/asymptotic distinctions.

**Acceptance:** no allocation-volume/peak-space confusion; no empty filter; no hidden fixed degree; a new consumer can use the public envelope without unfolding the implementation.

## W10. Independent review and upstream extraction

**Depends on:** two successful generic clients and source pilot.

**Own:** statement/API review report and candidate upstream package/proposal.

**Task:** independently read assumptions and reproduce a small client, rerun the related-work search, coordinate scope with maintainers and extract the smallest complete theory. Follow the actual upstream statement-file format and compile it.

**Deliver:** source/declaration census, reviewed complete roadmap, reproducible examples, precise limitations and placement recommendation.

**Acceptance:** substantial reusable proof content is demonstrated; supporting elementary lemmas are not presented as the main novelty; no experimental alternatives or local campaign backlog remain in the final timeless roadmap.
