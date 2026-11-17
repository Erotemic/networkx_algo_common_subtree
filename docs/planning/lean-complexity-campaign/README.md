# Lean complexity campaign: proto-roadmap

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

[Addressed partial moves and logical destruction](evidence/memo-evaluator-addressed-partials.md)
now retain concrete Box identities through owned field moves, fresh allocation
and partial destruction, with typed readback and caller-owner frames. The actual
source move/Box/drop primitives keep their complete costs. Live, duplicate-free
owners and guarded addresses are explicit resources. Whole addressed execution,
caller-local storage/loans and destructor interpretation remain required, then
public core/wrappers and global resources/G3. W06-C3 and the full goal stay open.
The 3,910-job build, all 33 Lean suites, native WP, nine Python tests and
780-endpoint axiom audit pass. Shared statement inspection covers 275 unique
declarations with no unknown references.


[Recursive evaluator typing and source regions](evidence/memo-evaluator-recursive-typing.md)
now connect all nine actual type profiles to complete recursive snapshot
execution, with typed initial locals, both intrinsics and deep ordinary-output
closure. Actual scoped signatures/locals, call-region arities and all region-use
positions are kernel checked. Native totality composes with these types at the
same complete costs. Addressed moves/owners/storage/local loans/destruction,
public maximum/wrappers and global resources/G3 remain. Full W06-C3 stays open.
The 3,904-job build, all 32 Lean suites, native WP, nine Python tests and
734-endpoint axiom audit pass. Shared statement inspection covers 1,046 unique
declaration records with no unknown references.


[Actual evaluator source typing](evidence/memo-evaluator-source-typing.md) checks
all nine declaration/control profiles and both Option instances. Independent
partial-local reads/moves/expressions/actions preserve declared types, holes,
siblings and Box shells. Recursive control/callee typing and whole addressed
owner/storage/local-loan/region/live-destruction composition remain required,
then public maximum/wrappers and global resources/G3. SRC-01/C3 stays open.
The 3,898-job build, all 30 Lean suites, native WP, nine Python tests and
706-endpoint axiom audit pass. Shared statement inspection covers 752 unique
declaration records.

The [universal evaluator increment](evidence/memo-evaluator-native-totality.md)
now establishes actual source/native totality and every-completed-run refinement
for all native query words and warm tables, including both overflows, propagated
failures and exact tables. Complete local/callee cost composition and sufficient-
fuel stability are checked. Whole-profile typed addressed safety, public core/
wrappers and global resource/G3 obligations remain; SRC-01/C3 is not closed.
The 3,890-job build, all 29 Lean suites, native WP, nine Python tests and
675-endpoint axiom audit pass. Shared statement inspection covers 837 unique
declaration records.


The [actual evaluator body/base increment](evidence/memo-evaluator-base-paths.md)
now kernel-identifies complete 113-local control and proves universal cache-hit
and empty-query source/native paths for arbitrary warm tables, retaining exact
tables, local destruction and full lookup/insertion costs. Recursive pair/pair
paths, whole-profile typed addressed safety, public core/wrappers and G3 remain
required. This is progress toward SRC-01/C3, not a gate closure.
The 3,881-job build, all 28 Lean suites, native WP, nine Python tests and
645-endpoint axiom audit pass. Shared statement inspection covers 838 unique
declaration records.


[Actual owned score choice](evidence/memo-owned-choice.md) now kernel-checks the
complete body, source/native correspondence and first-on-ties behavior with exact
losing-value destruction work. Native words of `n` losing pairs give `30 + 4n`
source steps, `4n + 3` visits and `2n` Boxes in the declared partial-local model.
Addressed live destruction, evaluator/core functional/resource/safety composition
and wrappers/G3 remain open. Seven ordinary helper contracts are now available.
The 3,877-job build, all 27 Lean suites, native WP, nine Python tests and
634-endpoint axiom audit pass. Shared statement inspection covers 706 records.


The [evaluator helper bridge](evidence/memo-evaluator-helper-bridge.md) now
kernel-checks all six helper identities in the actual expanded program and
transfers successful recursive runs, unchanged work and native contracts.
Existing addressed typing/ownership/storage/spatial/loan/region results compose
with the new source runs. Numeric-width assumptions are explicit. The evaluator
itself still needs full typing, local-borrow/destruction and functional/resource
composition, followed by public core/wrappers and G3. This does not close SRC-01/C3.
The 3,873-job build, 26 Lean suites, native WP, nine Python tests and
624-endpoint axiom audit pass. Shared statement inspection covers 1,239 records.


**Evidence date:** 2026-11-14.
**Repository baseline:** `4291e8bd12d693fbb0d1a6a8737ed96c5f6705e3`.
**Status:** research-backed campaign specification; no new Lean theorems or dependency integrations are claimed by this overlay.
**Requested destination:** `docs/planning/lean-complexity-campaign/`.

## Decision

Build a reusable route from **an execution-linked resource specification** to **a structural work bound** to **a readable complexity theorem**. Use the common-subtree algorithms as demanding applications, and unrelated algorithms as tests of generality. Preserve the existing independent mathematical specifications and Rust correctness proofs.

The first investment is an integration and statement audit, followed by a small end-to-end demonstration. It is premature to commission another general-purpose resource monad, separation logic, compiler, or verification-condition generator. Relevant implementations already exist, and several appeared or changed during 2026. In particular:

* Lean 4.35, already used by this repository, ships the experimental `Std.WP` / `vcgen` infrastructure [L04].
* arlib has operation currencies, charged data structures, and **compositional exact correspondence to its own RAM model** [L02]. It supplies more than an annotation monad, but does not automatically certify our Rust execution.
* Lax Archive submission **lax-62**, registered September 2026, contains a Lean timed-refinement stack based on Isabelle's NREST/Autoref/Sepref approach [L05]. Selected source was inspected. Its example documentation explicitly leaves independent functional specifications for two examples unproved. It is an important integration candidate, not a certified replacement for this project's specifications.
* The September 2026 **Iris in Lean** preprint and port provide a serious alternative for resource ownership [L06]. The presence of Iris does not establish that every Rocq time-credit, debit, expected-cost, or space logic is already ported.

The final recent-work pass also found the **October 2026 verified order-maintenance development**, with an explicit RAM and step-preserving translation [L14], and added Rocq certifying extraction/time bounds [R14] to the mandatory source-bridge references. These further narrow any claim that resource refinement is absent.

The highest-value prospective contribution is therefore a **small interoperable layer for memoized and batched dynamic-programming resource proofs, plus the missing source-to-cost connection**, with precise contracts and independently useful applications. The original roadmap left its backend undecided. The [executed G1 comparison](evidence/g1-backend-decision.md) now selects native Std.WP for the next C2 contracts; source/RAM/IR adequacy remains separate work.

## Read in this order

| Document | Purpose |
|---|---|
| [00-charter.md](00-charter.md) | Scope, decisions, contribution test, success criteria |
| [01-repository-baseline.md](01-repository-baseline.md) | What the uploaded repository actually proves and does not prove |
| [02-related-work-census.md](02-related-work-census.md) | Evidence-graded census, including 2026 developments |
| [03-gaps-and-reuse.md](03-gaps-and-reuse.md) | Existing support, integration gaps, proposed development, excluded duplication |
| [04-semantic-architecture.md](04-semantic-architecture.md) | Meanings of cost, semantic boundaries, backend adapters |
| [05-theorem-ladder.md](05-theorem-ladder.md) | Stable target IDs, dependency order, candidate theorem graph |
| [06-theorem-dossiers.md](06-theorem-dossiers.md) | Mathematical statements, assumptions, proof strategies, false neighbors |
| [07-interfaces-and-proof-experience.md](07-interfaces-and-proof-experience.md) | Proposed Lean-facing interfaces and client proof shapes |
| [08-applications-and-obligations.md](08-applications-and-obligations.md) | Exact role of each layer in 2004/2016/2018, plus independent clients |
| [09-execution-plan.md](09-execution-plan.md) | Ordered experiments, deliverables, acceptance and redirection criteria |
| [10-validation-and-review.md](10-validation-and-review.md) | Statement, source, cost, adversarial and integration review |
| [11-tauceti-candidate.md](11-tauceti-candidate.md) | How a small, timeless upstream roadmap would be extracted |
| [12-risks-and-research-boundaries.md](12-risks-and-research-boundaries.md) | Risks, unresolved decisions, separate future research |
| [13-agent-work-orders.md](13-agent-work-orders.md) | Concrete bounded assignments and required handoff evidence |
| [14-bibliography.md](14-bibliography.md) | Citation IDs, URLs, exact locators and evidence limits |
| [APPLY.md](APPLY.md) | Non-destructive overlay application and explicit commit commands |

Machine-readable companions: [sources.json](evidence/sources.json), [targets.json](evidence/targets.json), [repository-observations.json](evidence/repository-observations.json). The [search log](evidence/search-log.md) records the scope and limits of this census. The [validation report](evidence/validation-report.md) describes what was checked for this delivery.

## Executed follow-up

The [actual evaluator source profile](evidence/memo-evaluator-source-profile.md)
now kernel-checks all nine retained bodies, including the 113-local evaluator
and public entry point, and binds source reading to complete profile execution.
Partial moves, scalar/checked-add operations, live drops, metadata and early
returns use the shared control executor/frontend. Native guards exercise actual
empty/nonempty and warm-cache overflow paths. Universal source/native and typed
addressed safety/resource composition remain next. The 3,865-job build, 25 suites, native WP, nine Python tests, thirteen Rust
tests, full regeneration check and 592-endpoint axiom audit pass.

The [actual evaluator/partial-local increment](evidence/memo-evaluator-partial-locals.md)
inspects the pinned evaluator/public-entry extraction and proves partial-field
moves with exact transfer of declared destructor work. Siblings and Box shells
remain available; shared referents are readable but cannot be moved through.
Whole-local destruction charges the remaining structure and preserves other
locals. These primitives are not yet consumed by an evaluator source/heap
certificate. Next normalization/execution with arithmetic, metadata, local
borrows and full safety/cost composition. The 3,858-job build, 24 suites, native WP, nine Python tests and
572-endpoint axiom audit pass.

The [memo loan/region proof](evidence/memo-loan-regions.md)
now composes actual helper runs with recursive typed shared loans, reference-free
ordinary outputs and parsed region-bearing local annotations. The existing
retained-world valuation and erasure lemmas are reused; insertion retains its
owned table while keys/witness may borrow into it. Native endpoints preserve
all prior source/heap, storage, guarded/spatial, owner-transfer and exact-cost
conclusions plus typed caller loans. Next actual evaluator/core, wrappers,
input/error policy and G3 adversaries. The 3,855-job build, 23 suites, native WP, nine Python tests and
552-endpoint axiom audit pass.

The [memo storage/initialization proof](evidence/memo-stack-initialization.md)
retains distinct source allocation/deallocation markers and exact declared local
counts for all four helpers. Generic storage checker soundness and fuel induction
produce recursive traces of actual initialized reads, allocated writes, moved
slots and frame closure with unchanged complete costs. Native totality composes
storage, guarded/spatial traces, typed readback, exact events and insertion's
original table under its new tail Box. Dynamic loans/lifetimes are next, then
actual evaluator/core and wrapper composition. The 3,850-job build, 21 suites, native WP, nine Python tests and
531-endpoint axiom audit pass.

The [memo guard/spatial proof](evidence/memo-spatial-ownership.md)
now traces every completed helper call through owner-safe local clobbers,
moved drops, return cleanup and separated complete ownership lists. Insertion's
owned table is retained in initial locals and suspended callers; no all-shared
shortcut is used. Native source/heap endpoints retain full costs, typed readback,
old-table identity and returned ownership. The 3,847-job build, twenty suites and
516-endpoint audit pass. Next storage/initialization and dynamic loan/lifetime
traces, then actual evaluator/core and wrapper composition.

The [memo type/region-scope proof](evidence/memo-source-typing.md)
now kernel-checks actual layouts, signatures, nested annotations, static
constraints and free/body region binding for all four memo helpers. Generic
preservation lemmas prove actual operational typing; ordinary outputs are
borrow-free even inside owned payloads. Insertion retains its owned table
argument and has three lifetimes for four value inputs. The 3,842-job build,
nineteen suites and 484-endpoint audit pass. Next guarded local/storage/spatial
and dynamic loan/lifetime traces, then the actual evaluator/core and wrappers.

The [addressed memo primitive proof](evidence/memo-heap-ownership.md)
now composes actual source runs with heap execution, independently typed append/
prepend readback and exact allocation growth. Concatenation owns its fresh
output; insertion transfers the original table under a new tail Box and preserves
external owner frames. A complete ledger retains old occurrences and adds each
fresh cell once. The 3,835-job build, eighteen suites and 461-endpoint audit pass.
Next establish intermediate type/storage/owner/loan/region traces for these
functions, then actual evaluator/core and wrapper composition.

The [actual memo primitive bridge](evidence/memo-source-primitives.md)
now retains and kernel-normalizes concatenation/insertion source, constructs
successful native-input runs, and proves agreement with independent append/
prepend models and the translated Rust functions. Structural copy/Box counts
are explicit. The shared control semantics/parser now support different callee
sets. The 3,829-job build, seventeen suites, nine Python tests, thirteen ordered
Rust tests, full regeneration and 430-endpoint audit pass. Next extend addressed
safety to these bodies, then the actual memo evaluator/core and wrappers.

The [scoped region-erasure proof](evidence/lookup-region-erasure.md)
now checks actual signature/body region binders and call arities, retains
region-bearing local types and proves their erasure equivalent to typed loans
under an explicit immutable retained-world lifetime. Both source snapshots
pass kernel certificates. `lookup_source_total` composes parsed source,
recursive regional traces, native success, safety, ownership, independent
first-hit readback and existing costs. The 3,823-job build, sixteen suites and
414-endpoint axiom audit pass. The next W06-C3 work is actual insertion,
concatenation, memo evaluation/core and wrappers, with the source/runtime trust
boundary explicit.

The [stable shared-loan proof](evidence/lookup-shared-loans.md) checks the actual
source borrow routes and retains typed earlier-heap reads through recursive
execution. Ordinary output is borrow-free even inside owned payloads. Native
lookup composes this with storage/spatial/frame safety and exact existing
costs. The 3,815-job build, fifteen suites and 382-endpoint audit pass. Source
region binding and official interpretation adequacy remain W06-C3 work.

The [normal storage-lifetime proof](evidence/lookup-stack-storage.md) retains
distinct source allocation/deallocation and proves initialized reads/allocated
writes through recursive execution. Both real bodies and exact declaration
counts pass kernel certificates; native lookup composes stack/spatial/frame
safety and independent typed readback with unchanged costs. The 3,807-job
build, fourteen suites and 338-endpoint audit pass. Shared-borrow lifetimes and
official source adequacy remain W06-C3 work.

The [intermediate spatial-ownership proof](evidence/lookup-spatial-ownership.md)
now covers simultaneous live locals, temporary values and suspended caller
frames with duplicate-free complete Box occurrence lists. Actual recursive
traces retain full source costs in both programs; native-input lookup composes
success, spatial/frame safety, returned ownership and typed readback. The
3,800-job build, thirteen suites and 304-endpoint audit pass. Stack/borrow and
official source adequacy remain W06-C3 work.

The [operational type-preservation proof](evidence/lookup-type-preservation.md)
connects checked source constraints to the addressed primitives/control and
discharges recursive typed callee contracts, including generic Box, for both
programs at every fuel. Complete source costs and allocation growth survive
composition. The 3,794-job build, twelve suites and 252-endpoint audit pass.
Spatial ownership, stack/borrow and official source adequacy remain open.

The [source type certificates](evidence/lookup-source-typing.md) kernel-check
the retained field layouts, lifetime-erased signatures/nested annotations and
all four helpers' static constraints for both actual extractions. Parsed fields
agree with independent `Heap.Shape`. The 3,790-job build, eleven suites and
225-endpoint audit pass. Operational type preservation, spatial ownership,
stack/borrow and official source adequacy remain open.

The [intermediate frame-safety certificates](evidence/lookup-frame-safety.md)
prove that completed lookup/copy executions reset/overwrite only non-owning or
empty locals, respect callee ownership profiles and clean up returns. Both real
bodies pass; soundness and recursive call safety preserve actual complete
execution/cost. Spatial ownership and typed source/lifetime adequacy remain
W06-C3 requirements, alongside the memo core and wrappers.

The [exclusive returned ownership proof](evidence/lookup-return-ownership.md)
strengthens addressed lookup with exact cell/heap layouts and duplicate-free
ownership-occurrence accounting. Every fresh Box is returned exactly once;
input Boxes cannot be owned by the output. Intermediate frame/reset/destruction,
stack lifetime and official source-adequacy obligations remain W06-C3 work.

The [addressed lookup memory realization](evidence/lookup-heap-realization.md)
now constructs sufficient-fuel heap executions with typed first-hit readback,
shared aliases, complete source costs, old-memory preservation and fresh
Box-allocation growth. Input layouts exist for all native values. Unique
ownership/destruction, stack lifetimes, JSON field signatures and official
source adequacy remain W06-C3 work, followed by the actual memo core/wrappers.

The [kernel-checked source-control certificates](evidence/lookup-source-certificates.md)
check retained original/mutant lookup JSON and preserve complete execution/cost
at all fuels. They remove Python control-reifier trust for those snapshots and
reject the mutant's old certificate/comparison budget. Typed heap/ownership/
reference/Box and complete memo-core adequacy remain W06-C3 obligations.

The [whole-run memo work envelopes](evidence/memo-work-envelopes.md) prove local
primitive budgets along actual evaluation, then derive weighted finite bounds
and native Std.WP. Both independent clients consume the theorem; cold list and
dense setup are included. The 3,765-job build, seven suites and 140-endpoint
axiom audit pass. Remaining local input/body/key/materialization and source
realization retain MEM-03/W05, W04's other interfaces and W06-C3. These are C1
declared-event costs. Earlier dated milestones follow.

The [independent edit-distance client](evidence/memo-edit-distance.md) now adds
an attained minimum-cost edit specification and list/dense implementations of
the same bounded-index body. Generic correctness/once-only expansion and warm
multi-root envelopes are reused. The 3,761-job build, new suite and 125-endpoint
axiom audit pass. W05's complete representation work envelopes and retained
local input/body/key costs remain open, along with W04's other interfaces and
W06-C3. This is C1, not source/runtime completion.

The [checked native memo core](evidence/memo-interpreter.md) proves actual
sequential evaluation, cache preservation, unique expansion, exact requests
and closed finite warm-cache envelopes. Two counted cache representations and
the existing LV recurrence body fit; the [reuse audit](evidence/memo-statement-audit.md)
records selected upstream declarations. The [LV follow-up](evidence/memo-lv-correspondence.md)
now proves exact old-evaluator values/tables/counters and warm D-product bounds.
W04/W05 remain partial: unrelated client, complete representation envelopes and
remaining size/substitution interfaces are open. This is C1, not source/runtime.
The 3,757-job build, updated memo suite and 115-endpoint axiom audit pass. Earlier milestones below retain their then-current scope.

The [G1 backend decision](evidence/g1-backend-decision.md) compares the same
four generated functions in native WP, charged arlib and Lax62 NREST. All three
preserve successful operational values/costs and reject the compiled source
mutation's old comparison budget. Native Std.WP is selected for the next C2
memo interfaces; remaining G0 audit and W06-C3 source/heap/reification obligations
remain open. This is not generic memo or application runtime completion.

The [charged arlib source interpreter](evidence/lookup-arlib-source-pilot.md)
proves exact successful value and six-currency correspondence for the same
generated bodies as the native WP pilot, with all four contracts and rejection
of the compiled source mutation's old comparison budget. The optional build
passes. Lax62, the G1 decision, RAM realization and SRC-01/C3 remain open.

The [native Std.WP adapter](evidence/lookup-native-wp.md) compiles successful-run
WP contracts for all four existing source-model functions, sequential cost
threading, and rejection of the compiled extra-comparison mutation's old
contract. It is the native W03 leg at the established C2 boundary; competing
adapters, G1 route selection and SRC-01/C3 remain open.

The [reified lookup operational pilot](evidence/lookup-source-pilot.md) adds
execution-linked instruction bounds and exact packet correspondence inside a
read-only operational model, with a compiled Rust mutation. Its reifier and
source interpretation remain trusted. The 3,750-job library build, four Lean
example suites and seven frontend regressions pass. This is bounded C2
progress; SRC-01/C3 and the full G1 route-selection gate remain open.

The [G0/W02 follow-up](evidence/executed-g0-w02.md) records actual declaration
inspection, narrow upstream compilation, a checked Std.WP worksheet, an
omitted-scan counterexample and the source-operation inventory at `0cdd643`.
G0 remains partial; G1 and the actual Rust-to-cost bridge remain open. Existing
arlib mathematics is reused rather than recreated. The main toolchain and
production algorithms remain fixed.

## Original first work package and current next step

The comparison below has now produced the scoped C2 decision linked above.
Next are W05's remaining local input/body/key/materialization cost contracts
and W06-C3 source realization, with W04's other interfaces and the
named W06-C3 work retained.
The original G0/G1 requirements remain recorded here; source adequacy has not
been waived.

Run **G0: backend and statement reconnaissance** and **G1: one actual lookup and loop** before starting a broad formalization. Compare arlib, the Lax timed-refinement stack, and an adapter using Lean's existing `Std.WP` machinery on the **same task**. The comparison must include an omitted-operation test, a result specification independent of the instrumented implementation, and the current repository's toolchain. Investigate Iris as the ownership backend if the batch/shared-state contract needs it; do not require a complete Iris port to establish a deterministic scalar-cost pilot.

Then prove a generic memoized-work theorem and use it both for the existing 2004 recurrence and for edit distance or another unrelated dynamic program. Bring source correspondence into that pilot, rather than postponing it until an entire new abstract library exists.

## Meaning of completion

A campaign target is complete only when its statement, semantic model, proof, importable API, and independent consumer agree. A checked inequality for an arbitrarily annotated program is a valid annotation-model theorem, but is not automatically a source-runtime theorem. A functional refinement does not transfer cost. A RAM theorem concerns the specified RAM. A peak-residency theorem does not establish a Rust allocator budget.

The original proposed signatures remain **design sketches** unless an executed
report links their checked declarations. The initial overlay had no Lean/Lake
executable; subsequent reports record the actual pinned builds and exact scope.
The new memo core addresses D7 and part of D8; it does not silently turn every
proposal into a checked result.

This is a dated proto-roadmap. It is not a claim of Tau Ceti acceptance, a complete survey of every unpublished development, or a declaration that the proposed theorems are all absent upstream. Each absence or reuse judgment is scoped to inspected evidence.
