# Common-subtree verification planning

For the latest stopping point and new-machine commands, read
[RESUME.md](RESUME.md).

This folder contains the intended destination, proof obligations, implementation
work and concrete status for the Lozano-Valiente and Droschinsky formalization
program. Read these in order:

1. **[Verified common-subtree research program](verified_common_subtree_research_program.md)**:
   overall goals, decisions, reusable foundations, Rust/Aeneas architecture,
   implementation inventory, branch/provenance policy and definition of done.
2. **[Lozano-Valiente (2004): verified Rust and Lean](lozano_valiente_2004_verified_rust_lean.md)**:
   ordered rooted trees, contractions, Dyck words, decomposition bounds,
   recurrence/optimality proofs, true leaf counts, runtime model, and Rust
   refinement.
3. **[Pinned source statement crosswalk](paper_statement_crosswalk.md)**: exact
   source editions, mathematical corrections and result-by-result status.
4. **[Droschinsky (2016 and 2018): verified Rust and Lean](droschinsky_2016_2018_verified_rust_lean.md)**:
   weighted unordered isomorphism, weighted partial matching, topological
   embeddings with distance penalties, paper-correct scoring, faster
   algorithms and their verification.
5. **[Mathematical presentations and application study](common_subtree_presentation_and_application_paper.md)**:
   rendered standalone talks and the prospective controlled application pilot.

## Current execution order: usable software first

[Concrete helper calls in the mixed world](lean-complexity-campaign/evidence/memo-evaluator-helper-calls.md)
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

[Addressed switches, return packets and actual choice](lean-complexity-campaign/evidence/memo-evaluator-addressed-control.md)
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

[Initial activations and executable storage/drop actions](lean-complexity-campaign/evidence/memo-evaluator-storage-actions.md)
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

[Computed frame resources and assignment](lean-complexity-campaign/evidence/memo-evaluator-derived-inventories.md)
now derive complete finite read/owner/loan inventories from actual roots/masks,
extract remaining contexts and preserve suspended caller inventories. Assignment
computes its own guards and post-RHS context while executing the RHS once, with
actual source/cost/frame correspondence. Initial/control/callee, exclusive owner/
spatial and dynamic region/destructor traces remain required, then public core/
wrappers/resources/G3. W06-C3 and the full planning goal stay open.
The 3,929-job build, all 37 Lean suites, native WP, nine Python tests and
929-endpoint axiom audit pass. Shared statement inspection covers 313 unique
declarations with no unknown references.

[Executable addressed RHSs and assignment](lean-complexity-campaign/evidence/memo-evaluator-addressed-rhs.md)
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

[Guarded in-place writes and storage lifecycle](lean-complexity-campaign/evidence/memo-evaluator-frame-writes.md)
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

[Addressable local storage and retained reference graphs](lean-complexity-campaign/evidence/memo-evaluator-local-storage.md)
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

[Addressed partial moves and logical destruction](lean-complexity-campaign/evidence/memo-evaluator-addressed-partials.md)
now retain concrete Box identities through owned field moves, fresh allocation
and partial destruction, with typed readback and caller-owner frames. The actual
source move/Box/drop primitives keep their complete costs. Live, duplicate-free
owners and guarded addresses are explicit resources. Whole addressed execution,
caller-local storage/loans and destructor interpretation remain required, then
public core/wrappers and global resources/G3. W06-C3 and the full goal stay open.
The 3,910-job build, all 33 Lean suites, native WP, nine Python tests and
780-endpoint axiom audit pass. Shared statement inspection covers 275 unique
declarations with no unknown references.

[Recursive evaluator typing and source regions](lean-complexity-campaign/evidence/memo-evaluator-recursive-typing.md)
now connect all nine actual type profiles to complete recursive snapshot
execution, with typed initial locals, both intrinsics and deep ordinary-output
closure. Actual scoped signatures/locals, call-region arities and all region-use
positions are kernel checked. Native totality composes with these types at the
same complete costs. Addressed moves/owners/storage/local loans/destruction,
public maximum/wrappers and global resources/G3 remain. Full W06-C3 stays open.
The 3,904-job build, all 32 Lean suites, native WP, nine Python tests and
734-endpoint axiom audit pass. Shared statement inspection covers 1,046 unique
declaration records with no unknown references.

[Actual evaluator source typing](lean-complexity-campaign/evidence/memo-evaluator-source-typing.md)
checks all nine lifetime-erased declaration/control profiles and both actual
Option instances. Independent partial-local typing now preserves reads, owned
field moves, expressions and actions, retaining holes, siblings and Box shells.
Next recursive control/callee typing, then addressed owners/storage/local loans/
regions and live destruction. Public maximum/wrappers and global resource/G3
obligations remain; this does not close W06-C3 or the full planning goal.
The 3,898-job build, all 30 Lean suites, native WP, nine Python tests and
706-endpoint axiom audit pass. Shared statement inspection covers 752 unique
declaration records.


[Universal actual evaluator/native agreement](lean-complexity-campaign/evidence/memo-evaluator-native-totality.md)
now covers every finite native word pair and warm table, all success/overflow/
error paths and exact returned tables. Full costs compose from actual syntax,
destruction and completed callees; sufficient fuel does not change them.
Independent consistency/memo-table results reuse their original sound-cache and
width premises. Whole-profile types/regions/owners/storage/local borrows and
addressed destruction, public core/wrappers and global resources remain next.
This functional milestone does not close W06-C3 or the full planning program.
The 3,890-job build, all 29 Lean suites, native WP, nine Python tests and
675-endpoint axiom audit pass. Shared statement inspection covers 837 unique
declaration records.


[Actual evaluator body and base paths](lean-complexity-campaign/evidence/memo-evaluator-base-paths.md)
now kernel-check the complete 113-local control and prove actual source/native
agreement for every cache hit and every query with either word empty. Arbitrary
warm tables/scores, exact returned table order and complete helper/local costs
are preserved. Recursive pair/pair error/overflow/success/resource composition
and whole-profile typed addressed safety remain next, then public core/wrappers
and G3. This does not close the full planning program or W06-C3.
The 3,881-job build, all 28 Lean suites, native WP, nine Python tests and
645-endpoint axiom audit pass. Shared statement inspection covers 838 unique
declaration records.


[Actual owned score choice](lean-complexity-campaign/evidence/memo-owned-choice.md)
now has a kernel body certificate, universal source/native and first-on-ties
contracts, and exact losing-witness destructor/work counts. For `n` losing-word
pairs, work is `30 + 4n`, visits `4n + 3`, Boxes `2n`; no score/word consistency
is assumed. Addressed live destruction and whole-evaluator/core composition
remain next. This completes another source fragment, with W06-C3 still open.
The 3,877-job build, all 27 Lean suites, native WP, nine Python tests and
634-endpoint axiom audit pass. Shared statement inspection covers 706 records.


The [evaluator helper bridge](lean-complexity-campaign/evidence/memo-evaluator-helper-bridge.md)
kernel-checks identity of all six actual helper bodies with their completed
profiles. Successful recursive execution preserves the same nesting fuel and
complete old cost, with zero additional destruction/solver-call currency.
Native contracts and addressed typing, owner/storage/spatial, loan and region
results are reused. Numeric-width premises are explicit and hold for all native
inputs. Next compose evaluator typing/regions/owners/storage/local borrows and
destruction, functional/overflow/table behavior and resources, then public core
and separate wrappers. Full W06-C3 and remaining planning targets stay open.
The 3,873-job build, 26 Lean suites, native WP, nine Python tests and
624-endpoint axiom audit pass. Shared statement inspection covers 1,239 records.


The [actual evaluator source profile](lean-complexity-campaign/evidence/memo-evaluator-source-profile.md)
now kernel-checks all nine retained bodies, including the 113-local evaluator
and public entry point, and binds source reading to complete profile execution.
Partial moves, scalar/checked-add operations, live drops, metadata and early
returns use the shared control executor/frontend. Native guards exercise actual
empty/nonempty and warm-cache overflow paths. Universal source/native and typed
addressed safety/resource composition remain next. The 3,865-job build, 25 suites, native WP, nine Python tests, thirteen Rust
tests, full regeneration check and 592-endpoint axiom audit pass.

The [actual evaluator/partial-local increment](lean-complexity-campaign/evidence/memo-evaluator-partial-locals.md)
inspects the pinned evaluator/public-entry extraction and proves partial-field
moves with exact transfer of declared destructor work. Siblings and Box shells
remain available; shared referents are readable but cannot be moved through.
Whole-local destruction charges the remaining structure and preserves other
locals. These primitives are not yet consumed by an evaluator source/heap
certificate. Next normalization/execution with arithmetic, metadata, local
borrows and full safety/cost composition. The 3,858-job build, 24 suites, native WP, nine Python tests and
572-endpoint axiom audit pass.

The [memo loan/region proof](lean-complexity-campaign/evidence/memo-loan-regions.md)
now composes actual helper runs with recursive typed shared loans, reference-free
ordinary outputs and parsed region-bearing local annotations. The existing
retained-world valuation and erasure lemmas are reused; insertion retains its
owned table while keys/witness may borrow into it. Native endpoints preserve
all prior source/heap, storage, guarded/spatial, owner-transfer and exact-cost
conclusions plus typed caller loans. Next actual evaluator/core, wrappers,
input/error policy and G3 adversaries. The 3,855-job build, 23 suites, native WP, nine Python tests and
552-endpoint axiom audit pass.

The [memo storage/initialization proof](lean-complexity-campaign/evidence/memo-stack-initialization.md)
retains distinct source allocation/deallocation markers and exact declared local
counts for all four helpers. Generic storage checker soundness and fuel induction
produce recursive traces of actual initialized reads, allocated writes, moved
slots and frame closure with unchanged complete costs. Native totality composes
storage, guarded/spatial traces, typed readback, exact events and insertion's
original table under its new tail Box. Dynamic loans/lifetimes are next, then
actual evaluator/core and wrapper composition. The 3,850-job build, 21 suites, native WP, nine Python tests and
531-endpoint axiom audit pass.

The [memo guard/spatial proof](lean-complexity-campaign/evidence/memo-spatial-ownership.md)
now traces every completed helper call through owner-safe local clobbers,
moved drops, return cleanup and separated complete ownership lists. Insertion's
owned table is retained in initial locals and suspended callers; no all-shared
shortcut is used. Native source/heap endpoints retain full costs, typed readback,
old-table identity and returned ownership. The 3,847-job build, twenty suites and
516-endpoint audit pass. Next storage/initialization and dynamic loan/lifetime
traces, then actual evaluator/core and wrapper composition.

The [memo type/region-scope proof](lean-complexity-campaign/evidence/memo-source-typing.md)
now kernel-checks actual layouts, signatures, nested annotations, static
constraints and free/body region binding for all four memo helpers. Generic
preservation lemmas prove actual operational typing; ordinary outputs are
borrow-free even inside owned payloads. Insertion retains its owned table
argument and has three lifetimes for four value inputs. The 3,842-job build,
nineteen suites and 484-endpoint audit pass. Next guarded local/storage/spatial
and dynamic loan/lifetime traces, then the actual evaluator/core and wrappers.

The [addressed memo primitive proof](lean-complexity-campaign/evidence/memo-heap-ownership.md)
now composes actual source runs with heap execution, independently typed append/
prepend readback and exact allocation growth. Concatenation owns its fresh
output; insertion transfers the original table under a new tail Box and preserves
external owner frames. A complete ledger retains old occurrences and adds each
fresh cell once. The 3,835-job build, eighteen suites and 461-endpoint audit pass.
Next establish intermediate type/storage/owner/loan/region traces for these
functions, then actual evaluator/core and wrapper composition.

The [actual memo primitive bridge](lean-complexity-campaign/evidence/memo-source-primitives.md)
now retains and kernel-normalizes concatenation/insertion source, constructs
successful native-input runs, and proves agreement with independent append/
prepend models and the translated Rust functions. Structural copy/Box counts
are explicit. The shared control semantics/parser now support different callee
sets. The 3,829-job build, seventeen suites, nine Python tests, thirteen ordered
Rust tests, full regeneration and 430-endpoint audit pass. Next extend addressed
safety to these bodies, then the actual memo evaluator/core and wrappers.

The [scoped region-erasure proof](lean-complexity-campaign/evidence/lookup-region-erasure.md)
now checks actual signature/body region binders and call arities, retains
region-bearing local types and proves their erasure equivalent to typed loans
under an explicit immutable retained-world lifetime. Both source snapshots
pass kernel certificates. `lookup_source_total` composes parsed source,
recursive regional traces, native success, safety, ownership, independent
first-hit readback and existing costs. The 3,823-job build, sixteen suites and
414-endpoint axiom audit pass. The next W06-C3 work is actual insertion,
concatenation, memo evaluation/core and wrappers, with the source/runtime trust
boundary explicit.

The [shared-loan proof](lean-complexity-campaign/evidence/lookup-shared-loans.md)
now backs each shared reference with a typed read in the retained caller heap,
checks source borrow routes and preserves loans through all recursive completed
runs. Ordinary results contain no shared references, including inside Boxes.
Native lookup composes this with prior safety/readback/cost theorems. The
3,815-job build, fifteen suites and 382-endpoint audit pass. Source region and
official interpretation adequacy remain W06-C3 work.

The [normal storage-lifetime proof](lean-complexity-campaign/evidence/lookup-stack-storage.md)
now retains distinct allocation/deallocation markers and checks initialized
reads plus allocated writes through every recursive completed normal run.
Both source bodies and exact declaration counts pass kernel certificates.
Native lookup composes storage, spatial/frame safety, typed readback and costs.
The 3,807-job build, fourteen suites and 338-endpoint audit pass. Shared-borrow
lifetimes and official source adequacy remain W06-C3 work.

The [intermediate spatial-ownership proof](lean-complexity-campaign/evidence/lookup-spatial-ownership.md)
now tracks duplicate-free Box occurrences across all live locals, temporaries
and suspended caller frames on completed normal paths. Both real programs have
recursive traces with unchanged complete costs; native lookup composes this
with success, final ownership and typed first-hit readback. The 3,800-job build,
thirteen suites and 304-endpoint audit pass. Stack/borrow/lifetime and official
source adequacy remain W06-C3 work.

The [operational type-preservation proof](lean-complexity-campaign/evidence/lookup-type-preservation.md)
now connects checked static constraints to actual addressed reads, borrows,
moves, aggregates and recursive execution. Both programs preserve typed output
and old memory at every fuel for successful runs, retaining complete source
costs. The 3,794-job build, twelve suites and 252-endpoint audit pass. Spatial
ownership, stack/borrow and official source adequacy remain W06-C3 work.

The [source type certificates](lean-complexity-campaign/evidence/lookup-source-typing.md)
now check lifetime-erased field declarations, signatures, local/nested
annotations and static constraints for all four helpers in both retained
extractions. Independent `Heap.Shape` witnesses and concrete certificates are
kernel checked. The 3,790-job build, eleven suites and 225-endpoint audit pass.
Operational type preservation, spatial ownership and stack/borrow/source
adequacy remain W06-C3 work.

The [checked frame-safety proof](lean-complexity-campaign/evidence/lookup-frame-safety.md)
now covers intermediate local clobbers, moved drops, callee ownership profiles
and return cleanup for both generated programs' completed normal executions.
Its sound analysis and recursive call proof preserve exact execution/cost.
The 3,785-job build, ten suites and 210-endpoint audit pass. Spatial ownership,
checked source typing/lifetimes and official adequacy remain W06-C3 work.

The [returned ownership proof](lean-complexity-campaign/evidence/lookup-return-ownership.md)
connects actual generated lookup/copy execution to exclusive fresh output
regions. Every new Box occurs once in the returned footprint; input Boxes are
not reused as owned output. The 3,779-job build, nine suites and 190-endpoint
audit pass. Intermediate ownership/frame/destruction and typed source adequacy
remain the next W06-C3 obligations.

The [addressed lookup realization](lean-complexity-campaign/evidence/lookup-heap-realization.md)
now preserves typed readback, complete costs and fresh Box-cell growth in an
immutable heap with shared aliases. Lookup succeeds for all represented native
inputs at sufficient fuel; input layouts are constructible. The 3,776-job build,
nine suites and 175-endpoint audit pass. Unique ownership/destruction, stack
lifetimes, checked JSON field typing and official source adequacy remain open.

The [checked source-control certificates](lean-complexity-campaign/evidence/lookup-source-certificates.md)
validate both actual lookup extractions, preserve complete outcomes/costs for
all fuels and reject the real extra-comparison mutant's old certificate/budget.
The 3,770-job build, eight Lean suites and 152-endpoint axiom audit pass.
Typed heap/reference/ownership/Box adequacy and the actual memo core remain
the next W06-C3 obligations; this is a snapshot-primitive control result.

The [whole-run memo work envelopes](lean-complexity-campaign/evidence/memo-work-envelopes.md)
now derive representation budgets from actual local operations and compose
nonuniform finite work bounds, with native Std.WP and two independent clients.
Cold list/dense setup and encoded index work are included. The 3,765-job build,
seven suites and 140-endpoint axiom audit pass. This closes the declared-model
run-budget gap; remaining input/body/key/materialization and source realization
keep MEM-03/W05, W04's other interfaces and W06-C3 partial. Earlier milestones
below retain their checked scope.

The [native memo core](lean-complexity-campaign/evidence/memo-interpreter.md)
now proves sequential interpreter correctness, once-only expansion, exact
root-plus-body request counts and finite warm-cache envelopes. Two counted
cache representations and the existing LV recurrence body fit the interface;
the [reuse audit](lean-complexity-campaign/evidence/memo-statement-audit.md)
records selected upstream declarations and compatibility. The
[LV follow-up](lean-complexity-campaign/evidence/memo-lv-correspondence.md) now
proves exact old-evaluator values/tables/counters and warm D-product bounds.
The 3,757-job build, updated memo suite and 115-endpoint axiom audit pass;
the unchanged suites passed in the preceding core build.

The [independent edit-distance client](lean-complexity-campaign/evidence/memo-edit-distance.md)
now proves minimum-cost edits and consumes the same generic memo theorem with
list/dense caches. The 3,761-job build, new suite and 125-endpoint axiom audit
pass. Dense index conversion and full cache setup are explicitly counted.
W04/W05 remain partial: complete representation work envelopes and other
size/substitution interfaces are open, including local input/body costs.
W06-C3 and the wider program's production/runtime/release/application work
remain open. Earlier dated milestones follow.

The [reified lookup operational pilot](lean-complexity-campaign/evidence/lookup-source-pilot.md)
adds checked instruction accounting and universal first-hit/event correspondence
inside the declared read-only model, plus a compiled extra-work Rust mutation.
All 3,750 main Lean jobs, four example suites and seven frontend regressions
pass. The reifier/reference interpretation remain trusted; full G1 and
SRC-01/C3 are still open.

The [2026-11-16 lookup packet model](lean-complexity-campaign/evidence/lookup-packets.md)
now proves structural comparison/copy/allocation envelopes and erasure to the
actual extracted function results. All 3,744 main Lean jobs and three example
suites pass. The source-event adequacy bridge remains open; this does not
establish Rust runtime bounds or complete G1/SRC-01.

The 2026-11-14 reprioritization supersedes the earlier proof-first sequencing.
Finish public Python/PyO3 algorithm coverage, independent correctness/parity,
and measured performance before substantial remaining proof work. Preserve
all established proofs. Full mathematical, production Rust correspondence and
applicable complexity verification remain blockers for the final verified
release, while development builds and use can proceed. The concise current
inventory and evidence are in [capabilities.md](capabilities.md).

The original-identity affinity isomorphism extension now has independently
specified operational pruning witnesses and complete mathematical optimum
proofs for both parent policies. Its witnesses preserve original order,
parent edges and endpoint uniqueness. The production arena has a conditional
feasibility/readback bridge; full weighted Rust DP/memo/score correspondence
and runtime remain open. All 3,739 main Lean jobs and both example suites pass.
Rust/Python and performance targets are unchanged.

The preceding actual production choice append and materializer milestone has composed source
contracts: old choices remain meaningful, new head/tail assembly is exact, and
bounded stored endpoints produce bounded emitted coordinates. All 3,735 main
Lean jobs, both example suites, 13 ordered-core tests and 234 required-native
installed Python tests pass. Complete production DP/memo/choice provenance,
parent feasibility, optimality and runtime refinement remain open.

The preceding integer-materializer milestone established
a source proof of exact token emission and safe termination from valid
arena/root/output bounds, with 3,732 main Lean jobs and 234 required-native
installed API tests passing at that milestone.
[Source theorem and the small stack-representation check](../../dev/benchmarks/2026-11-14-iso-choice-stack.md).

Production ordered isomorphism now caches scores/choices and reconstructs only
the winner. Rooted calls compute only the level recurrence. All 234 required-native
installed API tests, 13 ordered-core tests and 3,728 Lean jobs pass; the optimized
production score/choice refinement remains open.
[Short timing and memory evidence](../../dev/benchmarks/2026-11-14-ordered-iso-choices.md)
records the improvement without changing backend selection.

The exact matching API now bypasses square assignment for inputs without a
positive edge; its actual-source total-correctness theorem covers that branch.
All 3,728 main Lean jobs and 232 required-native installed Python tests pass.
[Small before/after measurements](../../dev/benchmarks/2026-11-14-exact-nonpositive.md)
record the effect. The preceding proof milestone also justifies the production
float family's transposed occupied-column restriction over exact ordered
arithmetic; actual float source/control-flow and runtime refinement remain open.

Implementation stability comes from exhaustive/differential objectives, independent
witness checks and native tests, plus short representative performance checks.
Use small workloads and about three timed samples during development; accept
some timing variance. Commit coherent implementation milestones before the
long final benchmark campaign. The new [complexity-library reuse audit](lean_complexity_library_reuse_audit_2026_11_14.md)
now has an [executed arlib experiment](../../proofs/experiments/arlib_cost/README.md)
with a proved memo-lookup bridge and operation bound. Its 3,744-job joint build
passes; arlib stays optional and main dependency pins remain unchanged.

## Initial proof scope: arithmetic boundary

Per the author's 2026-11-14 instruction, **IEEE-754 correctness is deliberately
excluded from the initial proof scope**. Prove the mathematical algorithms,
matching, witnesses, optimized schedules and applicable complexity results.
Rust correspondence must state its arithmetic model and any arithmetic
preconditions explicitly. Exact integer-core proofs retain their existing
checked-arithmetic guarantees. Do not identify idealized ordered-ring/real
operations with actual `f64` operations or claim an end-to-end IEEE-754 proof.

Floating-point rounding, numerical stability and overflow correspondence are
not initial proof-completion gates. Keep finite-input, overflow and precision
regressions as software tests. This exclusion does not remove the remaining
algorithmic, witness, production-structure or complexity proof obligations.
The [proof ledger](../../proofs/PROOF_STATUS.md) must distinguish those open
obligations from this intentionally excluded numerical scope. This decision
supersedes earlier planning text listing floating arithmetic equivalence as
required proof work.

Both Droschinsky Rust families and the verified exact assignment/partial
matching cores are now callable through public Python APIs. A fresh installed
wheel passes all 228 tests with native backends mandatory. Independent graph
witness rescoring and exhaustive optimum comparisons are included. Installed
API measurements cover both optimized schedules, matching deletion families,
conversion overhead and independent witness rescoring. See the capability
matrix and benchmark evidence before continuing the remaining ordered
coverage, correctness and optimization tasks.

The ordered isomorphism APIs now expose the existing root-preserving level
state with `rooted=True`, alongside the default general state. Independent
parent-preserving subset enumeration validates both contracts and fractional
affinities. Normal and genuine Rust-only ABI3 wheels are tested; the latter
passes the complete 228-test API suite on each CPython 3.10–3.14.

2018 now uses the fixed-left mapped/skipped schedule and includes the skipped
highest-vertex path case. Independent high-degree/path oracles pass; installed
APIs improve 179× on 32/32 stars and 19–36× on module trees. Directed view IDs
and original edge metadata now remove the remaining core lookup cost. Supplied-path
witness rescoring now passes independent checks and enables complete 512-node
scaling runs; production refinement and formal complexity remain open.
[Implementation and evidence](../../dev/benchmarks/2026-11-14-embedding-schedule.md).

2016 now reuses high-degree right-parent deletion families; exhaustive matching
and graph-witness checks pass. Measured 32/32 chain-versus-star and double-star
speedups are 2.74× and 1.69×. Later choice-table and dense-view changes address module costs; the current
2018 optimized schedule is implemented and measured separately.
[Evidence and assurance boundary](../../dev/benchmarks/2026-11-14-matching-families.md).

Both graph families additionally expose fixed ambient roots and the separate
root-to-root restriction, with original-node witnesses and all existing signed
scoring modes. Independent rooted oracles and 47 native / 199 installed tests
pass, including every host ABI3 runtime. A source-only portable rebuild at
`e272d36` also passes 199 tests on the glibc floor and all five runtimes. [Root contracts and measurements](../../dev/benchmarks/2026-11-14-graph-root-modes.md).

The 2018 API now also accepts positive infinity as the distance penalty,
forbidding skipped vertices under every root policy. Independent enumeration
and both witness formats validate this case; 48 native and 209 installed tests
pass, including each host ABI3 runtime. [Evidence](../../dev/benchmarks/2026-11-14-infinite-penalty.md).

The source-proved structural ordered isomorphism reference is now callable
from both balanced-sequence and NetworkX APIs as `reference-rust`, with
`node_affinity=None` and either root policy. Original-index reconstruction is
independently tested and extracted, but its refinement remains open. All 219
installed tests, 10 ordered-core tests, 3,713 Lean jobs and both Lean example
suites pass. Eight-pair stars are 625× slower than optimized Rust; this explicit
reference stays outside `auto`. [Evidence](../../dev/benchmarks/2026-11-14-ordered-isomorphism-reference.md).

## Verified actual one-path sparse augmentation: 2026-11-14

The actual signed-integer sparse search and checked path flip now have an
end-to-end independent minimum-permutation theorem from a feasible/tight
single-deficit matching and the paper's two-sided numeric invariant:
`Rust.SparseSearch.augment_sparse_permutation_spec`. Original-index readback,
rank/path construction, arithmetic safety and termination are derived. The
compact copied-graph deletion caller is implemented and tested, with projection
and warm-start source refinement still in progress. Full-matrix scans remain
a reference; the published optimized queue/runtime is open.

## Actual token and forest APIs with guided witnesses: 2026-11-14

The flat Boolean Rust API is totally verified with original token readback,
maximum contraction score and exact malformed-input side rejection. The
one-pair-per-vertex forest convention has an independent optimum bridge using
a retained virtual parent. The opt-in Python `impl="verified-rust"` integrates
that core for `node_affinity=None`; its token/NetworkX conversions remain tested
boundaries. Actual guided indexed reconstruction now has complete feasibility
and original-index correctness plus a recorded `2*n+1` witness-call bound.
Earlier reference backtracking is retained separately. Combined memo/copy costs,
optimized dictionaries, isomorphism indices and the paper runtime remain open.

## Verified actual indexed LCBE reference: 2026-11-14

The public Rust indexed contraction solver now returns independently maximum
trees with exact scores and canonical original edge/pair identities in both
inputs. `Rust.IndexedOrderedSolver.maximum_common_embedding_indexed_of_trees`
and `maximum_common_embedding_indexed_indices` prove success, actual original
pair deletions, unique indices in bounds and one pair identity per output edge.
The bound is fewer than 2^32 edges per input. Efficient witness reconstruction,
isomorphism indices and token/NetworkX conversion remain open; the current
reconstruction backtracks and makes no paper runtime claim.

## Verified actual exact assignment API: 2026-11-14

The actual square signed-i64 Rust assignment API now has an end-to-end total
correctness theorem (`Rust.AssignmentEntrypoint.min_cost_assignment_total_spec`).
Admitted matrices return a minimum-cost permutation with exact cost and
feasible/tight exported potentials; other represented inputs return the
specified size/shape rejection. Arithmetic safety and termination are derived
for every actual phase, including empty input. The actual rectangular optional
signed-i64 partial-matching API is also proved by
`Rust.MatchingEntrypoint.max_weight_partial_matching_total_spec`: exact input
indices, unique pair list, independently maximum compatible matching and exact
weight, or prescribed shape/size rejection. Graph/Python integration and
published optimized costs remain open. See
[proof status](../../proofs/PROOF_STATUS.md).

## Verified Rust memoization: 2026-11-14

The actual owned-memo Rust entry point now has a compiled end-to-end optimum
and exact-score theorem (`Rust.MemoizedOrderedSolver.maximum_common_embedding_of_trees`).
Its returned cache equals the numeric memo model after erasing witnesses;
cache keys are unique and bounded by the proved D-product. Both Rust solvers
pass all 38,809 ordered pairs through six edges. The linked-list table has
linear scans and copied witnesses; efficient dictionary/representation cost,
input-index mappings, ordered isomorphism and Python integration remain open.
See [proof status](../../proofs/PROOF_STATUS.md) and
[shape benchmarks](../../dev/benchmarks/2026-11-14-ordered-memo.md).

## Verified Rust ordered reference: 2026-11-14

The maintained Rust core now returns a structural maximum common tree and
exact score. Its Charon/Aeneas-translated entry point is proved correct for
all independent input trees below 2^32 edges each, with representation,
termination and arithmetic safety proofs. The exhaustive Rust oracle checks
all 38,809 pairs through six edges. The initial core is an exponential reference; the verified memoized entry
point is described above. Index mapping, efficient representation costs, Python
conversion and the unordered paper proof chains remain open.

## 2004 proof tranche accepted: 2026-11-14

The operational Lemma 8 recurrence now has a general constructive correctness
proof (`paperCommon_correct`, `paperCommon_tree_correct`), plus a separate
numeric recurrence theorem (`paperLcs_optimum`). Definition 4's least state
family, Lemmas 1--6, Fact 2, corrected actual-leaf bounds and Theorem 1 in
independent tree parameters compile. Theorem 2 is proved for operational
containment. Exact endpoints and all remaining obligations are in the
[paper statement crosswalk](paper_statement_crosswalk.md).

This closes the ordered LCBE mathematical optimum and state-bound chain.
Full implementation cost, input-index witness reconstruction, the distinct
ordered-isomorphism contract and Python integration remain open.
A fresh source-only checkout reproduced the previous full library build.

## Executed progress: 2026-11-14

The full Lean 4.35.0 library now builds in the VM with its nested `.lake`
bind-mounted to ext4. The current evidence and exact theorem names are in
[`proofs/PROOF_STATUS.md`](../../proofs/PROOF_STATUS.md); reproduction and
translation pins are in [`proofs/VERIFICATION.md`](../../proofs/VERIFICATION.md).
The older starting-point table below is historical.

Completed increments:

- Two-way operational contraction/encoding bridge and the printed Definition 2
  counterexample compile; the public endpoint dependency baseline is reviewed.
- An independent executable Lean contraction oracle is proved to return an
  `IsMaximumCommon` tree, with a complete contraction enumeration theorem.
- An executable finite integer-weight partial-matching oracle has a global
  optimality theorem against independently defined feasible matchings.
- Actual Rust source translates with pinned Charon/Aeneas; generated Lean
  builds and a refinement theorem connects the contraction budget to trees.
- The 2018 Python scorer/oracle and Rust reference DP use Definition 4's path
  scoring; both 1.75 discriminator cases pass. Omitted branch-point selections
  are rejected; exhaustive Rust mapping enumeration validates optimal scores
  and returned witnesses on small trees.
- Focused Lean, Rust, regeneration and independent-oracle CI is configured;
  the first remote run remains pending.

Next: paper statement ledgers, D/R/S combinatorics and the 2004 DP optimality
proof, then verified matching/graph recurrences and actual solver extraction.
The exhaustive reference solvers establish baselines, not published running times.

## Starting point as of 2026-11-13 (after reported successful Lean build)

| Priority | Immediate action | Evidence of completion |
| --- | --- | --- |
| 1 | Record the now-passing Lean 4.35.0 foundation build, check theorem axioms, pin the Lake manifest and add Lean CI | Reproducible build from a fresh checkout, accepted theorem inventory and dependency audit |
| 2 | Pin ordered-tree contraction/root conventions and independently enumerate tiny tree contractions | Small examples and oracle agree with mathematically specified embeddings |
| 3 | Prove encoding round trips and both directions of Dyck-word containment/contraction correspondence | Checked independent tree/sequence theorem |
| 4 | Test a minimal Charon/Aeneas-generated Lean function against a mathematical specification | Translated real Rust source, matching toolchain pins and a checked refinement lemma |
| 5 | Specify finite weighted partial matching and independently correct the 2018 paper path scorer | Matching oracle and 2018 edge-label/skipped-path counterexamples pass |

Other paper and implementation work can proceed in parallel **after** its
own prerequisites are met. Do not treat passing source compilation as
completion of the original paper, or correctness of a slow reference DP as
proof of the published optimized running time.

## Relevant files elsewhere in the repository

- `proofs/README.md` and `proofs/PROOF_STATUS.md`: current Lean workspace and
  declaration-level build/assurance state.
- `proofs/SubtreeProofs/Paper2004/`: fresh mathematical Lean source. The old
  versioned proof development is in Git history, not an import dependency.
- `rust/src/lib.rs`: existing optimized ordered balanced-sequence solvers
  (`Solver::emb`, `Solver::iso`) and Python bindings.
- `rust/crates/common_subtree_algorithms/`: Droschinsky Rust reference algorithms,
  matching solver, tests and benchmark drivers.
- `networkx_algo_common_subtree/common_subtree_reference.py`: slow independent
  reference logic for parts of the unordered algorithms; its current 2018
  scorer must be corrected before being a paper-faithful oracle.
- `dev/common_subtree_algorithms_notes.md` and
  `docs/source/common_subtree_correctness.rst`: historical implementation notes;
  the latter's 2018 path-scoring description needs review.

## Updating the plans

When completing a milestone, record the exact checked theorem, file, Rust
entry point (if applicable), command/test evidence, hypotheses, benchmark
configuration and outstanding gaps. Distinguish **authored**, **compiled**,
**proved**, **extracted**, **tested**, and **measured**. Keep paper statements
and corrections in an explicit theorem crosswalk rather than renaming weaker
results after stronger claims.

The program charter holds decisions shared between papers. The individual
paper plans hold their detailed proof and algorithm obligations. Avoid
reintroducing obsolete proof-reset instructions or duplicating an entire
program history inside new subtask plans.

## Native backend parity and migration

See [`backend_parity_and_cython_retirement.md`](backend_parity_and_cython_retirement.md)
for the independent oracle and cross-backend test plan, reproducible
comparative benchmarks, and requirements for replacing Cython as the fallback
with fully verified Rust implementations.
