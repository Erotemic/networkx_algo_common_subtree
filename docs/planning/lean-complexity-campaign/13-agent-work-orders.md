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
