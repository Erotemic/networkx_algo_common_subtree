# 09. Execution plan and decision gates

**Executed 2026-11-16:** [G1 route-selection decision](evidence/g1-backend-decision.md)
is delivered at the explicit C2 boundary after checking the same source fragment
in all three candidates. Native Std.WP is selected for W04/W05. Remaining G0
audit, W06-C3 and application/runtime requirements below remain open; the decision
does not establish source-to-RAM/Rust adequacy.

## 1. Campaign order

The campaign should proceed by demonstrations with explicit acceptance conditions. A gate may conclude that an existing library already solves the problem. That is a successful reuse result. Do not advance merely because a package contains many declarations or a local counter increases.

```text
G0 statement/dependency audit
  -> G1 actual lookup + loop, competing backend pilots
  -> backend decision and checked core signatures
  -> G2 generic memo theorem + LV evaluator + edit distance
  -> G3 complete source-connected memo client
  -> G4 batch/repair API + independent shared-work client
  -> G5 matching families, schedule and space applications
  -> G6 stabilized extraction, review and upstream submission
```

Source correspondence begins in G1, not after G5. G2 and a narrowly scoped G3 source adapter may proceed together after the semantic boundary is fixed. Algorithm-specific correctness work can continue independently, provided it does not import unstable generic internals.

## 2. G0: reproduce the decision evidence

**Inputs:** this directory, the exact uploaded baseline, current repository verification instructions and pinned upstream sources.

**Work:**

1. Reopen all selected upstream declarations and their definitions. Build a declaration-level matrix for arlib `ExactRealizes`/RAM, Lax62 NREST/refinement, CSLib TimeM, Lean `Std.WP`, and the narrow Iris ownership requirements. Inspect the order-maintenance development's reusable cost/translation lemmas [L14] and the certifying extraction approach [R14] before proposing a new source layer. Record commit, file, declaration, type, dependencies and axioms. Distinguish declarations actually imported by a public umbrella from orphaned files.
2. Compile the existing repository unchanged in its supported environment. Preserve its toolchain. Reproduce a minimal selected upstream example in an isolated package at the upstream pin before trying the project pin. Record failures rather than upgrading the main repository until something builds.
3. Inspect the existing source `memo_lookup`, one surrounding loop and generated Lean. Inventory every operation relevant to the declared model. Decide which source fragment the pilot covers and which translation/model assumptions remain trusted.
4. Audit the exact statements of the memoization and time-refinement sources selected for reuse. For a proposed generalization, state the difference from the cited theorem. Retrieve linked artifacts and licenses before copying code.
5. Check Tau Ceti/CSLib/arlib/Iris/Aeneas issues, open proposals and recent releases for overlapping work. A public search result or a registered proposal is a lead; a declaration plus its semantics is usable evidence.

**Outputs:** checked signature worksheet; upstream pin/build matrix; primitive-event inventory; source claim-boundary diagram; first novelty ledger; proposed source-cost route.

**Pass:** a reviewer can identify exactly which infrastructure already exists, which adapters remain, and what the pilot will prove.

**Redirect:** if a direct imported theorem already covers the intended core, replace the implementation assignment with integration and an independent client. If an upstream package fails to build, retain it as reference until the failure is resolved or the statement is reimplemented with justified scope. A failed build is not proof that the mathematical result is absent.

## 3. G1: same actual lookup and loop across candidates

**Program:** the current `verified_ordered_core` lookup and a real scan/loop used by it or its immediate caller. Use the same independent table/result specification, input domain and cost model across candidates. Do not give one candidate a toy list and another the full Rust wrapper.

**Mandatory cases:** missing key, first hit, last hit, empty table, repeated equal keys subject to the actual table invariant, structural key comparison, and early exit. If unique keys are required by the specification, state that premise and test a separate weaker lookup specification rather than misrepresenting duplicates as supported.

**Candidate A:** arlib's charged primitives and exact/inequality realization.

**Candidate B:** Lax62's timed-refinement/IR route, restricted to imports needed by the task.

**Candidate C:** a thin cost-aware adapter using Lean's existing `Std.WP`/`vcgen`, with TimeM or an existing trace representation as the accounting baseline. This is not permission to build an entire new backend.

Iris is a conditional additional candidate when the ownership example cannot be expressed adequately by these interfaces. Record the reason before adding its dependency surface.

**Required theorem package:** independent lookup value/correctness theorem; precise event/step bound; termination and error policy; relationship to pinned generated/source code; an explicit explanation of what execution model is covered. Print the final theorem signatures and their axioms.

**Negative experiment:** add an extra full scan or structural comparison without changing the result. The resource contract must change or a proof obligation must fail. A test harness reporting a larger count is useful supporting evidence, but the acceptance condition is that the old adequacy/bound theorem cannot simply apply unchanged.

**Comparison dimensions:** soundness and model coverage first; then compatibility, reusable primitive coverage, client proof burden, performance of elaboration, dependencies, license and maintainability. Do not reduce this to an arbitrary weighted score that allows a source-adequacy failure to be offset by fewer lines of code.

**Pass:** one chosen route has a source-linked pilot or a sharply bounded remaining source gap, an independent result specification, and reusable composition rules. The decision report names rejected routes and the particular evidence, rather than saying one library is generally superior.

**Stop condition:** do not broaden the campaign if every route produces only a charged twin with value equality. Resolve the cost semantics/source connection or explicitly narrow the initial deliverable to C1/C2 while continuing a named C3 work package. Do not label it a Rust runtime result.

## 4. G2: generic memo work, with two different clients

**Dependencies:** G1 semantic/contract choice; checked MEM-01/02/03 signatures; preserved local correctness specification.

**Work:** prove the chosen request interpreter's value/cache invariants, unique expansion, exact root-plus-body request identity, finite state envelope and representation-parametric cost theorem. Support multiple roots, warm caches and repeated requests. Keep eviction, recursive cycles and concurrency outside the first API.

**Client A:** adapt the existing LV2004 evaluator and recover `memoLcs_counts`, its state bound and its comparison bound as compatibility results. Preserve exact constants and small-input cases.

**Client B:** edit distance with an independent recurrence specification. Add a sparse DAG client if needed to reveal an assumption accidentally tied to a rectangular table or to tree keys.

**Representation experiment:** instantiate one combinatorial proof with the current association list and a second verified representation. Include the second representation's initialization/conversion cost. The theorem should predict a different cost when lookups have a different implementation.

**Pass:** both algorithms use the same semantic memo theorem; neither must assume the total runtime conclusion as a premise. Client-specific work consists of recurrence correctness, closure, termination and local cost facts. Record which pre-existing manual accounting proofs were replaced and which remain.

**Redirect:** if integration forces a new algorithm rather than the current one, document that as a verified alternative implementation. Do not attach its theorem to the old source. If the generic interface requires tree-specific imports, keep it local and revise the boundary before extraction.

## 5. G3: complete source-connected memo client

**Work:** extend the lookup pilot to the actual memo evaluator, then compose one clearly named public core entry point. Establish event adequacy, representation costs, output-size facts and the relevant source/extraction correspondence. Only then include indexed/token/reconstruction wrappers.

A generated instrumentation route must produce original and instrumented functions with a reproducible source relationship. Erasure and functional equality are necessary but not sufficient; prove the instrumentation accounts for the chosen control-flow and primitive semantics. A manually written adapter must expose the corresponding proof obligations just as clearly.

**Pass:** an APP-01 theorem with an exact bound and a readable asymptotic corollary at a declared model level. The report distinguishes the current list-table bound from any faster abstract-dictionary or improved-source result. The independent score/embedding specification remains the same.

**Regression checks:** extra scan/clone, stale cache environment, omitted key comparison, omitted output materialization and an input rejected by a size/overflow guard. No silent changes to generated code or old proof premises.

**Redirect:** if the desired source bridge requires unsupported compiler semantics, publish the C2 interpreter result with that limitation and isolate the compiler/source work. This still has reusable value; it is not completion of the C3 milestone.

## 6. G4: shared preparation and repair families

**Inputs:** actual family implementation and one independent prepared-query or reoptimization client.

**Work:** choose sequential mutation versus branch-from-baseline semantics. Prove preparation correctness, valid state reuse, job dispatch, local repair bounds and complete lifecycle accounting. Use finite weighted charging first when sufficient. Add potentials or branching credit conservation only when their additional strength is exercised.

**Required adversarial case:** a version that copies or resets an entire baseline for every job. The generic contract must expose that cost. It must not certify the optimized family bound based solely on the final matching result.

**Pass:** both clients reuse the batch theorem, with independent local structural arguments. A claim of advanced amortized/shared-state generality needs a nontrivial second argument, beyond summing independent constant-time queries.

**Redirect:** if the only reusable theorem is elementary sum algebra and all interesting reasoning remains matcher-specific, keep the wrapper small. Do not turn it into a separate major roadmap merely to preserve the campaign's original size.

## 7. G5: matching, scheduling and space integration

**Work packages:** rectangular matching cost; 2016 deletion-family cost; 2018 regime selection and family envelope; actual oriented schedule readiness; degree-sensitive sum; occupancy/lifetime proof; complete wrapper composition.

Each package reuses existing correctness declarations where their signatures match. Resource contracts must describe the actual data structures and search variant. A mathematically correct but slower implementation gets its actual bound until changed through a justified refinement.

Run a source-algorithm correspondence review before attempting the final 2018 theorem. Check that the source makes the requisite algorithm choice and follows a valid table schedule. Separate score-only, witness-producing, real/integer-weight and nonempty API statements.

**Pass:** local APP-02/03 results at explicit cost/space levels, together with evidence that the generic interfaces actually simplified their proofs. Independent rolling-row DP exercises the space API without matching-specific assumptions.

**Redirect:** if correctness or source algorithm selection is missing, expose that prerequisite rather than using a runtime theorem to conceal it. Resource proofs can proceed for supported subroutines while the application remains incomplete.

## 8. G6: extract, review and submit

Select the smallest coherent reusable core that passed independent clients. Stabilize names and imports only now. Prepare a complete timeless API with exact sources, supported generalizations, checked suggested signatures and false-neighbor examples. Re-run the related-work search before submission. Coordinate the intended home with maintainers; do not assume Tau Ceti is the right home for every backend adapter.

A local source-specific campaign can continue after the reusable core is submitted. A final upstream roadmap should not inherit this document's exploratory alternatives or tentative optional targets. See [11](11-tauceti-candidate.md).

## 9. Parallel work and integration discipline

Use separate worktrees or standalone packages for backend experiments. Do not let agents independently edit the same manifest, generic contract or generated source. Assign one integration owner for a temporary phase; this is coordination, not a new permanent authority mechanism.

After G1, independent work can proceed on primitive contracts, memo body clients and matching mathematics against fixed signatures. A change to an agreed interface must include the affected client diff and semantic rationale. Keep ordinary proof dependencies visible; avoid process-only tests that count labels or enforce prose as if it were mathematical correctness.

## 10. Gate report template

Every gate report contains: baseline and dependency pins; exact target IDs; source and theorem statements; build commands/results; printed assumptions; client demonstration; adversarial example; source/model boundary; unresolved issues; and the resulting decision. A report may conclude `reuse`, `adapt`, `implement`, `narrow scope`, or `blocked by named prerequisite`. It must not substitute percentages or theorem counts for the unresolved mathematical obligation.
