# Lean complexity campaign: proto-roadmap

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

The highest-value prospective contribution is therefore a **small interoperable layer for memoized and batched dynamic-programming resource proofs, plus the missing source-to-cost connection**, with precise contracts and independently useful applications. The roadmap leaves its implementation backend undecided until the experiments in [09-execution-plan.md](09-execution-plan.md) resolve that decision.

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

## First work package

Run **G0: backend and statement reconnaissance** and **G1: one actual lookup and loop** before starting a broad formalization. Compare arlib, the Lax timed-refinement stack, and an adapter using Lean's existing `Std.WP` machinery on the **same task**. The comparison must include an omitted-operation test, a result specification independent of the instrumented implementation, and the current repository's toolchain. Investigate Iris as the ownership backend if the batch/shared-state contract needs it; do not require a complete Iris port to establish a deterministic scalar-cost pilot.

Then prove a generic memoized-work theorem and use it both for the existing 2004 recurrence and for edit distance or another unrelated dynamic program. Bring source correspondence into that pilot, rather than postponing it until an entire new abstract library exists.

## Meaning of completion

A campaign target is complete only when its statement, semantic model, proof, importable API, and independent consumer agree. A checked inequality for an arbitrarily annotated program is a valid annotation-model theorem, but is not automatically a source-runtime theorem. A functional refinement does not transfer cost. A RAM theorem concerns the specified RAM. A peak-residency theorem does not establish a Rust allocator budget.

The proposed signatures in this directory are **design sketches, not compiled Lean declarations**. This environment had no Lean/Lake executable, so the overlay contains no `Suggested.lean` presented as checked. Signature compilation and dependency compatibility are explicit first-stage deliverables. The detailed mathematical statements and counterexamples are intended to make those deliverables precise.

This is a dated proto-roadmap. It is not a claim of Tau Ceti acceptance, a complete survey of every unpublished development, or a declaration that the proposed theorems are all absent upstream. Each absence or reuse judgment is scoped to inspected evidence.
