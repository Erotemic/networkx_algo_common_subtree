# 11. Candidate Tau Ceti roadmap extraction

## 1. Campaign versus upstream roadmap

This directory is a dated campaign specification with competing experiments, application obligations and open decisions. A Tau Ceti submission should be a smaller, coherent mathematical/semantic development whose objects and theorems are fixed. The inspected guidance calls for layered APIs, actual reuse of existing declarations, precise sources, false-neighbor discussion, human review and checked suggested statements [L10].

Do not interpret the project as categorically excluding software semantics: the inspected roadmap guidance permits subjects beyond ordinary Mathlib scope. The right question is whether the selected development is reusable, substantial, well specified and acceptable to maintainers. Aeneas-specific glue and a local matching proof may belong elsewhere even when a general resource theorem is suitable.

## 2. Preferred first candidate

**Working title:** Resource Bounds for Finite Memoized Computations.

**Proposed core:** a complete theory of a well-founded, sequential request interpreter with sound warm caches, multiple root queries, dynamic/repeated dependency requests and representation-parametric work contracts. Its main result connects executed requests and unique expansions to a total priced work bound. It is supported by existing backend semantics and finite combinatorics rather than a new universal programming language.

The candidate should include:

| Layer | Required public result | Dependency/reuse expectation |
|---|---|---|
| Objects and semantics | Keys, independent value relation, request bodies, cache abstraction and interpreter | Reuse the selected backend and existing well-founded recursion |
| Correctness | Successful evaluation meets the independent recurrence relation and preserves cache soundness | Adapt an established memoization construction when suitable |
| Expansion structure | A key absent initially is expanded at most once; initially valid entries need no expansion | Proof about the actual interpreter, not an assumed event property |
| Request accounting | Root occurrences plus requests made by the executed bodies | Preserve multiplicity and warm-cache behavior |
| Resource interpretation | Local work and primitive representation contracts compose into a total bound | Reuse cost algebra/realization; count initialization and finalization |
| Stable clients | LV evaluator plus an unrelated dynamic program, with two representation choices | No tree-specific import in the general development |

The mandatory main statement is the combined MEM-01/02/03 theorem described in dossiers D7-D8. The simple finite-sum corollary alone is not the proposed contribution. Source realization for an arbitrary Rust program is not part of this first generic theorem; a real source-connected client is nevertheless required evidence that its interface is practical.

## 3. Why this could justify a roadmap

The prospective proof difficulty lies in simultaneously handling the interpreter's control flow, cache ownership/soundness, dynamic dependencies, uniqueness of completed expansion, repeated requests and representation-aware resource composition. The published ingredients are memoization refinement [I01], modular resource specifications [R01], resource-aware refinement [I02--I04] and existing Lean cost/semantics implementations [L02--L05, L14].

This combined formulation is a **proposed synthesis**. It must not be attributed as an unnamed theorem to Wimmer-Hu-Nipkow or CFML. The statement audit must identify which ingredients already have an exact upstream declaration, which are adapters, and which require a new proof. If a suitable combined theorem already exists, the contribution becomes an integration/API application rather than a new mathematical roadmap.

Independent use is supported initially by clients, not asserted as an established count of downstream users. Memoized symbolic computation, DAG evaluation and dynamic programming are plausible later consumers. The roadmap should claim demonstrated reuse for the completed examples and explain the other applications as anticipated scope.

## 4. Complete basics for the selected objects

A final submission must specify the basic theory needed to use its objects: cache abstraction and empty/extended-cache laws; valid environment/version; request/body composition; termination premises; result functionality where used; cold and warm evaluation; repeated and multiple roots; trace/count correspondence; monotone work envelopes; and backend realization.

Choose the semantics of failure before writing the statement file. Either the core proves total success under a well-formedness precondition, or it supports explicit outcomes with costed failure. Do not leave a theorem that is vacuous for a diverging or stuck computation. For the first deterministic core, supported successful execution plus an adequate determinism/termination result is sufficient; a nondeterministic extension needs its own universal totality theory.

Document excluded objects precisely: eviction, cache invalidation, recursive cycles, concurrent evaluation, arbitrary shared lazy thunks and unbounded source callbacks are outside this particular theory. These are scope boundaries, not optional unfinished lemmas inside a supposedly complete roadmap.

## 5. Alternative second candidate

A later candidate could address **Resource Accounting for Shared Preparation and Related Jobs**. It should be proposed only after the batch and independent shared-work clients establish that there is substantial reusable proof content beyond finite sums.

The final chosen theory would need a precise ownership model, preparation/job lifecycle, a correctness relation for each derived instance, and either a bounded-fiber charging theorem or a branching-credit theorem with a meaningful semantic connection. It should include all basics for that selected model. Do not submit an open-ended list of possible potentials, lazy semantics, incremental graphs and matching optimizations as one roadmap.

The 2016/2018 matcher-specific repair analyses remain motivating clients until an independent general theorem with evidence of broad use is identified. Their difficulty alone does not justify making the entire matching development a foundational campaign.

## 6. Statement-artifact requirements

Before a real submission, produce the upstream-required statement artifact at the selected exact toolchain. This overlay intentionally does not include a `Suggested.lean` claimed to typecheck.

For every proposed declaration, the statement artifact and prose must record:

* the existing upstream types and declarations it uses;
* its exact input, error, arithmetic, termination and resource conventions;
* the originating theorem/section or explicit synthesis classification;
* a worked instance and a nearby false statement;
* dependency order and expected proof strategy;
* the independent client that exercises its claimed generality.

Compile all suggested declarations, including edge cases and representative uses. A proof placeholder permitted in the roadmap's statement file does not count as completion. Keep it separate from production imports and make its status explicit.

A human reviewer should first check the semantics and statement strength, then a second reviewer should try to instantiate the public API without private implementation knowledge. Kernel checking cannot decide whether the intended theorem was stated.

## 7. Upstream coordination and packaging

Before opening a proposal, search the current roadmap repository, pending contributions, relevant Zulip discussions and the chosen backend's issue tracker. State the intended scope and ask whether an existing effort overlaps. No such maintainer contact is claimed by this overlay.

Choose the home by the resulting contribution: finite algebra/asymptotics may fit Mathlib; general algorithm interfaces may fit CSLib or arlib; ownership logic may fit Iris-Lean; source translation support may fit Aeneas; a complete semantic theory may be proposed to Tau Ceti with maintainer agreement. These choices need not share one repository.

The submitted roadmap should be timeless: remove dated reconnaissance status, local paths, experiment alternatives, optional backlog and instructions to upstream to another library. Keep exact theorem provenance and stable source revisions where they clarify mathematics. Each promised layer must be a selected part of the complete theory.

## 8. Submission readiness test

A candidate is ready when all statements compile, its prerequisites have precise interfaces, at least two distinct clients validate the abstraction, its substantial missing proofs are identified, its source provenance is accurate, and its resource meaning is clear. It is not ready solely because this planning directory is long, the bibliography is large, or a generic namespace exists.

The campaign can succeed without a Tau Ceti submission. Reusing an existing cost/refinement stack and contributing a few strong adapters plus demanding clients may make Lean complexity proofs substantially easier. The destination should follow that evidence.
