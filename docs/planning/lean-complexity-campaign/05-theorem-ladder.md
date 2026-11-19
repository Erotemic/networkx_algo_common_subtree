# 05. The theorem ladder

## 1. Reading the graph

This is a dependency graph, not a claim that each node is a missing theorem. Nodes marked reuse may collapse to an import or a thin specialization. Nodes marked adapter are where an existing result meets this project's representation. Nodes marked generalization are candidate reusable work, pending the source/compatibility experiments. Local applications remain separate from the proposed general library.

The IDs are stable work references; proposed Lean names are in [06](06-theorem-dossiers.md) and [07](07-interfaces-and-proof-experience.md). The mathematical statements in those documents determine scope. The dependency graph alone is not a specification.

```text
Mathlib sums/filters + existing cost/backend interfaces
        |
        +--> execution adequacy --> compositional rules --> subroutine contracts
        |          |                         |
        |          +--> cost simulation -----+--> pinned-source pilot
        |                                            |
        +--> finite work charging                    |
        |       |                                    |
        |       +--> memo uniqueness --> request counts --> priced memo cost
        |       |                                             |
        |       |                              existing evaluator + Rust bridge
        |       |
        |       +--> shared preparation --> repair-family accounting
        |
        +--> potential contracts --> shared-state/branch ownership (when needed)
        |
        +--> schedule readiness --> executed schedule work --> frontier space
        |
        +--> degree/size envelopes --> uniform asymptotic specifications

Local applications combine these with independent tree/matching correctness.
```

A cost model that has not been related to execution can still support useful mathematical results. Mark those C0/C1. The first pilot must also explore the adequacy bridge so the campaign cannot drift indefinitely into disconnected pseudocode.

## 2. Target census

| ID | Result | Kind / current status | Dependencies | First consumer |
|---|---|---|---|---|
| `ALG-01` | Finite sum, cardinality and reindexing API | existing mathematics; reuse_pending_pin_check | - | All work bounds |
| `COST-01` | Event-occurrence pricing and currency exchange | existing/adapted interface; reuse_or_adapter | ALG-01 | Memo lookup and primitive implementations |
| `SEM-01` | Operational resource adequacy | semantic theorem; adapter_pending | COST-01 | Actual lookup/loop pilot |
| `SEM-02` | Compositional total-cost program rules | semantic/API theorem; reuse_or_adapter | SEM-01 | Fold, early exit and recursive body |
| `REF-01` | Cost-aware simulation composition | semantic theorem; reuse_or_adapter | SEM-01, COST-01 | Abstract primitive to concrete event block |
| `REF-02` | Stuttering and termination transfer | semantic theorem; statement_audit_required | REF-01 | Loops with abstractly invisible source work |
| `SUB-01` | Result-size-aware subroutine substitution | interface theorem; adapter_pending | SEM-02, REF-01 | Dictionary and matcher contracts |
| `WORK-01` | Weighted bounded-fiber work charging | mathematical theorem; formulation_proposed | ALG-01, COST-01 | Graph scans and matching repairs |
| `AMO-01` | Finite-trace potential bound | existing mathematical theorem; reuse_or_short_lemma | ALG-01 | Sequential queue and mutable warm starts |
| `AMO-02` | Framed modular potential contracts | semantic/API theorem; adapter_pending | SEM-02, AMO-01, SUB-01 | Composed amortized data structures |
| `AMO-03` | Credit conservation on branching jobs | semantic/mathematical theorem; conditional_design_after_pilot | AMO-02, WORK-01 | Forked persistent computations and sibling instances |
| `MEM-01` | Memo interpreter soundness and unique expansion | semantic theorem; generalization_candidate | SEM-02, ALG-01 | LV2004 and edit distance |
| `MEM-02` | Root-plus-body request accounting | semantic/combinatorial theorem; generalization_candidate | MEM-01, WORK-01 | Multi-root warm-cache DP |
| `MEM-03` | Representation-parametric memo work bound | semantic/interface theorem; generalization_candidate | MEM-02, SUB-01, COST-01 | List and direct-address memo backends |
| `SCHED-01` | Ready schedule correctness | semantic/combinatorial theorem; generalization_candidate | SEM-02, ALG-01 | Tabulation and directed messages |
| `SCHED-02` | Schedule event accounting and batch readiness | semantic theorem; generalization_candidate | SCHED-01, SEM-02, WORK-01 | Two-pass oriented tree evaluation |
| `BATCH-01` | Shared preparation and per-job accounting | semantic/interface theorem; generalization_candidate | SUB-01, WORK-01, SEM-02 | Related matching instances |
| `BATCH-02` | Bounded repair-family work theorem | mathematical/interface theorem; generalization_candidate | BATCH-01, WORK-01 | Deletion-family solver and independent reoptimization |
| `SIZE-01` | Degree-sensitive product-sum envelopes | mathematical theorem; reuse_or_short_lemma | ALG-01, WORK-01 | Tree DP aggregate cost |
| `SPACE-01` | Well-formed occupancy-profile composition | existing/adapted resource theorem; reuse_or_adapter | SEM-01, COST-01 | Allocate/free traces |
| `SPACE-02` | Schedule frontier and representation residency | semantic/combinatorial theorem; generalization_candidate | SPACE-01, SCHED-02 | Rolling DP and oriented tables |
| `ASY-01` | Opaque monotone cost envelopes | interface theorem; adapter_pending | SUB-01, ALG-01 | Stable subroutine specifications |
| `ASY-02` | Admissible-domain uniform big-O transfer | mathematical/interface theorem; reuse_or_adapter | ASY-01, ALG-01 | Readable multivariate end theorems |
| `SRC-01` | Pinned-source event interpretation and adequacy | source-specific semantic bridge; open_local_bridge | SEM-01, REF-01, REF-02, SUB-01 | Actual Rust lookup and scan loop |
| `MEM-04` | Existing evaluator/source memo correspondence | local adapter; open_local_adapter | MEM-03, SRC-01 | Actual owned memo solver |
| `SRC-02` | Wrappers, copies and output-sensitive bounds | source-specific interface bridge; open_local_bridge | SRC-01, SUB-01 | Indexed/token/Python boundary claims |
| `MATCH-01` | Rectangular matcher resource contract | algorithm-specific theorem; open_local_algorithm | SUB-01, SEM-02, AMO-02, SRC-01 | 2016 Lemma 5; 2018 matching prerequisite |
| `MATCH-02` | 2016 deletion-family resource bound | algorithm-specific theorem; open_local_algorithm | MATCH-01, BATCH-02 | 2016 Lemma 6 and family caller |
| `MATCH-03` | 2018 deletion strategy and combined bound | algorithm-specific theorem; open_local_algorithm | MATCH-02, BATCH-02 | 2018 Lemmas 13/14 |
| `APP-01` | LV2004 full specified-model resource theorem | local application; open_application | MEM-04, SRC-02, ASY-02 | Preserve existing operation/comparison endpoints |
| `APP-02` | DKM2016 total specified-model resource theorem | local application; open_application | MATCH-02, SCHED-02, SIZE-01, SRC-02, ASY-02 | Optimized production family schedule |
| `APP-03` | DKM2018 total time and stated-space theorem | local application; open_application | MATCH-03, SCHED-02, SIZE-01, SPACE-02, SRC-02, ASY-02 | Unrooted optimized implementation |


## 3. The first coherent reusable core

The first candidate core consists of COST-01, SEM-01/02, SUB-01, MEM-01/02/03, WORK-01 and the necessary REF/ASY adapters. Existing implementations should discharge as much of it as possible. Its acceptance application is the present 2004 memoized recurrence plus an unrelated dynamic program, not the entire matching engine.

Source pilot SRC-01 runs alongside that core. MEM-04 then connects the existing evaluator and source representation. This ordering prevents the claim "we proved generic memoization" from concealing the fact that the source never uses the certified interpreter or primitive interfaces.

The next coherent extension is BATCH-01/02 with modular potentials and explicit readiness. AMO-03 is selected only if the real implementation requires branching ownership beyond a simple nonduplicating batch ledger. The conditional design question belongs to this campaign plan; a final upstream roadmap must choose and state one complete theory.

SPACE-01/02 has a separate endpoint: abstract residency under a schedule and representation model. A source-level physical-memory claim requires additional proof and is not hidden in APP-03's name.

## 4. Difficulty and contribution classification

| Group | Main difficulty | Expected independent use | Tau Ceti candidate? |
|---|---|---|---|
| ALG-01, COST-01, AMO-01, SIZE-01 | Mostly existing algebra/short consequences | Very broad | Supporting API; insufficient standalone justification |
| SEM/REF/SUB | Sound semantics and compositional refinement without hidden work | Broad program verification | Possible, but inspect and reuse existing stacks first |
| MEM-01/02/03 | Dynamic requests, cache ownership, actual execution and representation costs | DP, memoized symbolic evaluation, acyclic graph computation | Strong candidate after two consumers and exact source audit |
| SCHED/SPACE | Evaluation order, future-use liveness, representation residency | Tabulation, graph messages, rolling arrays | Candidate with a precise complete theory |
| AMO-03, BATCH | Shared state, nonduplicated resources and related-job accounting | Persistent structures, batch optimization, incremental work | Candidate only with nontrivial independent applications |
| SRC | Precise translation/execution boundary | Potentially broad Rust verification | Better coordinated with backend/source-verification maintainers |
| MATCH/APP | Paper and implementation mathematics | Immediate local value | Local unless broader reuse is demonstrated |

The campaign must not advertise the existence of a generic wrapper as a new mathematical theorem. A good outcome may consist largely of audited adapters and a few strong missing results.

## 5. Completion record for each node

A completed node gets: statement source and provenance class; exact Lean declaration; input/error/arithmetic/resource conventions; dependencies; proof without unapproved axioms; compiled consumer; false-neighbor regression example; source/refinement endpoint; and a short account of what the theorem does **not** establish. Every node has an owner during implementation, but ownership is temporary coordination rather than a permanent authorizing gate.
