# 12. Risks and research boundaries

## 1. Active risks

| Risk | Evidence/status | Mitigation and decision trigger |
|---|---|---|
| Rebuilding existing semantics | arlib, Lax62, Std.WP and the 2026 order-maintenance work overlap proposed layers | G0 declaration audit and same-task G1 pilots; redirect to reuse where statements match |
| Using the word verified too broadly | Some artifacts prove executable-twin or model-specific results; source and compiler boundaries differ | Independent specification and model-level labels on every endpoint |
| Deferring source adequacy indefinitely | A cost twin can be functionally equal while omitting arbitrary work | Actual lookup/loop first; negative extra-scan example; no C3 claim from value equality |
| Toolchain migration dominates | Lax62 and other references use different Lean/Mathlib versions | Isolated builds and narrow imports; no baseline upgrade without a compatibility report |
| Generic API assumes the desired bound | A contract can package total work as an unexplained premise | Inspect each premise and require local rather than conclusion-equivalent evidence |
| Wrong operation model | Structural keys, allocation, big integers, output construction and copies are not inherently constant-time | Complete operation inventory and size-aware primitive contracts |
| Misusing fuel | Fuel may bound recursion depth while allowing unbounded aggregate work | Inspect semantics; explicit event/step interpretation [L15] |
| Vacuous totality | Successful-run implication can hold for a diverging/stuck program | Separate totality/progress; all branches for nondeterminism |
| Incorrect sharing | Mutable threads and independent baseline branches require different accounting | Explicit lifecycle and ownership; exact repair-job partition |
| Optimized algorithm differs from source | Source may always choose one matcher or rebuild per deletion | Algorithm-selection/readiness proof before the claimed optimized bound |
| Weak asymptotic domain | Product limits or fixed machine widths can hide excluded inputs | Uniform pointwise envelopes, admissible-domain and nontrivial-filter review |
| Memory theorem overstates its model | Logical live cells differ from physical allocation/residency | Representation/lifetime proof and resource-specific naming |
| Premature abstraction | Every possible effect/resource/model is generalized before a client exists | Deterministic work first; two independent consumers before API stabilization |
| Research census ages | Active 2026 projects can change rapidly | Versioned refresh before backend selection and before submission; record unresolved leads |
| Parallel agents change shared premises | Manifest or interface changes invalidate independent work | Separate worktrees, fixed handoff signatures and one temporary integration owner |
| Planning replaces proof work | A large documentation tree can become an end in itself | Gate reports must contain actual declarations/clients once implementation starts |

## 2. Arithmetic and machine models

Begin with a stated sequential work model. Counting additions is different from bounding the bit cost of additions on arbitrary naturals. A word-RAM theorem must state the word width, address/value bounds and which operations are primitive. A fixed-width Rust type has a finite input universe; asymptotics over unbounded input sizes requires a family of widths or an abstract input family with explicit representability assumptions.

Zero-filled array allocation is a particularly consequential model choice. Some verified machines treat it as one step; others charge each written cell or assume a preallocated memory region [L14]. All can support valid conditional theorems. The application must use the model it actually establishes and include initialization when claiming a different model.

For floating weights, preserve the local correctness assumptions about comparisons and arithmetic. A resource bound for executed floating operations is not a proof that they implement exact real optimization. State numerical correctness and resource claims separately before combining them with the appropriate premises.

## 3. Expected complexity is a separate extension

A hash-table assumption of expected constant lookup needs a probability model, a seed/hash-family distribution, key construction/equality costs, load-factor/resizing analysis and an adversary model. Adaptively chosen keys can invalidate a bound proved for an independent fixed query sequence. Reusing a random seed across jobs requires its own conditional reasoning.

Tachis and ExpIris demonstrate relevant expected-cost methods [R06--R07]. The campaign should initially retain a deterministic or explicitly abstract-dictionary theorem, then add a precise probabilistic adapter if the published expected bound is required. Do not label a random sampling test a proof of expected runtime. Optional stopping and integrability conditions must be discharged when a chosen framework requires them.

## 4. Persistence, laziness and incremental computation

Sequential potentials apply to the state sequence that is actually threaded. A branching persistent data structure can reuse a value while duplicating a naive potential argument. Delayed computation introduces questions of when a thunk is forced, whether its result is memoized and which uses share it. Thunks and Debits and The Memorist Tale address related settings [R05, R08]; their differing semantics should not be merged casually.

The first memo theorem fixes a well-founded dependency relation, a stable input environment and a non-evicting cache. Incremental invalidation, cyclic fixpoints and concurrency require additional validity/liveness protocols. A future incremental build-system application is plausible, but it does not follow merely from the acyclic memo theorem.

## 5. Parallelism and space

Total work is additive across executed operations. Parallel span is the length of a critical dependency path and uses different composition. A list of event counts alone does not establish a span theorem. Parcas is a relevant 2026 reference [R09], outside the first deterministic sequential core.

Peak memory is also nonadditive. A well-formed allocation profile can compose with a net change and a peak; source memory additionally depends on lifetime, aliasing, garbage collection or deallocation, and allocator assumptions. Rocq heap-space developments [R11--R12] and compiler space safety [R13] motivate these boundaries but do not directly supply a Rust allocator proof.

## 6. Compiler and extraction boundaries

A validated source translation, an operational interpreter theorem and an empirical source/backend trace comparison establish different things. Source transformation soundness should be proved when feasible, or explicitly included in the trusted boundary. Benchmarks and differential testing remain valuable diagnostics without being formal refinement evidence [L17].

Certifying extraction with time bounds [R14] is directly relevant to source-to-cost automation. Model-invariance results [R15] explain why some abstract complexity claims are meaningful across machines, but polynomial overhead is insufficient to preserve an exact linear or degree-sensitive bound. Preserve the required strength of the simulation.

Do not build a complete verified Rust compiler as a prerequisite for the first useful result. A restricted, precisely stated source fragment and primitive model can give a valuable C3 theorem. The restriction must be visible to downstream claims.

## 7. Research decisions that may change the campaign

The backend choice may eliminate most of the proposed generic infrastructure work. The memo proof may reveal that source instrumentation is the main reusable gap. The batch proof may turn out to need only a small charging theorem, or may expose a genuine persistent-ownership problem. The optimized matching analysis may require changing the algorithm rather than the proof framework.

Each outcome should change the plan. Preserve the evidence and useful intermediate results, but do not continue a large abstraction program merely because its name is already in the roadmap. The success criterion remains easier, sound, reusable complexity proofs.
