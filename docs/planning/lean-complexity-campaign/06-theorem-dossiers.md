# 06. Theorem dossiers

## How to use these dossiers

Each dossier fixes a mathematical obligation and an intended proof boundary. Proposed names are API suggestions, not existing Lean declarations. The provenance field distinguishes a direct reusable source construction from a **new campaign formulation** built from several established ideas. No unnumbered generic theorem below should be attributed verbatim to a cited paper.

The first work order must translate these statements into checked signatures in the chosen backend. If a source already has the result, record its declaration and replace the proposed implementation with an adapter. Preserve the statement and counterexample tests.

## D1. Event occurrence accounting and pricing

**Targets:** ALG-01, COST-01.
**Provenance:** existing Mathlib finite algebra; arlib cost exchange [L01--L02]; resource currencies [I03].
**Proposed API:** `work_append`, `work_map_exchange`, `work_le_of_event_prices`.

For a finite list of event occurrences `tau` and a price `p : E -> Nat`, let `W_p(tau)` be its list sum. Prove append composition and monotonicity under pointwise prices. For an implementation map `expand : E -> List F`, if

\[
\forall e\in\tau,\quad W_q(expand(e))\le p(e),
\]

then

\[
W_q(\operatorname{flatMap}(expand,\tau))\le W_p(\tau).
\]

A stateful refinement will supply the particular expansion blocks and their local state-dependent bounds; this simple theorem is the algebraic summation step. For fixed currencies, a nonnegative additive exchange map on finitely supported counts may be more efficient than materializing lists.

**Proof plan.** Use list induction or sum over occurrence indices; derive vector exchange by linearity. Reuse arlib's exchange theorem if its types and exact assumptions match. Avoid introducing a second finitely supported-vector hierarchy.

**False neighbor.** Replacing `tau` by its set of distinct event labels loses repeated work. Ten visits to the same dictionary key are ten requests. Equality of output values gives no information about the event list.

**Acceptance.** One repeated-event example, one state-dependent lookup adapter, and agreement between event-list and count-vector views for a fixed rate. No claim of intrinsic research difficulty for the algebra alone.

## D2. Operational adequacy and total-cost specifications

**Targets:** SEM-01, SEM-02.
**Provenance:** resource-aware semantics [A01, R01, I02]; existing Lean realization/WP candidates [L02, L04--L05].
**Proposed API:** backend-specific `run_adequate`, `totalCost_bind`, `totalCost_if`, `totalCost_fold`.

Fix an operational semantics for a program type and a resource event interpretation. A total-cost specification under precondition `P(x,s)` must imply a terminating allowed outcome and an independent result/state relation `Q(x,s,y,t)`. Every run allowed by that semantics from that input satisfies the specified resource bound. For deterministic semantics, existence plus determinism can establish termination of the unique execution when the big-step/small-step correspondence is adequate. For nondeterminism, additionally prove that every maximal execution terminates in an allowed outcome; one successful execution plus a bound on successful traces does not suffice. These properties must be established or inherited from the backend.

Prove compositional rules from the **definitions of the semantics**. For sequencing, quantify the second specification over every intermediate result/state admitted by the first. For branches, charge the test if the model counts it and use the taken branch. For loops, require the invariant, local resource rule, exit postcondition and a termination argument. A ranking function is logical evidence; its runtime evaluation is charged only if the program computes it.

**Proof plan.** Prefer existing primitive/WP rules. Establish an adequacy theorem once for the selected interpretation. Register sound `@[spec]` lemmas for `vcgen`, or use the backend's existing VCG. Distinguish a partial-correctness WP from a total-correctness or finite-cost WP explicitly.

**False neighbors.** A specification with no possible outputs can trivially bound all successful executions of a diverging program. A top/failure abstract specification may admit anything. `pure (expensive x)` has zero annotation cost but can perform arbitrarily much source work. A loop with a zero-priced body does not terminate merely because its accumulated price is bounded.

**Acceptance.** Actual lookup and an early-exit scan, each proved against independent semantics and a nonzero operation bound; a deliberate omitted primitive must leave an unprovable adequacy obligation. The theorem's axioms and assumptions must be printed and reviewed.

## D3. Cost-aware simulation, composition and stuttering

**Targets:** REF-01, REF-02.
**Provenance:** timed/data refinement [I02--I03]; arlib exact realization [L02]; machine-refinement precedent [R10]. The generalized adapter statement is a campaign formulation.
**Proposed API:** `CostSimulation.trace`, `CostSimulation.comp`, `CostSimulation.total`.

Relate concrete states `c` and abstract states `a` by `R`. Each concrete execution fragment implementing an abstract step must preserve `R` and satisfy a local cost inequality. One useful scalar form is

\[
W_c(\gamma)+\Phi(c',a')
\le \operatorname{budget}(a,\epsilon,a')+\Phi(c,a),
\]

where `gamma` is the actual concrete event block and `epsilon` the corresponding abstract transition. State precisely how complete runs decompose into such blocks. Initialization and finalization are separate blocks with explicit budgets.

Summation gives a concrete run bound from abstract budgets and initial potential. Compose simulations by composing state relations and the local budget transformations. When costs are vectors, require the exchange map to be monotone and additive or prove the corresponding local inequality. For a state-dependent exchange, do not pretend that one fixed linear map suffices.

**Stuttering.** Any sequence of concrete steps corresponding to no abstract step must be controlled. A well-founded rank can justify termination; a finite potential with positive-priced progress can justify a work bound. These are distinct obligations. A proof about finite runs alone does not establish that every concrete run is finite.

**Proof plan.** Induct over concrete block decompositions, not merely over the abstract result value. Reuse exact correspondence as a stronger special case. Keep inequalities when equality would force irrelevant instrumentation detail on clients.

**False neighbors.** A concrete program that recomputes the answer exponentially often remains functionally equivalent to a linear abstract algorithm. An unbounded concrete stuttering loop can simulate zero abstract actions. Per-call overhead `b` paid for `k` calls contributes `k*b`, not one `b`.

**Acceptance.** A refinement where one abstract dictionary lookup expands to several comparisons, a proof that changing the representation changes the bound, and an explicit treatment of source loop control. At least one simulation must preserve an independent output specification as well as costs.

## D4. Result-size-aware and amortized subroutine substitution

**Targets:** SUB-01, AMO-02, ASY-01.
**Provenance:** modular specifications and `specO` in [R01]; resource contracts in [A01, R02, I02].
**Proposed API:** `ResourceSpec.bind`, `ResourceSpec.weakenBudget`, `ResourceSpec.frame`, `AsymptoticSpec`.

A contract for a subroutine specifies a result relation, a relation between input/output sizes, and

\[
C+\Phi_{out}(s')\le B(x,s)+\Phi_{in}(s).
\]

The caller must establish the precondition, provide the potential, and prove the next call's precondition using the returned value and state. If the next budget depends on the output length, an input-size upper bound is valid only through a proved size relation and monotonicity of that budget.

For a framed resource component, show the routine preserves the unrelated state and its potential. A sum of potentials is compositional only when both predicates describe the same actual state decomposition or a justified ownership split. Pairing arbitrary numerical functions is not enough to prove ownership preservation.

To hide implementation constants, package an envelope `b : Size -> Nat` with an execution specification, nonnegativity (automatic for `Nat`), required monotonicity, and a Mathlib asymptotic bound. A client refers to `b` without unfolding its implementation. Do not expose a nonconstructive envelope when downstream executable code needs to evaluate it; separate logical specification use from runtime scheduling.

**Proof plan.** Compose local inequalities using the intermediate potential exactly once. Derive a finite-trace bound as a consequence of the program rule. Add pointwise weakening and finite-sum rules before writing automation.

**False neighbor.** A linear routine can return an exponentially encoded object under an abstract oracle model; composing a linear-in-output consumer is not automatically linear in the original input. Sharing a stored potential across two callers spends it twice unless the contract allows a split.

**Acceptance.** A dictionary lookup/insert sequence and a two-stack queue client. Then an independent client substitutes a different primitive implementation without editing its combinatorial state-count proof.

## D5. Finite-trace potential and branching-credit conservation

**Targets:** AMO-01, AMO-03.
**Provenance:** classical amortization [A06], mechanized treatments [I05, R02], persistent/debit reasoning [R05]. The finite branching-ledger interface below is a campaign formulation.

### Sequential statement

For states `s_0,...,s_m`, nonnegative costs `c_i`, budgets `b_i`, and nonnegative potential `Phi`, assume

\[
c_i+\Phi(s_{i+1})\le b_i+\Phi(s_i)
\quad (0\le i<m).
\]

Then

\[
\sum_{i<m}c_i+\Phi(s_m)
\le\sum_{i<m}b_i+\Phi(s_0).
\]

Prove this by addition/induction without truncated natural subtraction. An integer/rational potential variant may require a lower bound and a changed conclusion; do not generalize by dropping nonnegativity.

### Branching statement

For a finite forest of **job occurrences**, every created child has one parent. At each expanded node `v`, require

\[
c(v)+\sum_{u\in children(v)}\Phi(u)
\le b(v)+\Phi(v).
\]

Then total work of expanded nodes plus potential on the remaining frontier is bounded by total injected budgets plus initial-root potential. This is a conservation theorem. It does not authorize duplicating a persistent credit because the underlying immutable data can be shared.

For an execution DAG with shared nodes, first specify unique ownership of credits or assign work to unique forcing/expansion events. The forest theorem cannot be used by giving a shared child its full potential once for every incoming edge.

**Counterexample.** Start with data carrying potential `n`; create `k` logical clones for free; charge each clone's `n`-step scan against that same initial potential. The claimed `O(n+k)` bound conflicts with actual `kn` work. A correct split rule would need enough incoming budget to fund all child potentials, or prove the expensive result is computed once and actually shared.

**Proof plan.** Sum local inequalities and cancel each internally transferred potential exactly once. For a separation-logic implementation, derive the ledger rule from ownership assertions; for a simple batch engine, make the ledger an explicit proof invariant.

**Acceptance.** Sequential queue, fork/clone counterexample, and a positive example with a genuinely shared memoized thunk or shared prepared table. If no independent consumer needs the branching extension, retain the counterexample and avoid a large generic debit framework in the first core.

## D6. Weighted finite charging

**Target:** WORK-01.
**Provenance:** finite sum/reindexing algebra [L01], classical charging [A06], difficult applications exemplified by [R03]. The chosen interface is a campaign formulation.
**Proposed API:** `sum_cost_le_sum_capacity` and a bounded-multiplicity corollary.

Let `E` be a finite type of executed event occurrences, `R` a finite resource set, and `owner : E -> R`. Give each event a nonnegative weight `c(e)` and each resource a budget `B(r)`. If for every `r`

\[
\sum_{e:owner(e)=r}c(e)\le B(r),
\]

then

\[
\sum_{e\in E}c(e)\le\sum_{r\in R}B(r).
\]

A useful corollary assumes at most `k(r)` assigned events, each of cost at most `w(r)`, giving `sum_r k(r)w(r)`. More complex local inequalities can be used without forcing all events to have the same weight.

**Proof plan.** Partition the finite occurrence set by fibers and reuse finite-sum interchange. Produce an API for nested/pair-indexed resources and a disjoint-union rule. This theorem is elementary; its value is as a stable interface for nontrivial ownership maps and fiber bounds supplied by algorithms.

**False neighbors.** Assigning an event to a resource that is not in the bounded resource set; counting labels rather than occurrences; proving a per-call bound but forgetting that the resource is reused across calls; bounding fiber cardinality while event weights are unbounded.

**Acceptance.** Graph adjacency scans and a repair loop with heterogeneous event costs. The event-to-resource map must arise from actual run invariants, rather than an assumed theorem restating the global bound.

## D7. Memo interpreter: correctness, expansion uniqueness and request accounting

**Executed follow-up:** [native memo core](evidence/memo-interpreter.md).
`evalRoots_trace_spec`, `roots_request_identity`, `roots_envelope` prove the
native interpreter results. LV evaluator correspondence and the unrelated
client remain open; this does not close the full application acceptance gate.

**Targets:** MEM-01, MEM-02.
**Provenance:** verified memoization [I01]; existing local `memoLcs` proof [P01]. The multi-root, dynamic-request contract is a campaign formulation.
**Proposed API:** `Memo.eval_sound`, `Memo.expands_once`, `Memo.requests_eq`, `Memo.requests_le`.

Fix a key type `K`, a value specification `V(k)`, a well-founded dependency relation `prec`, and a body computation for each key. The body can invoke local primitives and request values for keys smaller under `prec`. Its evaluation terminates given terminating primitive/request operations. It cannot write the memo table directly. Answers satisfying the recursive specifications must make the body's returned value satisfy `V(k)`.

Use an initially sound cache `C_0` with unique keys, no eviction, and sequential evaluation. Let `roots` be a finite list. Let `X` be the finite set of keys whose bodies are expanded during the run, and let `reqs(k)` be the **list of request occurrences in the actual expansion** of `k`.

Required results:

1. Every completed cached value remains sound; every root answer satisfies its specification.
2. Every expanded key was absent initially and is expanded exactly once; the final domain is the initial domain union the expanded keys.
3. Each request, including a cache hit, performs one interpreter lookup under the chosen interpreter definition.
4. The exact request count is
   \[
   Q=|roots|+\sum_{k\in X}|reqs(k)|.
   \]
5. If all expanded keys lie in `S` and every valid body execution makes at most `q(k)` requests, then
   \[
   |X|\le |S\setminus dom(C_0)|,\qquad
   Q\le |roots|+\sum_{k\in S\setminus dom(C_0)}q(k).
   \]

The last sum uses nonnegative upper bounds. If `S` only covers newly expanded reachable keys, state that exactly; arbitrary unrelated warm-cache entries need not lie in `S`.

**Proof plan.** Prove cache monotonicity and soundness jointly by well-founded recursion. Use completed-key insertion and non-reentrant dependencies for uniqueness. Maintain an event partition into root requests, body-generated requests and insertions. Derive counts from that partition, not by adding unconstrained counters to the return value. Adapt the existing single-root `4 * misses + 1` proof as a compatibility corollary.

**False neighbors.** Repeated roots still cause repeated lookups. A fully warm cache has no expansions but can have many requests. Two identical child requests are two calls, even if only one child expansion occurs. Eviction invalidates once-only expansion. A changed environment invalidates cached values. Threading the old table into each sibling loses sharing. A cyclic request graph needs a different semantics.

**Acceptance.** Empty roots, duplicate roots, warm cache, duplicate children, early-exit bodies, and a deliberately broken sibling-cache implementation. Independent clients: LV2004 and edit distance. These tests supplement the theorem; they do not replace its proof.

## D8. Representation-parametric memo cost

**Executed partial follow-up:** [whole-run native work bounds](evidence/memo-work-envelopes.md)
derive actual primitive budgets and weighted envelopes for list/direct/encoded
caches, consumed by LV and edit distance. Complete source/input/body/key and
materialization costs remain retained; the C1 result does not close MEM-04.

**Targets:** MEM-03, MEM-04.
**Provenance:** memoization [I01], modular cost specifications [R01], charged primitives [L02]; new combined campaign statement.
**Proposed API:** `Memo.work_le`, list/direct-address specializations, and local evaluator/source realization.

Partition the actual run's work into initialization/finalization, requests, body-local operations and completed insertions. Let `k_j, sigma_j` identify the key and representation state at lookup occurrence `j`. Let `l(k,sigma)` bound a lookup under its actual input/state contract; `u(k)` bound insertion including stored key/value materialization; `w(k)` bound local body work excluding requested subcomputations and separately charged interpreter actions. Let `h_req` and `h_exp` be any remaining interpreter overheads.

Then prove

\[
C\le C_{init}+C_{finish}
 +\sum_{j<Q}\bigl(h_{req}+l(k_j,\sigma_j)\bigr)
 +\sum_{k\in X}\bigl(h_{exp}+w(k)+u(k)\bigr).
\]

Every event must occur in exactly one category, or deliberate overcounting must be justified as an upper bound. A body-local bound must hold for all valid responses/history states admitted by the interpreter; it cannot assume the eventual global complexity theorem.

For an association list of at most `M` keys and a whole-key equality cost at most `E`, one simple conservative lookup envelope is `a + b*M*(1+E)`. Thus a request bound of order `M` can still give a quadratic table-scan cost, before local word work. For direct addressing, establish dense bounded key IDs and include table initialization plus representation conversion. A logarithmic map needs a proved balancing/lookup cost contract, not a name suggesting balance.

**Proof plan.** Combine D1 event partition, D7 expansion/request counts and SUB-01 primitive bounds. Export both exact expression and convenient monotone envelope. For the local adapter, prove actual `memoLcs` and the certified interpreter agree on values/cache and resource events at the selected boundary. Then connect the relevant source model. Do not substitute an arbitrary new algorithm merely because its final score matches.

**False neighbors.** Key comparisons treated as constant despite structural words; key construction omitted because it occurs before a lookup; allocating an entire state-space table omitted from a sparse reachable-state bound; materializing a witness at every cache entry omitted from a score-only cost.

**Acceptance.** Same combinatorial theorem instantiated with the current list table and a second verified representation. The bounds must differ when the implementations differ. Preserve existing local counter theorems as regression clients.

## D9. Schedules, tabulation and live frontiers

**Targets:** SCHED-01, SCHED-02, SPACE-02.
**Provenance:** bottom-up/space-aware DP [I01]; concrete two-sided scheduling challenge [P03]; heap-space distinction [R11]. The generic scheduled resource theorem is a campaign formulation.
**Proposed API:** `Schedule.ready`, `Schedule.eval_spec`, `Schedule.work_le`, `Schedule.live_bound`.

For finite tasks `S`, each task has dependencies, input/result specifications and a local resource contract. A schedule is an ordered sequence of task executions, reads, writes and explicit retirements. Prove that every read refers to a valid available result, each task execution uses its required predecessors, and outputs satisfy the recursive specification.

A topological permutation is one sufficient schedule for a DAG. More elaborate two-pass or grouped schedules require a phase/rank relation and their own readiness proof. Acyclicity of an abstract graph is not enough when the implementation reads values that were retired or has introduced extra dependencies.

The work theorem sums actual scheduled task/event occurrences. Include construction of the schedule, dependency enumeration, readiness checks that are executed, and table index calculations. A mathematical existence proof of a topological order does not establish an efficient implementation of that order.

For space, define a live set before each scheduled task and a representation size `size(k)` for retained values. If the implementation retires values exactly as specified, has no hidden retained aliases, and has local scratch/output bounds, a conservative peak envelope is

\[
C_{base}+\max_i\left(
 \sum_{k\in LiveBefore(i)}size(k)+Scratch(i)+NewOutput(i)\right).
\]

This covers the transient moment before old values are freed. Add separately retained input, output witnesses and shared prepared structures. A theorem about logical live cells is not physical heap adequacy without a representation proof.

**Proof plan.** Induct over the schedule maintaining value soundness, availability and ownership. Relate `LiveBefore` to last-use positions or future dependency membership. For a rolling array, prove slot reuse only after the previous value's last use. Use SPACE-01 to compose occupancy summaries.

**False neighbors.** Left/right recurrence cases that depend circularly on one another; a topological order with early free; a cache that retains every old value even after logical last use; transient new output larger than the post-step live set; charging only scheduling mathematics while omitting a quadratic source scheduler.

**Acceptance.** A simple DAG evaluator, edit-distance rolling rows with value equality to the full table, and the actual two-pass oriented-tree schedule as a later application. Keep schedule equivalence separate from schedule cost equivalence.

## D10. Shared preparation and bounded repair families

**Targets:** BATCH-01, BATCH-02, MATCH-02/03.
**Provenance:** related matching instances [P02--P03]; graph amortization precedent [R03]; ownership warning [R05]. The batch interface is a campaign formulation.

Given a base instance `B` and a finite family of jobs `J`, preparation produces a certified state `P`. Each job's result is specified independently for its own derived instance. The implementation either threads mutable state from one job to the next, or reads shared `P` and creates bounded private workspaces. Record which case applies.

Prove an event decomposition

\[
C_{family}=C_{prepare}+C_{dispatch}+C_{jobs}+C_{finalize}.
\]

Bound `C_jobs` using local resource contracts and either a valid sequential potential or a weighted bounded-fiber charging map. Let `r` be the **exact cardinality** of the repair-job subset. If each repair costs at most `a(s,t)`, and every other job costs at most `b(s,t)`, derive

\[
C_{family}\le C_{prepare}+C_{dispatch}+r\,a(s,t)+(|J|-r)\,b(s,t)+C_{finalize},
\]

using a precisely defined partition of repair/nonrepair jobs. If only `r <= r_max` is known, use the always-valid bound `r_max*a(s,t) + |J|*b(s,t)`, or prove the additional order and cardinality premises needed to retain the subtraction. For heterogeneous jobs, use the corresponding sums rather than an unjustified maximum.

**Crucial premises:** the baseline representation is actually reused; any copies/resetting are counted; repair eligibility is decidable by the charged dispatch code; previous solutions/potentials remain valid for the derived instance; returned witnesses and restoration work are accounted for. These are local invariants, not an assumption that total cost already has the desired asymptotic order.

**Matching instantiation.** Use existing deletion correctness to identify unaffected cases and the number of affected matched vertices. Prove the actual search/repair implementation's cost and the baseline/scratch lifecycle. The family may branch from one baseline; do not simply telescope the same baseline potential separately in every child.

For 2018, a repair analysis for the small-side regime and the earlier family solver are combined by a parameter regime. The generic library can supply conditional algorithm selection and uniform-envelope composition; the specific inequalities and source dispatch remain local. The `s^4` term must not be discarded globally.

**False neighbors.** Cloning the complete graph/matching for every deletion; resetting a full array inside an ostensibly small repair; counting only changed vertices while scanning all edges; assuming source code selects the cheaper proven strategy when it does not.

**Acceptance.** One matching family plus an independent prepared-state client (for example repeated queries using one preprocessed graph, or a persistent memoized computation). If only matching fits the proposed API, keep the abstraction local rather than forcing a generic package.

## D11. Degree sums and asymptotic specification

**Targets:** SIZE-01, ASY-01/02.
**Provenance:** Mathlib algebra/filters [L01], multivariate specifications [R01], application structure [P03].
**Proposed API:** `sum_pair_degree_envelope`, `ResourceSpec.isBigO`, constrained-parameter corollaries.

For finite index sets and nonnegative `a(u), b(v)` with maxima bounded by `A,B`, elementary sum algebra gives

\[
\sum_{u,v}a(u)b(v)\min(a(u),b(v))
\le \min(A,B)\left(\sum_u a(u)\right)\left(\sum_v b(v)\right).
\]

A tree application then uses the appropriate child-count or degree-sum identity. The graph representation and orientation determine which identity is valid. This is a useful API, but not a difficult standalone theorem.

The asymptotic interface should first have a pointwise bound valid for all admissible inputs, including small cases. Then prove a Mathlib `IsBigO` statement on a specified nontrivial filter. For an input family with parameters `n,m,d,...`, clarify whether constants are uniform in all of them or some are fixed. A single path to infinity can hide bad behavior when another parameter is small; test the intended domain.

A `Size -> Nat` envelope may include `1+...` to cover initialization. To remove the `1`, prove the leading term is eventually bounded below. Casting to real-valued asymptotics must preserve nonnegative quantities and should be handled by reusable lemmas rather than repeated ad hoc coercion scripts.

**False neighbors.** Deriving `O(nm)` only when both variables grow and presenting it as uniform for fixed `n=1`; restricting to an empty admissible filter; fixed-width machine input domains presented as an unbounded asymptotic family; treating a maximum degree that varies with input as a hidden constant.

**Acceptance.** Degree-sensitive tree sum, a deliberately unbalanced parameter family, singleton trees, and a comparison between exact finite bound and the readable asymptotic result. Existing Akra-Bazzi is reused only when a client genuinely has that recurrence shape.

## D12. Source instrumentation and complete wrapper bounds

**Targets:** SRC-01, SRC-02, MEM-04, APP-01/02/03.
**Provenance:** existing Aeneas source relation [L07], execution/compilation examples [L05, R10]; specific Rust event bridge is new campaign work.

Choose a supported source fragment and event model. State the relation among original source, generated Lean, instrumented semantics, and abstract cost model. If instrumentation is a transformation, prove or explicitly trust its soundness at the declared boundary. Hash the original and generated artifacts used by a theorem.

Prove erasure of instrumentation separately from event adequacy. A source correspondence theorem must cover exactly which control-flow and primitive operations produce which events; it cannot merely show the original and instrumented variants return the same answer. Demonstrate that an extra scan or clone changes the cost obligation while leaving the value theorem unchanged.

For wrappers, decompose input validation/conversion, core computation, witness construction, token/index conversion and output assembly. Use output-sensitive bounds where output size dominates. The entire public function's complexity is not the core's complexity unless those stages are bounded and composed.

For fixed-width arithmetic, maintain overflow/domain premises and distinguish arithmetic-operation counts from bit complexity. For floats, a resource bound on operation count can be unconditional in a supported semantics while mathematical optimum correctness depends on additional numerical conditions; present the conjunction with those conditions intact.

**Proof plan.** Begin with the actual lookup and one loop. Then realize the current memo evaluator; only afterward expand to a complete solver and wrapper. Reuse existing functional proofs whenever their premises match. Do not rewrite generated Lean or replace independent specifications to simplify the bridge.

**Acceptance.** Reproducible generation, unchanged independent correctness endpoint, mutation that adds uncounted work rejected by the resource proof, and explicit level C1/C2/C3 in the final theorem documentation. A source-level operation bound is an acceptable first endpoint; a claim about machine instructions requires a separate compiler/machine simulation.

## D13. Matching contracts as local consumers

**Targets:** MATCH-01/02/03.
**Provenance:** exact source statements [P02--P03]; existing local matching specifications.
**Output:** resource specifications around actual matching functions, not a second matching correctness library.

Specify dimensions, allowed/forbidden edges, signed weight semantics, partial/perfect/cardinality-constrained matching mode, and representation state. State whether the cost concerns arithmetic operations, comparisons, memory accesses, or a concrete machine model. Handle zero/one dimensions separately from logarithmic formulas.

Before accepting the rectangular bound, audit whether source code uses a dense scan, heap, priority queue or Bellman-Ford variant. A proof for one data structure cannot be attached to another implementation by output equivalence. Before accepting a deletion-family bound, identify whether both sides' deletions are supported and how index compression, dummy vertices and decoding affect operation counts.

The 2018 combined family bound has a regime split between earlier reuse and an additional repair strategy. Use an explicit algorithm-choice theorem with both correctness/resource contracts and the dispatch cost. A paper existence theorem that there is an algorithm with a bound is weaker than a theorem that the current caller implements that algorithm.

**Acceptance.** A parameterized resource contract whose independent result specification is the existing matching optimum; a client that consumes the contract without opening the Hungarian proof; and adversarial cases with ties, negative weights, forbidden edges, unbalanced dimensions and repeated deletion queries. These cases expose semantic gaps; they are not a substitute for the uniform theorem.
