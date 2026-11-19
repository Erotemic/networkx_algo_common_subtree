# 08. Application obligations and independent reuse

## 1. How the application map is used

A generic theorem is justified by the local proof work it removes and by structurally different consumers. This document specifies those consumers and the mathematical work that remains local. It does not claim the current Rust implementations already have the paper's optimized cost behavior.

Repository references below are relative to the uploaded baseline identified in [01](01-repository-baseline.md). Existing proof-status reports are evidence of that baseline; no Lean or Rust build was rerun for this overlay. The paper crosswalk remains authoritative for the project's existing statement distinctions, including repaired definitions and nonempty/default API modes.

## 2. LV2004: first complete resource client

### Existing material to reuse

Start from `proofs/SubtreeProofs/Paper2004/MemoizedDynamicProgram.lean`. The evaluator already records calls, misses and whole-key comparisons and proves value correctness, table soundness, unique keys, a state bound and a comparison bound. Its logical recurrence and counters are a better first adapter target than an invented alternate implementation.

For trees with edge counts `e_a,e_b`, depths `d_a,d_b` and genuine leaf counts `l_a,l_b`, the existing envelope is

\[
M=(e_a(\min(d_a,l_a)+1)+1)
  (e_b(\min(d_b,l_b)+1)+1).
\]

The existing cold-root theorem yields `calls <= 4*M+1`. Preserve this exact small-input-safe form as a corollary of the general memo theorem. Preserve the association-list comparison theorem as a second corollary. Do not weaken them to an assumed `O(M)` oracle.

### Algorithm-specific premises

The client supplies the corrected decomposition-state closure, the well-founded pair measure, recurrence correctness, the at-most-four request occurrences per expansion and a local word-operation envelope. The generic library supplies unique expansion, total request accounting, primitive substitution and composition.

The current key contains structural Dyck words. Account for key construction, concatenation/slicing where performed, whole-key equality, copied or retained values, cache insertion and output construction. Define the local work function in terms of the actual representation before simplifying it to tree parameters.

### Three distinct dictionary results

| Representation | Additional proof | What the client may claim |
|---|---|---|
| Current association list | Lookup scans and structural equality cost; insertion and value representation | Deterministic bound with the table-scan factor |
| Dense IDs/direct-address table | Correct finite ID encoding, table initialization, key-to-ID cost and bounds | Constant-cost indexed access under the specified word/array model |
| Hash table | Hash/equality cost, load/resizing behavior, distribution/adversary model | A conditional expected/amortized theorem with those hypotheses |

A generic constant-time dictionary assumption is a valid abstract-model corollary when labeled as such. It is not a proof of the production hash table's expected runtime. For the first complete deterministic result, accept the current list representation's bound even if it is slower than the published optimized model. Then change the representation through a certified contract and state the improved theorem separately.

### Source adapter

Start at `rust/crates/verified_ordered_core/src/lib.rs`: `memo_lookup`, then the loop/recursion in `memoized_common_embedding`, then `maximum_common_embedding`. Inspect `proofs/SubtreeProofs/Rust/MemoizedOrderedSolver.lean` for reusable functional and table invariants. The source adapter must relate actual primitive/control-flow events, rather than only the returned score.

The indexed/token APIs and reconstruction routines are separate consumers. Document validation, index conversion, witness reconstruction, cloning and the size of the returned result. A score-only theorem cannot be advertised as a complete Python-facing wrapper theorem. The source pin and generated-module identity are part of every C3 claim.

### Acceptance endpoints

First deliver a generic MEM-03 theorem and the existing evaluator's exact-count corollaries. Then deliver MEM-04 with a declared source-cost boundary. Finally compose the selected representation and wrapper contracts into APP-01. The result documentation must say whether it is deterministic, amortized or expected, and whether it counts abstract requests, arithmetic operations, source events or machine instructions.

## 3. DKM2016: a matcher contract and a family contract

The local project already contains substantial matching recurrence, duality, reduction, deletion and repair correctness. Extend those specifications with resource contracts. Do not introduce a second optimum definition merely to simplify the complexity proof.

The paper obligations tracked locally include a rectangular matching bound of order `k*l*(k+log l)` for the appropriate ordered dimensions, and the related deletion-family bound [P02]. Exact arithmetic, forbidden edges, partial/perfect assignment reductions and negative weights must match the theorem being instantiated. Treat zero dimensions separately or use small-input-safe expressions such as `1+log(max(1,l))` before asymptotic simplification.

### Matcher-local work

Inspect the actual source variant before selecting a theorem: dense row scans, priority-queue operations, alternating-tree search, potential updates, path augmentation and index conversion can have different costs. The cost of a dense scan cannot be replaced by a heap bound because the functions return the same optimal matching.

MATCH-01 should export an independent optimum postcondition and a resource envelope parameterized by dimensions and the chosen primitive model. The tree DP proof must use that contract without unfolding Hungarian search. The existing `MatchingCostSpecification.lean` concerns objective weights, so it supplies correctness ingredients rather than runtime evidence.

### Family-local work

Identify which derived instances are solved, which side is deleted, which deletions leave a matching valid without repair, how many require repair, and whether jobs mutate a single state or branch from a baseline. Record all preparation, dispatch, copy, restore and witness costs.

BATCH-01/02 should supply the resulting composition once the local repair-cost and affected-job bounds are proved. A finite charge map may be sufficient; a potential-based ownership logic should be introduced only if the actual shared-state behavior needs it. The proof must not spend the same baseline potential independently for every deletion.

### Whole-DP work

Prove the actual number and shape of matcher/family invocations, and the readiness of every child result. Then apply finite double-sum and degree identities. A maximum-degree parameter that grows with the input remains explicit in the uniform theorem. Do not turn a per-root bound into an all-roots result by multiplying an unjustified or overly coarse state count.

## 4. DKM2018: schedule and algorithm selection are central

The original paper's section 5.2 combines two matching-family methods. Lemma 14 supplies `O(s^4+s^2*t)` for `s <= t`; the earlier method is used in another parameter regime. The degree-sum argument then yields the stated tree-product/maximum-degree time bound. The paper also identifies a dependency-order difficulty in assembling main and subinstances [P03]. These are separate obligations: a generic memo bound does not supply the regime selection or the required evaluation order.

### The combined family envelope

The local proof must retain both available resource contracts. For the earlier method, use an envelope corresponding to `s*t*(s+log t)`. For the Lemma 14 method, retain the `s^4+s^2*t` expression. Split the domain at the paper's `s` versus `log t` regime, with zero/singleton dimensions handled explicitly.

In the large-`s` regime, `log t <= s` absorbs the earlier logarithmic term. In the small-`s` regime, the general growth bound `(log t)^2 = O(t)` permits absorption of `s^4` into a uniform constant times `s^2*t`. Prove an exact inequality with a fixed base and constant, or an eventual inequality plus explicit finite exceptions. Do not use the false universal inequality `(log t)^2 <= t` for an arbitrary logarithm base and every small `t`.

Then prove the source dispatch executes the method justified for its regime, or prove that its actual single method independently has the combined bound. An existence proof for a fast algorithm cannot certify a caller that always runs a slower method. Computing or approximating the regime test has a cost and a correctness obligation; avoid gratuitous floating-log decisions by proving a suitable integer threshold implementation if needed.

### Scheduling and reuse

The repository's production plan uses oriented views and a left-postorder/right-two-pass schedule. The paper discusses related main/subinstance ordering. These descriptions need a correspondence proof, not an assertion that all two-pass algorithms have the same dependencies.

Define each table cell's independent mathematical meaning. Give each concrete read a producer, phase and rank. Prove availability at the read, invariance under later updates, and any lifetime conditions. For reused maxima, state which entry must be excluded and what tie behavior preserves correctness. A generic ready-schedule theorem then discharges value propagation and sums the actual scheduled events.

The best-two maxima construction and cardinality-constrained matching cases remain local mathematical components. Their resource contracts must include the scans actually performed, including repeated scans in different orientations. Invalid sentinel arithmetic or a score-zero default must not turn an infeasible nonempty case into a valid result.

### Total time and space

With a family envelope of the required form, the reusable degree-product inequality combines with the appropriate tree degree/child-count identities. It is the local adapter's job to prove which measure the source uses. Time remains a claim about the selected resource model.

For space, record the lifetime of the DP tables, family workspaces, input copies, witnesses and recursion stack. A bound on the number of logical cells is insufficient when a cell stores a variable-length witness or all historical versions are retained. Theorem 15's stated table-space result and any integer-weight improvement have separate qualifications [P03]. A source-level occupancy result should be labeled accordingly, without inferring a bound on allocator fragmentation or operating-system residency.

## 5. Independent consumers and what each tests

At least one non-tree dynamic program is required before stabilizing MEM APIs. At least one genuinely different shared-work example is required before stabilizing the batch extension. Merely changing the score type of the same subtree recurrence does not establish independent reuse.

| Consumer | Required result | Interface stress | Campaign stage |
|---|---|---|---|
| Edit distance, full table and memoized | Correct recurrence; reached-state/request bound; priced lookup/body work | Two-dimensional keys, boundaries, no tree decomposition | G2 mandatory |
| Sparse DAG reachability or DAG value evaluation | Work in reached vertices plus requested edge occurrences | Sparse state envelope, repeated requests and multiple roots | G2 or API review |
| Two-stack queue | Sequence bound with a potential-bearing state contract | Long cheap/expensive mixes, result-size/frame behavior | G3/G4 supporting |
| Prepared graph queries with shared preprocessing | Preprocessing paid once; explicit per-query scans and workspaces | Batch lifecycle and actual source reuse | G4 mandatory alternative |
| Persistent queue or memoized branching computation | Bound that rejects duplicated initial credit | Branching ownership beyond sequential telescoping | Only if AMO-03 selected |
| Rolling-row edit distance | Equality to full-table value and peak live-cell bound | Retirement, slot reuse and transient output | G5 space extension |

The prepared-query example can establish the basic batch API but may be too easy to justify a difficult shared-work theorem. If the extension claims substantially general amortized reoptimization, add an example with a nontrivial charging argument, such as a supported incremental graph routine. The proof should exercise the claimed strength instead of merely fitting the types.

## 6. Work saved versus work deliberately retained

| Reused result | Proof work removed from clients | Proof work that must remain |
|---|---|---|
| Generic memo interpreter | Cache induction, unique expansion, root/request accounting | Recurrence correctness, closure, local dependency/work bounds |
| Primitive contracts | Repeated loop-level proofs for each lookup and insert | Correct representation choice and size/overflow premises |
| Modular potential rule | Repeated telescoping and frame composition | An appropriate potential and local transition inequality |
| Bounded-fiber charging | Global occurrence summation | A valid charging map and fiber bound |
| Batch composition | Repeated preparation/dispatch/job arithmetic | Actual reuse, repair correctness and local repair cost |
| Ready schedule | Generic propagation and event summation | A concrete producer/rank/lifetime proof |
| Uniform asymptotic adapter | Repeated coercion/filter/constant plumbing | Correct admissible domain and input envelope |
| Source realization | Repeated backend adequacy arguments | Program-specific simulation where source differs from the certified interpreter |

## 7. Application handoff record

Each application report names its source/hash, mathematical specification, resource semantics, primitive contracts, input domains, theorem level, exact and asymptotic statements, and limitations. Include links to the generic declarations used and list the local lemmas that remain. Report missing prerequisites as blockers rather than supplying them as unexplained assumptions in a headline theorem.

## Sources

See [14-bibliography.md](14-bibliography.md), particularly [P01--P03], [I01], [R01], [R03], [R05]. The precise local declaration map and baseline are in [01](01-repository-baseline.md).
