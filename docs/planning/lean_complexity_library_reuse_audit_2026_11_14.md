# Lean complexity-proof library reuse assessment (2026-11-14)

**Target repository:** `networkx_algo_common_subtree` snapshot `e272d36b09de`, 2026-11-14.  
**Scope:** Formal time/space bounds and source refinement for Lozano–Valiente 2004, Droschinsky–Kriege–Mutzel 2016 and 2018.  
**Method:** Inspected upstream repository source and published module documentation on 2026-11-14, cross-checked against our Lean files and `paper_statement_crosswalk.md`. **No upstream Lean build or integration smoke test was executed in this environment** (Lean/Lake unavailable). Inspecting source declarations is evidence of their presence, not proof of compatibility in our workspace.

## Execution follow-up

The [isolated experiment](../../proofs/experiments/arlib_cost/README.md) now
builds with the exact main dependency pins: 3,744 jobs pass, including the full
main proof library. It proves an operation-bearing lookup's value and exact
comparison-counter bridge to existing `memoFind`, a `2*n+1` recorded-operation
bound, early-hit behavior and explicit dictionary model exchanges. Three
negative compilation checks pass. The original source-only assessment below is
preserved; `results.json` records the subsequent execution. Decision: retain
the experiment without adding arlib to the main manifest. Existing counters
remain useful; production resource correspondence is a separate obligation.

## Decision in brief

1. **Keep Mathlib and Aeneas as the established foundation.** Mathematical cardinality, combinatorial sums and asymptotics stay in Mathlib; source correspondence stays in Aeneas.
2. **Perform one isolated arlib proof spike before committing to any cost framework.** Contrary to earlier descriptions of arlib as mainly for randomized algorithms, arlib's *current* `Arlib.Computation` area contains a sophisticated resource-modeling library. Its `main` branch at `8d08f89a6d05c5e8368e91659bd6e117fbb74c4e` uses **Lean 4.35.0 and the same Mathlib commit** (`56a005855ea17e0b0958f73ec801ae140b0a1679`) as our snapshot. This is the best candidate for reusable charging infrastructure. Adopt only if a demonstration proves a real connection to the present recurrence or solver, not just an unrelated `Charged` example.
3. **Read CLRS-Lean for weighted-assignment invariants and amortized-proof organization; do not adopt as a dependency yet.** Its current `main` is pinned to 4.32.0-rc1. The local signed, partial, forbidden-edge matching reduction and actual Rust exact matching proofs substantially overlap the reusable correctness core. The paper-specific deletion-family amortization is still ours to prove.
4. **Read small, targeted Tau Ceti modules, but do not add the moving dependency.** The candidate Dyck-word file adds only elementary counts; reduced planar trees prohibit unary nodes; its matching module is unweighted multigraph matching, not the weighted matching engine. Its path lemmas may help an individual 2018 structural proof, but require a precise use case and a local import demonstration. Current `main` is rapidly changing.
5. **Do not use Lean4CStheory's `TimeM` as the primary operation-count model.** It wraps CSLib's `TimeM`, whose annotations are explicitly **trusted**, not tied mechanically to operations. Its generic halving/Master-theorem lemmas are not the bottleneck for the matching-family sums.
6. **Do not run Tex2Lean over the papers to recreate the existing work.** Its Model/Interface/Analysis separation and `Charged` recommendations are good review patterns. Its CLI/extension is a workflow tool, not a drop-in library of matching cost theorems; current published package source is not publicly exposed for independent code review. It uses arlib's `Charged` operations.

## Exact version / compatibility ledger

| Project | Source revision inspected | Lean pin | Mathematical overlap | Integration decision |
|---|---|---|---|---|
| Our proofs | `e272d36b09de` snapshot | `v4.35.0`, Mathlib `v4.35.0` | Independent DP/specs, exact matching components | Baseline |
| Mathlib | Project's pinned `v4.35.0` | `v4.35.0` | `Asymptotics.IsBigO`, `Finset`/`Fintype`, paths, trees, sums | Already required |
| arlib | `8d08f89a6d05c5e8368e91659bd6e117fbb74c4e` | `v4.35.0`, Mathlib SHA `56a00585…` | Charged code, sealed data structures, RAM cost and space | **Highest-value experiment** |
| CLRS-Lean | `9352a92ba9b1d44ad1349f9e57ac31c858ec81b8` | `v4.32.0-rc1` | Hungarian optimality, tree potentials, amortization patterns | Source reference only |
| Lean4CStheory | `7f0a215d60c83906e15cbc753f7dc7e7a5d3f935` | `v4.33.1` | Simple recurrence/cost examples | Source reference only |
| Tau Ceti | `ca32605ff53921fa0689dd312618b7cfaafa7e43` | Moving current Mathlib/Lean | Selected path/graph lemmas | Source reference only |
| Tex2Lean | Public documentation/release package | Own setup | Formalization workflow, `Charged` example use | No integration |

Even identical Lean/Mathlib revisions do not imply all Lake dependencies build together. In particular, test arlib with the pinned Aeneas dependency before adding it to the main manifest.

## A. arlib: concrete source findings (highest priority)

Repository: https://github.com/meelgroup/arlib/tree/8d08f89a6d05c5e8368e91659bd6e117fbb74c4e

### Exact available constructs

* `Arlib/Computation/Cost.lean`: `CostVec κ` counts each primitive operation type `κ` separately, `Rate` prices operations, and `CostVec.steps_exchange_le` transfers a bound through an operation-cost exchange. The concrete word-RAM `Op` has `add`, `lt`, `load`, `store`, `alloc`, etc. Distinguish abstract operation counts from executable instructions.
* `Arlib/Computation/Charged.lean`: `Charged κ κₛ α` contains value, cost vector and space profile with private constructor; `Charged.op`, `Charged.opUpdate`, `Charged.foldl`, `Charged.cost`, `Charged.steps` and `Charged.space`. In particular, `Charged.cost_bind` establishes composition of recorded costs *from the charged program*, not a separately supplied cost recurrence.
* `Arlib/Computation/Dict.lean`: `Dict ι α` exposes charged `Dict.find`, `Dict.insert`, `Dict.erase`, `Dict.size`, `Dict.cardEq`, with `Dict.lookup` and key sets as noncomputable specification views. Lookup/insert are **abstract operations**—not automatically constant-time machine actions.
* `Arlib/Computation/Heap.lean`: sealed leftist heap with `Heap.push`, `Heap.pop` and comparison-cost bounds (`cost_push_le`, `steps_push_le`, etc.). Potentially useful if the matching implementation needs a priority queue, but does not provide Hungarian/dynamic assignment correctness.
* `Arlib/Computation/Std.lean`: `StdOp` unifies eight operation currencies, and `StdImpl` exchanges abstract costs into implementation-dependent word costs. `StdImpl.constantTime` is a *cost assumption*. A worst-case constant-time dictionary does **not** establish expected `O(1)` hashing, which is relevant to 2004 Theorem 3.
* `Arlib/Computation/ChargedStorage.lean`, `ChargedLoop.lean`, `RAMDict.lean` and `ExactRealization.lean`: certified finite buffers, word-indexed loops, direct-address dictionaries and relations to the library's **own abstract RAM**. These provide models/examples, not automatic cost theorems for Aeneas-generated Rust.
* `ArlibTest/Computation/ChargedAuthoring.lean`: executable example of a source `Charged Op Unit (Word 8)` program and its `RAM` analogue; `ExactRealizes` proves both result correspondence and equality of opcode counts. Concrete examples prove `Charged.steps CostModel.unitCost source = 23` and the RAM program likewise costs 23. Useful as a reproducible smoke test.

### Safety and trust boundaries

Read `docs/dev/Cost-Modelling-Protocol.md` and `docs/dev/Charged-RAM-Realization.md`. The library explicitly warns that a careless program can compute a costly function inside `pure` for **zero charged steps**. Correct cost claims require **sealed data**, no hidden specification view, and a program/operation audit. Its own space documentation also notes limitations of unrestricted sharing and the need for `ExactNet` assumptions.

A `Charged` implementation that merely wraps `memoLcs` as `pure (memoLcs ...)` proves nothing about runtime. Likewise, an oracle operation that says “solve Hungarian matching in one step” establishes only a bound in *Hungarian calls*, unless its implementation cost is independently proved.

### Value to specific obligations

* **2004 Theorem 3**: strong candidate for a verified operation vector distinguishing (a) memo-key comparisons, (b) Dyck-word access/splice/copy, and (c) dictionary find/insert. Our `Paper2004/MemoizedDynamicProgram.lean` already has `MemoRun.calls`, `misses`, `comparisons`, and an association-list `memoFind`; a Charged version should be proved equivalent to this existing computation, not replace the independent optimum. For the paper's *expected hashing* term, either state a separate abstract amortized/expected hash contract or prove an actual randomized dictionary model; `StdImpl.constantTime` alone is insufficient.
* **2016 Lemma 5/6, Theorems 4/7**: model operation families for augment/search/dual adjustments/matching reuse. The nontrivial work is still bounding the sum across correlated matching calls. `Heap` and `Dict` may supply charged primitives if the paper schedule uses them.
* **2018 Lemmas 12–14, Theorem 15**: model oriented DP state evaluations, table accesses, right-deletion matching-family reuse and peak storage. Source-level loop and memory cost correspondence remains a separate obligation.

**Verdict:** Try in an isolated branch. A dependency is warranted only if we can reuse it without duplicating algorithm implementations or weakening claims.

## B. CLRS-Lean: weighted matching mathematics

Repository: https://github.com/TankTechnology/CLRS-Lean/tree/9352a92ba9b1d44ad1349f9e57ac31c858ec81b8

Chapter 25 (https://tanktechnology.github.io/CLRS-Lean/CLRSLean/FourthEdition/Chapter_25/) includes:

* `Problem`—balanced complete bipartite graph with real assignment weights;
* `Feasible`—dual labels satisfying `y_l + y_r ≤ w(l,r)`;
* `perfect_tight_optimal`—a perfect matching of tight edges under feasible labels is optimal;
* `potential_step`, `exists_augment_of_tight_free`, `growTree`—local Hungarian invariants;
* `hungarian_constructs_optimal (P : Problem V) : ∃ M : Matching V P.G, P.Optimal M`.

That last theorem is an **existence/correctness result in CLRS's model**, not a theorem about our Rust matching code or about the total cost of all vertex-deleted matchings. Our exact signed-i64 Rust matching cores and the dummy/forbidden-edge/partial matching reductions already have source-level proofs. Importing CLRS may create more translation work than using our existing results.

Other CLRS chapters model asymptotic and amortized algorithm costs (e.g. union-find). Useful to study as proof design examples; do not assume their data structures/cost bounds transplant directly into the graph solver.

**Verdict:** Retain as documented reference; consider local reuse of a particular invariant only after a targeted equivalence proof and compatible toolchain pin. No full dependency currently.

## C. Tau Ceti: inspect narrow results, not the whole moving library

Repository: https://github.com/TauCetiProject/TauCeti/tree/ca32605ff53921fa0689dd312618b7cfaafa7e43

Concrete module inspection:

* `TauCeti.Combinatorics.Enumerative.DyckWord`: 26 lines; provides `count_U_add_count_D`. **Low incremental value** to the already proved ordered-tree/Dyck/containment bridge.
* `TauCeti.Combinatorics.Tree.ReducedPlanar`: `ReducedPlanarTree` with no unary vertices; contains `numInternal_add_one_le_numLeaves`. Generic ordered trees in our specification *can* have unary nodes, so direct substitution would change the problem. **Low benefit without a special reduced-tree subproblem**.
* `TauCeti.Combinatorics.SimpleGraph.Paths`: path splitting/support lemmas including `IsPath.exists_support_eq_cons_append` and `exists_eq_append_of_exists_mem_support`. **Potential value** to 2018 Lemmas 9/10 if a pending proof goal matches the exact hypotheses. The module does not provide the paper's unrooted dichotomy itself.
* `TauCeti.Combinatorics.Graph.Matching.Basic`: validity/perfectness in a **multigraph** model (`Graph α β`); not weighted assignment/Hungarian or deletion-family amortization. Our existing weighted assignment development has a different representation. **Low direct benefit**.

Tau Ceti is under very active development and tracks Mathlib master. Even if a standalone lemma looks attractive, prefer reproducing a narrowly useful general theorem with appropriate attribution or collaborating upstream, rather than pinning a 37,000-file evolving dependency solely for that lemma. Check licensing and exact statement equivalence before reusing code.

**Verdict:** No mandatory dependency. Do a goal-specific source search when work begins on 2018 Lemmas 9/10.

## D. Lean4CStheory + CSLib TimeM

Repository: https://github.com/Lean4CStheory/Lean4CStheory-Library/tree/7f0a215d60c83906e15cbc753f7dc7e7a5d3f935

`Lean4CStheory/Time/Basic.lean` defines `abbrev TimeM α := Cslib.Algorithms.Lean.TimeM Nat α`; `TimeM.tick (a) (c)` returns `⟨a,c⟩`. CSLib's own TimeM documentation says **time annotations are trusted and unverified against actual execution work**: https://api.cslib.io/docs/Cslib/Algorithms/Lean/TimeM.html . This is acceptable for deliberately axiomatized abstract cost, but it leaves the central implementation-to-cost bridge as a manual obligation.

`Lean4CStheory/Asymptotics/MasterTheorem/NatRecurrences.lean` proves concrete halving-recurrence bounds including `master_halves_plus_linear`, `master_two_branch_linear_of_contract`, and `master_median_of_medians_linear`. These are not the degree-sensitive finite-sum and matching-reuse bounds needed for 2016/2018. The extra dependency uses Lean 4.33.1, so pin mismatch adds cost.

**Verdict:** Useful readable examples, but avoid integration.

## E. Tex2Lean

Documentation: https://www.tex2lean.com/ and https://github.com/meelgroup/tex2lean-releases

This is a formalization workflow (CLI/VS Code extension) for extracting statements from LaTeX, preparing `Model/`, `Interface/`, and `Analysis/`, proving with external AI agents, and auditing assumptions. Its published guide explicitly recommends arlib's `Charged` for time complexity. It is not a theorem library that can be directly imported to resolve our open matching arguments; the downloadable product's code is not currently a publicly reviewed source library.

Our repository already has a statement crosswalk, mathematical definitions, independent specifications and verified source bridges. A wholesale automated re-formalization risks duplicate statements and altered assumptions (especially the erroneous printed 2004 containment definition).

**Verdict:** Borrow proof-review/checklist methodology, not the tool as a new project driver.

## F. Mathlib and Aeneas (existing dependencies)

* `Mathlib.Analysis.Asymptotics.Defs` supports `Asymptotics.IsBigO`, `IsBigOWith`, etc.; for finite algorithm counts first prove an explicit `Nat` inequality with parameters and constants, then derive asymptotic notation. The asymptotics API is not a source cost semantics.
* Existing Mathlib `Finset`/`Fintype` sums and combinatorial injection arguments are directly applicable to the degree products, state-family cardinalities, and amortized charging needed by Droschinsky.
* Aeneas translates Rust semantics to functional Lean, preserving functional behavior and error branches. **It does not, by itself, give a hardware-instruction or RAM execution-cost theorem.** A subsequent proof must relate the Rust program, its modelled operations and the charged abstraction. Do not conflate a cost bound for a functionally equivalent Lean algorithm with a proved cost bound of the production Rust.
* Under our proposed **ideal exact arithmetic** for production `f64`, assume exact arithmetic only for operations reached during a run (or use a generic arithmetic interface), not a global false axiom. Its unit arithmetic charges describe an algebraic-operation model, **not** machine-word runtime for arbitrary reals.

## Concrete recommendations by missing paper theorem

| Obligation | Strongest available help | Existing local proof endpoint | Missing theorem/proof obligation |
|---|---|---|---|
| 2004 Theorem 3 | arlib `Charged`+`Dict`+`CostVec`; Mathlib sums | `MemoizedDynamicProgram.lean`: `memoFind_comparisons`, `MemoRun`, `memoLcs_correct`; `TreeStateBounds.lean` | Charged structural word/dictionary operations; bound per state; bridge to exact executed recurrence; qualified expected-hashing assumption |
| 2016 Lemma 5 | CLRS Hungarian potential invariants as reference; local `AssignmentDuality`, `CopiedMatchingDuality` | Signed/partial matching reduction and exact source proofs | Rectangular matching source/operation bound, relevant data-structure model |
| 2016 Lemma 6 & Theorem 7 | arlib charged heap/collection primitives + Mathlib amortized sums | `AssignmentVertexDeletion.lean`, `AssignmentCycleRepair.lean`, existing sparse augmentation proofs | Correct optimized deletion-family scheduler; bound over all reused matchings |
| 2016 Theorem 4 | Above + existing rooted recurrence | `Droschinsky2016/RootedRecurrence.lean`, `RootedDynamicProgram.lean` | Sum of entire oriented DP + matching work, reconstruction, memory |
| 2018 Lemmas 9–10 | Tau Ceti path-support lemma candidates + Mathlib walks | `Droschinsky2018/Reconstruction.lean`, `MappedDecomposition.lean` | Independent unrooted structural dichotomy/fixed-root reduction |
| 2018 Lemmas 12–14 | arlib operation counting + local matching proofs | `Droschinsky2018/SkippedRecurrence.lean`, `RootedDynamicProgram.lean` | Evaluation order, maximum reuse, all-deletion family complexity |
| 2018 Theorems 6, 15 | Mathlib finite sums + charged time/space | Correct rooted reference evaluator | Full optimized runtime/space theorem and Rust representation bridge |

## One limited integration experiment (accept/reject gate)

**Do not add permanent dependencies until this experiment succeeds on a separate branch.**

1. **Pin upstream**: Use arlib SHA `8d08f89a6d05c5e8368e91659bd6e117fbb74c4e`; verify `lean-toolchain` is `v4.35.0` and the Mathlib resolved SHA is `56a005855ea17e0b0958f73ec801ae140b0a1679`, matching our snapshot. Update the *experimental branch only* Lake file and check `lake build SubtreeProofs` with the pinned Aeneas dependency.
2. **Build the reference example**: Import `Arlib.Computation.Charged`, `Arlib.Computation.Dict`, `Arlib.Computation.Std`, and `Arlib.Computation.ChargedStorage` in a standalone test. Reproduce a small verified operation-count calculation from `ArlibTest/Computation/ChargedAuthoring.lean` using a sealed carrier. Do not treat a `pure` wrapper as acceptance evidence.
3. **Prove a bridge to an existing computation**: Define a small *charged memo lookup* with the same semantics as the actual `memoFind` for one finite table. Prove `chargedFind.val = memoFind ... |>.1` and derive an upper bound on the charged lookup/table operation count from the original table length. Repeat on an early-exit branch.
4. **Verify no cost laundering**: Deliberately test that a supposedly sealed dictionary cannot be inspected in a `def` through its noncomputable view; ensure forbidden access is caught. Document every primitive that assumes unit time.
5. **Cost model honesty**: Show how the abstract dictionary operation bound translates under `StdImpl.listBacked` (linear lookup) and an explicit assumed constant-time model; do not call the latter expected-time hashing. Identify what must be supplied to prove an expected-hash theorem.
6. **Compare cost**: Measure proof complexity and build time against extending the existing `MemoRun` counters. If arlib requires rewriting the complete DP before yielding a valid new theorem, reject integration for the 2004 proof; it may still be worth using in later optimized matching cost analysis.

**Success condition:** One proof about an actual operation-bearing version of our memoized computation, with a nonvacuous cost bound and unchanged semantic output, checked under the repository's pinned toolchain. **Failure condition:** only imported example theorems pass, or an independent charged implementation has no proven refinement to the existing solver.

### Proposed long-term proof layout

```
Paper-level specification / independent optimum                 [existing]
                |
Verified DP / matching recurrence                              [existing]
                |
Optimized Rust result and reconstruction via Aeneas             [open]
                |
Resource-refinement relation to charged operations             [open]
                |
Charged operation count + shared amortized matching lemmas      [open]
                |
Big-O / peak-space corollaries under explicit cost assumptions   [open]
```

The resource relation is a second proof bridge. Functional equivalence does *not* alone imply similar complexity: one correct implementation could spend exponential time and another polynomial time. The charged model must describe the **specific algorithm whose complexity is claimed**.

## Final decision

**Primary action:** conduct the arlib spike above; no general dependency upgrade yet.  
**Secondary action:** extract the reusable amortized matching-family statements into a dedicated local `Complexity/MatchingFamilies` development, using Mathlib finite-sum lemmas. Treat CLRS and Tau Ceti as targeted references when exact statements match.  
**Avoid:** re-formalizing completed paper mathematics through Tex2Lean, importing CLRS or Tau Ceti wholesale, or claiming production Rust running time directly from a purely functional complexity model.

## Pinned upstream sources inspected

- arlib implementation: https://github.com/meelgroup/arlib/tree/8d08f89a6d05c5e8368e91659bd6e117fbb74c4e/Arlib/Computation
- arlib Charged example: https://github.com/meelgroup/arlib/blob/8d08f89a6d05c5e8368e91659bd6e117fbb74c4e/ArlibTest/Computation/ChargedAuthoring.lean
- arlib cost protocol: https://github.com/meelgroup/arlib/blob/8d08f89a6d05c5e8368e91659bd6e117fbb74c4e/docs/dev/Cost-Modelling-Protocol.md
- CLRS Hungarian: https://tanktechnology.github.io/CLRS-Lean/CLRSLean/FourthEdition/Chapter_25/
- Tau Ceti candidate paths: https://github.com/TauCetiProject/TauCeti/blob/ca32605ff53921fa0689dd312618b7cfaafa7e43/TauCeti/Combinatorics/SimpleGraph/Paths.lean
- Tau Ceti Dyck: https://github.com/TauCetiProject/TauCeti/blob/ca32605ff53921fa0689dd312618b7cfaafa7e43/TauCeti/Combinatorics/Enumerative/DyckWord.lean
- Lean4CStheory source: https://github.com/Lean4CStheory/Lean4CStheory-Library/tree/7f0a215d60c83906e15cbc753f7dc7e7a5d3f935
- CSLib TimeM warning: https://api.cslib.io/docs/Cslib/Algorithms/Lean/TimeM.html
- Tex2Lean usage and assumptions: https://www.tex2lean.com/
- Mathlib asymptotic definitions: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/Defs.html
- Aeneas architecture: https://github.com/AeneasVerif/aeneas/blob/main/documentation/aeneas-overview.md
