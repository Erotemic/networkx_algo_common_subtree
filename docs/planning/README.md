# Common-subtree verification planning

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

## Current execution order: usable software first

The 2026-11-14 reprioritization supersedes the earlier proof-first sequencing.
Finish public Python/PyO3 algorithm coverage, independent correctness/parity,
and measured performance before substantial remaining proof work. Preserve
all established proofs. Full mathematical, production Rust correspondence and
applicable complexity verification remain blockers for the final verified
release, while development builds and use can proceed. The concise current
inventory and evidence are in [capabilities.md](capabilities.md).

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
wheel passes all 209 tests with native backends mandatory. Independent graph
witness rescoring and exhaustive optimum comparisons are included. Installed
API measurements cover both optimized schedules, matching deletion families,
conversion overhead and independent witness rescoring. See the capability
matrix and benchmark evidence before continuing the remaining ordered
coverage, correctness and optimization tasks.

The ordered isomorphism APIs now expose the existing root-preserving level
state with `rooted=True`, alongside the default general state. Independent
parent-preserving subset enumeration validates both contracts and fractional
affinities. Normal and genuine Rust-only ABI3 wheels are tested; the latter
passes the complete 209-test API suite on each CPython 3.10–3.14.

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
