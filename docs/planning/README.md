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
