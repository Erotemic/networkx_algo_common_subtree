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
3. **[Droschinsky (2016 and 2018): verified Rust and Lean](droschinsky_2016_2018_verified_rust_lean.md)**:
   weighted unordered isomorphism, weighted partial matching, topological
   embeddings with distance penalties, paper-correct scoring, faster
   algorithms and their verification.

## Starting point as of 2026-11-13

| Priority | Immediate action | Evidence of completion |
| --- | --- | --- |
| 1 | Fix last Lean 4.35.0 `OrderedTree.lean` elaboration issue and rerun `lake build` | Clean build, committed Lake manifest, `proofs/PROOF_STATUS.md` updated to match accepted declarations |
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
