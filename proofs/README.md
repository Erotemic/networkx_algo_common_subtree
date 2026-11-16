# Common-subtree mathematics and Rust verification

The development uses Lean 4.35.0, pinned Mathlib, and a compatible pinned
Aeneas backend. [PROOF_STATUS.md](PROOF_STATUS.md) records accepted theorem
names, hypotheses and open obligations; [VERIFICATION.md](VERIFICATION.md)
has exact build, extraction and VM cache instructions. The
[paper crosswalk](../docs/planning/paper_statement_crosswalk.md) pins source
editions and distinguishes original claims from corrections.

The independent ordered-tree problem specification lives in
`Paper2004/OrderedTree.lean`: arbitrary-depth ordered edge contractions,
true leaves/depth and the maximum-common-tree objective. Encoding and decoding
are inverse, and `ContractionSoundness` / `ContractionCompleteness` prove the
two-way correspondence with matched-pair deletions. The printed containment
clauses are preserved separately in `PaperContainment`; the compiled
`PrintedContainmentCounterexample` refutes their completeness.

`ContractionOracle` proves a deliberately slow independent tree enumerator
complete and its chosen tree globally optimal. `OptimalEncoding` transports
optimality between trees and balanced words. `Decomposition` formalizes the
paper's D/R/S families and proves their inclusions, cardinality of R, depth
bound, and a corrected actual-leaf bound. `TreeStateBounds` connects those
measures to the independent tree parameters. `DynamicProgram` proves the
constructive Lemma 8 recurrence optimal by a structural first-pair argument;
its decoded witness satisfies the independent `IsMaximumCommon` predicate.
`LinearEncoding` provides a constructor-only accumulator encoder with an exact
linear cost count (Fact 1). `MemoizedDynamicProgram` separately proves the threaded score computation
correct, keys unique, and lookup/insertion counts bounded by the D-product.
Its association-list lookup comparisons carry an extra proved state-count
factor. Full word-representation and dictionary runtime refinement remains open.

`Shared/WeightedMatching` specifies signed partial matchings with forbidden
pairs and proves a finite exhaustive optimizer correct. `AssignmentReduction`
proves the exact real-weight dummy-assignment reduction. `Shared/FiniteTree`
and `RootedTree` supply canonical paths, ancestry and connected-subtree geometry.
`Droschinsky2016/Specification` and `Witness` define independent nonempty graph
optima; `Rooted` proves fixed-root Lemma 2, and `RootedRecurrence` proves Eq. (1)
with exact score decomposition and concrete branch assembly. Efficient recursive
evaluation, Hungarian correctness, cost bounds and Rust refinement remain open.
`Droschinsky2018/Specification` defines skeletons and exact path penalties;
`Witness` constructs source-style rooted embeddings at corresponding chosen
roots. `Reconstruction` proves the exact unrooted source correspondence and
abstract-tree score equality. Shared path lifting and `RootedEmbedding` prove
ancestry in both directions from both witness formats. `Rooted` proves fixed
ambient-root and root-to-root source equivalences. `MappedDecomposition` and
`SkippedRecurrence` prove both halves of Lemma 5 against independent boundary
witness maxima, using concrete assembly and exact score decomposition. Efficient
executable evaluation, matching/cost and graph Rust refinement remain open.

`Rust/Generated` contains unedited Charon/Aeneas output from the maintained
`verified_ordered_core` Rust crate. `Rust/ContractionBudget` proves its first
operation refines a genuine tree contraction's edge count. `Rust/OrderedSolver` further verifies the real structural-witness solver
against the independent maximum for inputs below 2^32 edges per tree. This
reference Rust recursion is exponential. `Rust/MemoizedOrderedSolver` also
proves the actual memoized entry point correct and its cache equal to the numeric
Lean model, transferring cache uniqueness and state bounds. Efficient dictionary
and representation cost, index witnesses and API conversion remain open.

Build the full maintained proof chain with:

On virtiofs VMs, first run `dev/setup-build-caches.sh` from the repository
root and verify `--status`; see [VM caches](VERIFICATION.md#vm-caches).

```bash
cd proofs
lake exe cache get
lake build
```

Run independent finite mathematical diagnostics from the repository root:

```bash
python proofs/checks/check_printed_containment.py
python proofs/checks/check_tree_contraction_oracle.py
python proofs/checks/check_paper_dp_recurrence.py
```

These diagnostics enumerate tiny instances independently. Their results are
finite test evidence; the general claims above are Lean theorems. Endpoint
dependency review is opt-in through `BaselineAudit.lean` and is kept out of
routine compilation and CI.
