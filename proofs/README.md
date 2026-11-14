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
linear cost count (Fact 1). This recursive algorithm is not yet memoized, so its polynomial state domain
does not by itself prove a polynomial running time.

`Shared/WeightedMatching` specifies compatible partial matchings with integer
weights, forbidden pairs and unmatched endpoints. Its executable exhaustive
matrix optimizer is proved globally optimal. The graph-paper recurrences and
an efficient verified matching algorithm remain open.

`Rust/Generated` contains unedited Charon/Aeneas output from the maintained
`verified_ordered_core` Rust crate. `Rust/ContractionBudget` proves its first
operation refines a genuine tree contraction's edge count. This is a completed
translation feasibility spike, not verification of a Rust solver.

Build the full maintained proof chain with:

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
