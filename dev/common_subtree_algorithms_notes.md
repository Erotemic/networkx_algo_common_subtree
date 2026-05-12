# Paper-derived common subtree implementation notes

The `common_subtree_algorithms` crate is intended to become a compact,
graph-only reference implementation of algorithms described in:

1. A. Droschinsky, N. M. Kriege, and P. Mutzel, "Faster Algorithms for the
   Maximum Common Subtree Isomorphism Problem", arXiv:1602.07210.
2. A. Droschinsky, N. M. Kriege, and P. Mutzel, "Largest Weight Common Subtree
   Embeddings with Distance Penalties", arXiv:1805.00821.

## Naming

The crate uses a descriptive package and library name rather than a compact
acronym. When `MCSI` appears in internal notes, tests, or comments, it means
**maximum common subtree isomorphism**. Public API names should prefer spelled-out
terms unless an abbreviation is part of a well-established paper convention.

## Design scope

The implementation target is deliberately narrow:

- input objects are labeled trees;
- compatibility and weights are supplied through explicit scoring hooks;
- child subproblems are combined through maximum-weight bipartite matchings;
- returned solutions are concrete node mappings plus objective values.

The crate is not intended to include domain-specific parsers, visualization,
chemistry-specific rule systems, or general-graph decomposition machinery. Those
concerns can be layered above this crate later if the tree primitives prove
correct and useful.

## Current overlay contents

`rust/crates/common_subtree_algorithms` currently contains:

1. a small maximum-weight bipartite matching routine with forbidden edges and
   zero-profit unmatched vertices;
2. a rooted dynamic-programming implementation of maximum common connected
   subtree isomorphism for labeled trees;
3. an experimental distance-penalized embedding recurrence that permits skipped
   vertices in either tree;
4. Rust unit and integration tests covering matching, isomorphism, and embedding
   behavior.

The overlay also adds `networkx_algo_common_subtree.common_subtree_reference`, a
slow pure-Python reference module. It is designed for small examples and tests,
not for normal use. Its purpose is to make the intended graph objective easy to
inspect and to provide an independent oracle for future Rust/PyO3 integration.

## Correctness argument roadmap

The repository now contains `docs/source/common_subtree_correctness.rst`, which
spells out the non-formal proof obligations for the new weighted-tree family.
The current plan is to keep three artifacts synchronized:

1. a written recurrence/proof sketch;
2. a slow Python executable specification with witness rescoring; and
3. Rust tests that compare optimized routines against brute-force oracles on
   small cases.

This is intentionally compatible with the existing Lean sketch area for the
Lozano-Valiente family, but it avoids starting a new formalization until the
weighted-tree API and semantics stabilize.

## Validation roadmap

Completed in this overlay:

- deterministic matching tests against brute force;
- exact isomorphism tests against brute force on small labeled trees;
- embedding regression tests for skipped vertices and penalty behavior;
- Python reference tests for exact isomorphism and distance-penalized embedding.

Still useful future work:

- add fixtures that mirror examples from the two Droschinsky/Kriege/Mutzel papers
  where the paper examples specify enough labels and weights to be unambiguous;
- extend the Python reference to cover richer edge/path scoring once the public
  Rust scoring API is finalized;
- add randomized small-tree differential tests between the Python reference and
  Rust once a Python wrapper exists;
- optimize repeated matching instances only after the reference semantics are
  locked down by tests.
