# Common subtree algorithms

This crate is a deliberately sequestered Rust implementation space for weighted
common-subtree algorithms on labeled trees. It is intended to become a compact
third-party reference implementation of the graph algorithms described in these
two public papers:

- A. Droschinsky, N. M. Kriege, and P. Mutzel, "Faster Algorithms for the
  Maximum Common Subtree Isomorphism Problem", arXiv:1602.07210,
  https://arxiv.org/abs/1602.07210
- A. Droschinsky, N. M. Kriege, and P. Mutzel, "Largest Weight Common Subtree
  Embeddings with Distance Penalties", arXiv:1805.00821,
  https://arxiv.org/abs/1805.00821

## Name and terminology

The crate is named `common_subtree_algorithms` so readers can understand the
scope without already knowing paper-specific acronyms. When an acronym is useful
in comments or tests, use it only after defining it:

- **MCSI** means **maximum common subtree isomorphism**, the problem addressed by
  the 2016 paper.
- **Common subtree embedding with distance penalties** refers to the
  largest-weight embedding objective from the 2018 paper. The crate currently
  spells this out in public API names instead of introducing another acronym.

## Scope

The API is graph-only. It works with ordinary labeled trees, explicit scoring
hooks, and weighted bipartite matching subproblems. It intentionally excludes
application-specific parsing, visualization, chemistry/domain labels, and
general-graph preprocessing. Those concerns can be layered above this crate later
if the tree primitives prove correct and useful.

Implemented in this overlay:

- maximum-weight bipartite matching with optional forbidden edges and unmatched
  vertices;
- maximum-weight common connected subtree isomorphism for labeled trees, using
  rooted dynamic programming and child matchings as in the 2016 paper;
- an experimental largest-weight common subtree embedding routine with a
  per-skipped-vertex distance penalty, following the high-level recurrence
  structure of the 2018 paper.

The embedding routine is intentionally conservative. It is meant to stabilize the
core recurrence and test expectations before optimizing the repeated matching
instances or adding a public Python/NetworkX-facing wrapper.

## Validation strategy

The crate now has several layers of tests:

- hand-written smoke tests for the public API;
- deterministic bipartite-matching tests that compare the Hungarian-based solver
  against a brute-force matching oracle on small matrices;
- maximum common subtree isomorphism tests that compare the dynamic program
  against a slow exhaustive connected-subtree oracle on small labeled trees;
- embedding tests that exercise skipped vertices, high-penalty fallback, zero
  penalty long-path embeddings, and input-order symmetry.

A separate pure-Python reference implementation lives in
`networkx_algo_common_subtree.common_subtree_reference`. It directly enumerates
small vertex subsets and bijections. That implementation is intentionally too
slow for production, but it provides a readable executable specification for
future conformance tests.

Run the Rust-side tests with:

```bash
cargo test --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml
```

Run the Python reference tests with:

```bash
python -m pytest tests/test_common_subtree_reference.py
```

This crate is not wired into the Python extension yet. That is intentional: the
Rust API and conformance tests should stabilize before exposing it through PyO3
or a NetworkX conversion layer.
