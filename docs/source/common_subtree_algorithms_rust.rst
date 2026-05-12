Paper-derived weighted common subtree Rust experiment
======================================================

This overlay adds a sequestered Rust crate at
``rust/crates/common_subtree_algorithms`` for experimenting with graph-only
implementations of two public algorithms:

* Droschinsky, Kriege, and Mutzel, "Faster Algorithms for the Maximum Common
  Subtree Isomorphism Problem", arXiv:1602.07210.
* Droschinsky, Kriege, and Mutzel, "Largest Weight Common Subtree Embeddings
  with Distance Penalties", arXiv:1805.00821.

Terminology
-----------

The crate name is intentionally descriptive. If ``MCSI`` appears in local notes
or tests, it means **maximum common subtree isomorphism**. Public API names should
prefer spelled-out terms where practical.

Scope
-----

Included in this experiment:

* maximum-weight bipartite matching with forbidden edges and unmatched vertices;
* maximum-weight common connected subtree isomorphism for labeled trees;
* a distance-penalized labeled subtree embedding prototype;
* a slow Python reference implementation for small correctness tests.

Excluded by design:

* domain-specific parsers or label systems;
* visualization or file-format handling;
* general-graph decomposition and controller code;
* Python/NetworkX wrapping before the Rust API and tests stabilize.

Implementation model
--------------------

The 2016 isomorphism routine follows the paper-level recurrence: choose a root
pair, recursively score compatible child-root pairs, and combine independent
child choices with a maximum-weight bipartite matching. Unmatched children are
allowed, which lets the optimum be a connected subtree of each input tree.

The 2018 embedding routine extends the same rooted matching structure by allowing
vertices to be skipped at a configurable distance-penalty cost. The current
implementation is a reference-oriented prototype rather than the final optimized
form of the paper.

Reference implementation
------------------------

The Python module ``networkx_algo_common_subtree.common_subtree_reference`` is a
slow executable specification. It enumerates small connected subtrees, embedding
skeletons, and bijections directly. It is intended to validate semantics, not to
serve as a production backend.

Correctness artifacts
---------------------

See :doc:`common_subtree_correctness` for the proof obligations, witness
validators, brute-force reference checks, and fixture strategy used to validate
this crate before exposing it as a public backend.

Testing
-------

Run the Rust-side tests with::

    cargo test --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml

Run the Python reference tests with::

    python -m pytest tests/test_common_subtree_reference.py
