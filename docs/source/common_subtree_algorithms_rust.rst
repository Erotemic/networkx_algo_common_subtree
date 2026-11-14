Weighted common subtree Rust and Python APIs
============================================

The graph-only Rust crate at ``rust/crates/common_subtree_algorithms`` backs
the installed NetworkX/PyO3 interfaces for two algorithm families:

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

Available functionality:

* maximum-weight bipartite matching with forbidden edges and unmatched vertices;
* maximum-weight common connected subtree isomorphism for labeled trees;
* a distance-penalized labeled subtree embedding prototype;
* public Python APIs with original-node mappings and aligned path witnesses;
* finite signed scalar/callback weights, optional labels, empty/nonempty modes;
* independent exhaustive Python references and witness rescorers;
* separate exact integer assignment and partial matching APIs backed by the
  source-proved ``verified_assignment_core``.

For example::

    import networkx as nx
    import networkx_algo_common_subtree as common
    left, right = nx.path_graph(3), nx.path_graph(4)
    result = common.maximum_common_subtree_isomorphism(left, right, impl="rust")
    assert result.weight == 5
    assert common.score_common_subtree_isomorphism(left, right, result) == 5
    print(result.mapping)

See :mod:`networkx_algo_common_subtree.unordered` and
:mod:`networkx_algo_common_subtree.matching` for parameters and result types.
``impl="auto"`` prefers Rust; ``impl="python"`` independently enumerates small
instances. Graph inputs are undirected simple trees, including empty graphs.
Label options name attributes requiring equality; callbacks receive original
nodes or edge endpoint pairs. ``allow_empty=False`` retains negative optima
and returns ``None`` only for infeasible nonempty inputs.

Excluded by design:

* domain-specific parsers or label systems;
* visualization or file-format handling;
* general-graph decomposition and controller code.

Implementation model
--------------------

The 2016 isomorphism routine follows the paper-level recurrence: choose a root
pair under one fixed left-tree rooting, recursively score compatible child-root pairs, and combine independent
child choices with a maximum-weight bipartite matching. Unmatched children are
allowed, which lets the optimum be a connected subtree of each input tree.

The 2018 embedding routine extends the same rooted matching structure by allowing
vertices to be skipped at a configurable distance-penalty cost. The current
implementation is a reference-oriented prototype rather than the final optimized
form of the paper. An edge reward/compatibility test applies only when both
matched paths are single edges; longer paths incur only skipped-vertex
penalties. Both APIs provide independent original-node/path witness rescoring.

The floating-point graph DPs are independently tested; their production Rust
source refinement and published optimized complexity remain open. Mathematical
recurrence proofs and exact integer assignment source proofs have distinct
assurance boundaries. The current ledger is ``proofs/PROOF_STATUS.md``.

Reference implementation
------------------------

The Python module ``networkx_algo_common_subtree.common_subtree_reference`` is a
slow executable specification. It enumerates small connected subtrees, embedding
skeletons, and bijections directly. It is intended to validate semantics, not to
serve as a production backend.

Testing
-------

Run the Rust-side tests with::

    cargo test --manifest-path rust/crates/common_subtree_algorithms/Cargo.toml

Run the Python reference tests with::

    python -m pytest tests/test_common_subtree_reference.py

Exercise all installed native APIs and required Cython parity with::

    COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS=1 python -m pytest tests


Benchmarking
------------

PyTorch-sized module-tree benchmark fixtures are documented in
:doc:`common_subtree_benchmarks`.  They target model-hierarchy sizes and
perturbations that are relevant to partial weight loading between related neural
network models.
``dev/bench_unordered_apis.py --module-trees`` measures installed public APIs and
raw PyO3 calls, including witnesses. Repeated measurements and native allocation
profiles are under ``dev/benchmarks/``. Specialized paper matching/path schedules
remain explicit implementation work.
