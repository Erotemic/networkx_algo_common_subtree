Common subtree algorithms for NetworkX
======================================

|Pypi| |GithubActions|

Find common structure in trees with fast Rust-backed Python algorithms:
ordered subtree embeddings and isomorphisms, weighted **unordered** subtree
isomorphism, and topological embeddings with penalties for skipped vertices.
Results retain original input nodes so you can inspect, validate and use the
matching. Version 0.3.0 adds the unordered public APIs and exact integer matching.

Install
-------

.. code:: bash

    python -m pip install networkx-algo-common-subtree

Python 3.10 or newer is required. Binary wheels include the fast Rust backend;
ordinary runtime use needs NetworkX 2.8.8 or newer. Rust, Lean and development
submodules are not runtime dependencies. The Linux stable-ABI wheel also
supports Python 3.14; the regular Rust/Cython wheel matrix targets 3.10–3.13. If pip needs to build from source, install Cargo/Rust and a C/C++
toolchain first. See `build and platform details <docs/packaging.md>`_.

Choose an algorithm
-------------------

.. list-table::
   :header-rows: 1
   :widths: 25 50 25

   * - Problem
     - Public function
     - Inputs
   * - Ordered embedding; edges may be contracted
     - ``maximum_common_ordered_subtree_embedding``
     - Directed simple forests; child order matters
   * - Ordered isomorphism; preserve adjacency
     - ``maximum_common_ordered_subtree_isomorphism``
     - Directed simple forests; child order matters
   * - Weighted unordered isomorphism (2016)
     - ``maximum_common_subtree_isomorphism``
     - Undirected simple trees
   * - Weighted unordered embedding with skipped vertices (2018)
     - ``largest_weight_common_subtree_embedding_with_distance_penalty``
     - Undirected simple trees

For unordered inputs, node iteration and child order do not define the problem.
Ordered inputs use the order in which children appear in the graph. Both ordered
APIs default to equality of node identities; use ``node_affinity=None`` when
matching structure independently of node names.

Unordered subtree isomorphism
-----------------------------

.. code:: python

    import networkx as nx
    import networkx_algo_common_subtree as common

    left = nx.path_graph(["a", "b", "c"])
    right = nx.path_graph(["w", "x", "y", "z"])
    result = common.maximum_common_subtree_isomorphism(left, right)

    assert result.weight == 5  # three matched vertices plus two matched edges
    assert common.score_common_subtree_isomorphism(left, right, result) == 5
    print(result.mapping)      # original input nodes
    print(result.edge_paths)   # corresponding original edges/paths

``node_label="kind"`` and ``edge_label="kind"`` require equality of the named
attributes. Omitted labels allow any pair. ``node_weight`` and ``edge_weight``
accept finite signed numbers or callbacks on original nodes/endpoint pairs;
returning ``None`` forbids a pair. The default is one per matched vertex/edge.

The empty, score-zero result is allowed by default. ``allow_empty=False`` retains
negative nonempty optima and returns ``None`` when no compatible nonempty match
exists. Empty graphs are supported; cycles, disconnected nonempty graphs,
directed graphs and multigraphs are rejected by the unordered APIs.

Unordered embedding with distance penalties
-------------------------------------------

An embedding can match an edge to a longer path. This example matches two
endpoints while skipping the middle vertex in the second tree:

.. code:: python

    left = nx.Graph()
    left.add_nodes_from([("a", {"kind": "end"}), ("b", {"kind": "end"})])
    left.add_edge("a", "b")
    right = nx.path_graph(["x", "middle", "y"])
    nx.set_node_attributes(right, {"x": "end", "middle": "gap", "y": "end"}, "kind")

    result = common.largest_weight_common_subtree_embedding_with_distance_penalty(
        left, right, node_label="kind", edge_weight=0,
        skip_vertex_penalty=0.25,
    )
    assert result.weight == 1.75  # two matched vertices minus one skipped vertex
    assert common.score_common_subtree_embedding(
        left, right, result, node_label="kind", edge_weight=0,
        skip_vertex_penalty=0.25,
    ) == result.weight

The 2018 objective applies an edge reward and edge-label compatibility only
when **both** matched paths are single edges. Longer paths contribute penalties
for their skipped vertices. ``skip_vertex_penalty=float("inf")`` forbids skipping.

Both unordered functions accept ``roots=(left_root, right_root)`` to fix ambient
orientations, and ``root_to_root=True`` to require those roots to match. See the
`algorithm guide <docs/source/common_subtree_algorithm_families.rst>`_ and API
reference for these distinct root contracts.

Ordered trees
-------------

.. code:: python

    first = nx.DiGraph([(0, 1), (0, 2)])
    second = nx.DiGraph([("root", "x"), ("root", "y")])
    subtree1, subtree2, value = common.maximum_common_ordered_subtree_isomorphism(
        first, second, node_affinity=None, rooted=True,
    )
    assert value == 3

``rooted=True`` preserves the input root level; the default may choose descendant
roots. Ordered affinities are finite nonnegative weights, with zero forbidding a
match. The embedding variant permits edge contractions; its output edges need
not be edges of the input. Original node identities are retained in both modes.

Exact integer matching
----------------------

.. code:: python

    optimum = common.min_cost_assignment([[3, -2], [0, 4]])
    assert optimum.cost == -2
    assert optimum.column_for_row == (1, 0)

    matching = common.max_weight_partial_matching([[None, 5], [-2, 3]])
    assert matching.pairs == ((0, 1),)
    assert matching.weight == 5

These native APIs accept signed i64 entries and return checked i128 totals as
exact Python integers. Assignment requires a square matrix and includes dual
certificates. Partial matching allows rectangular matrices, unmatched vertices
and forbidden ``None`` entries. ``max_weight_partial_matching_deletions`` also
returns the optimum after deleting each original right vertex.

Backends and performance
------------------------

``impl="auto"`` selects Rust when installed. The ordered APIs also retain Cython
and Python implementations. For unordered algorithms, ``impl="python"`` is an
independent exhaustive reference for **small inputs**. Use ``impl="rust"`` to
require the fast graph backend instead of allowing a reference fallback, and
``common.available_unordered_backends()`` to inspect availability.

Floating implementations use f64. Very close scores and large integers can be
affected by rounding; nonfinite inputs and arithmetic overflow are rejected.
Witnesses are deterministic within a backend for fixed input iteration order;
equally optimal witnesses can differ between backends. Performance depends on
size, degree, shape and scoring. `Installed-API benchmark records
<dev/benchmarks/>`_ include conversion and witness validation.

Correctness and formal verification
-----------------------------------

The optimized ordered and unordered implementations are tested with independent
small-input oracles, differential comparisons and original-witness rescoring.
**Their complete production implementations are not yet formally verified.**
Lean proofs establish related mathematical specifications and selected actual
implementations; that distinction is part of this release's documented scope.

The exact integer matching cores have source-connected Lean correctness proofs.
Optional ordered modes expose proved implementations:

* ``impl="verified-rust", node_affinity=None``: ordered embedding with original
  token witnesses.
* ``impl="reference-rust", node_affinity=None``: the slower structural ordered
  isomorphism reference, for either root policy.
* ``impl="verified-lean"``: exact rational weighted ordered isomorphism, for
  either root policy. It accepts ``int``/``fractions.Fraction`` and returns a
  ``Fraction`` score. Its optional native executable requires a build with
  ``BUILD_LEAN_BACKEND=ON``; it is not bundled into ordinary release wheels.

Python/NetworkX conversion and native boundaries remain tested integration
layers. No published optimized running-time theorem is claimed for the native
kernels. `Proof coverage <proofs/PROOF_STATUS.md>`_ and
`exact rational usage <docs/source/verified_rational_ordered.rst>`_ describe the
checked endpoints and gaps. These optional modes do not change fast defaults.

Building and contributing
-------------------------

.. code:: bash

    python -m pip install -e '.[tests]'
    python -m pytest tests

The default source build includes Rust and Cython and requires Cargo. Explicit
``DISABLE_RUST_EXTENSIONS=1`` and ``DISABLE_C_EXTENSIONS=1`` disable their
respective builds. The optional Lean toolchain is needed only to build the
verified Lean executable or work on proofs. Guest-VM build-cache instructions
are in ``AGENTS.md``. `Release instructions <docs/releasing.md>`_ describe the
source/wheel validation and publication procedure.

References
----------

* Lozano and Valiente (2004), *On the maximum common embedded subtree problem
  for ordered trees*.
* Droschinsky, Kriege and Mutzel (2016), *Faster Algorithms for the Maximum
  Common Subtree Isomorphism Problem*, arXiv:1602.07210.
* Droschinsky, Kriege and Mutzel (2018), *Largest Weight Common Subtree
  Embeddings with Distance Penalties*, arXiv:1805.00821.

.. |Pypi| image:: https://img.shields.io/pypi/v/networkx_algo_common_subtree.svg
   :target: https://pypi.org/project/networkx-algo-common-subtree/

.. |GithubActions| image:: https://github.com/Erotemic/networkx_algo_common_subtree/actions/workflows/tests.yml/badge.svg?branch=main
   :target: https://github.com/Erotemic/networkx_algo_common_subtree/actions/workflows/tests.yml
