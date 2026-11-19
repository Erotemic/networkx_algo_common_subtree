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
supports Python 3.14; the regular Rust/Cython wheel matrix targets 3.10–3.13.
If pip needs to build from source, install Cargo/Rust and a C/C++ toolchain first. See `build and platform details <docs/packaging.md>`_.

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

Ordered trees: isomorphism and embedding
----------------------------------------

Consider two directed ordered trees with different branching and child order.
The drawings use `nx.write_network_text
<https://networkx.org/documentation/stable/reference/readwrite/generated/networkx.readwrite.text.write_network_text.html>`_
(NetworkX 3.1 or newer):

.. code:: python

    >>> import networkx as nx
    >>> tree1 = nx.DiGraph()
    >>> tree2 = nx.DiGraph()
    >>> tree1.add_edges_from([(0, 2), (5, 7), (5, 4), (5, 3), (2, 5), (2, 6), (3, 1)])
    >>> tree2.add_edges_from([(0, 6), (0, 1), (1, 5), (6, 2), (5, 4), (5, 3), (5, 7)])
    >>> print('Tree 1:')
    Tree 1:
    >>> nx.write_network_text(tree1)
    ╙── 0
        └─╼ 2
            ├─╼ 5
            │   ├─╼ 7
            │   ├─╼ 4
            │   └─╼ 3
            │       └─╼ 1
            └─╼ 6
    >>> print('Tree 2:')
    Tree 2:
    >>> nx.write_network_text(tree2)
    ╙── 0
        ├─╼ 6
        │   └─╼ 2
        └─╼ 1
            └─╼ 5
                ├─╼ 4
                ├─╼ 3
                └─╼ 7


The maximum common ordered isomorphism (a strict common subtree structure) is:

.. code:: python

    >>> import networkx_algo_common_subtree
    >>> subtree1, subtree2, score = networkx_algo_common_subtree.maximum_common_ordered_subtree_isomorphism(tree1, tree2)
    >>> print(f'score={score:g}')
    score=3
    >>> print('Isomorphic Subtree 1:')
    Isomorphic Subtree 1:
    >>> nx.write_network_text(subtree1)
    ╙── 5
        ├─╼ 4
        └─╼ 3
    >>> print('Isomorphic Subtree 2:')
    Isomorphic Subtree 2:
    >>> nx.write_network_text(subtree2)
    ╙── 5
        ├─╼ 4
        └─╼ 3

The biggest common structure between both of the original trees is the subtree
involving 5, 3, 4. Notice that the (5, 7) edge is not included because these
are **ordered** subtrees. In tree 1, the (5, 7) edge is before the (5, 4) edge
and in the second it is after it, so it is not included because the edges are
not in the same order.


This substructure can be generalized by allowing edges in the original graphs
to be collapsed, which can produce larger common substructures. This is the
maximum common ordered embedding.

.. code:: python

    >>> import networkx_algo_common_subtree
    >>> subtree1, subtree2, score = networkx_algo_common_subtree.maximum_common_ordered_subtree_embedding(tree1, tree2)
    >>> print(f'score={score:g}')
    score=4
    >>> print('Embedded Subtree 1:')
    Embedded Subtree 1:
    >>> nx.write_network_text(subtree1)
    ╙── 0
        └─╼ 5
            ├─╼ 4
            └─╼ 3
    >>> print('Embedded Subtree 2:')
    Embedded Subtree 2:
    >>> nx.write_network_text(subtree2)
    ╙── 0
        └─╼ 5
            ├─╼ 4
            └─╼ 3

In this example, the edges (0, 2) and (2, 5) in first tree were collapsed into
(0, 5). Similarly in the second tree the edges (0, 1) and (1, 5) were collapsed
into (0, 5), thus increasing the size of the common ordered subtree.

``rooted=True`` preserves the input root level; the default may choose descendant
roots. Ordered affinities are finite nonnegative weights, with zero forbidding a
match. Original node identities are retained in both modes.

Unordered subtree isomorphism
-----------------------------

Now treat the same trees as undirected and ignore sibling order. Give every
node its original identity as a label, so we still compare the same named
nodes. Use zero edge weight to count matched vertices, as in the ordered demo:

.. code:: python

    >>> left = tree1.to_undirected()
    >>> right = tree2.to_undirected()
    >>> for tree in (left, right):
    ...     nx.set_node_attributes(tree, {node: node for node in tree}, "name")
    >>> result = networkx_algo_common_subtree.maximum_common_subtree_isomorphism(
    ...     left, right, node_label="name", edge_weight=0,
    ... )
    >>> result.weight
    4.0
    >>> sorted(result.mapping.items())
    [(3, 3), (4, 4), (5, 5), (7, 7)]
    >>> networkx_algo_common_subtree.score_common_subtree_isomorphism(
    ...     left, right, result, node_label="name", edge_weight=0,
    ... )
    4.0
    >>> nx.write_network_text(left.subgraph(result.mapping), sources=[5])
    ╙── 5
        ├── 7
        ├── 4
        └── 3
    >>> nx.write_network_text(right.subgraph(result.mapping.values()), sources=[5])
    ╙── 5
        ├── 4
        ├── 3
        └── 7

All three leaves can now match, including node 7, even though their order differs.
The unordered isomorphism has four vertices; the ordered isomorphism had three.

``node_label="name"`` and ``edge_label="name"`` require equality of the named
attributes. Omitted labels allow any pair. ``node_weight`` and ``edge_weight``
accept finite signed numbers or callbacks on original nodes/endpoint pairs;
returning ``None`` forbids a pair. The default is one per matched vertex/edge,
so omit ``edge_weight=0`` when edges should contribute to the score too.

The empty, score-zero result is allowed by default. ``allow_empty=False`` retains
negative nonempty optima and returns ``None`` when no compatible nonempty match
exists. Empty graphs are supported; cycles, disconnected nonempty graphs,
directed graphs and multigraphs are rejected by the unordered APIs.

Unordered embedding with distance penalties
-------------------------------------------

Allowing paths in place of edges lets the same pair of trees also match node 0.
The path from 0 to 5 skips node 2 in the first tree and node 1 in the second:

.. code:: python

    >>> embedded = networkx_algo_common_subtree.largest_weight_common_subtree_embedding_with_distance_penalty(
    ...     left, right, node_label="name", edge_weight=0,
    ...     skip_vertex_penalty=0.25,
    ... )
    >>> embedded.weight
    4.5
    >>> sorted(embedded.mapping.items())
    [(0, 0), (3, 3), (4, 4), (5, 5), (7, 7)]
    >>> networkx_algo_common_subtree.score_common_subtree_embedding(
    ...     left, right, embedded, node_label="name", edge_weight=0,
    ...     skip_vertex_penalty=0.25,
    ... )
    4.5
    >>> [paths for paths in embedded.edge_paths if len(paths[0]) > 2]
    [((0, 2, 5), (0, 1, 5))]

The five matched vertices contribute 5; the two skipped vertices cost 0.5.
The 2018 objective applies an edge reward and edge-label compatibility only
when **both** matched paths are single edges. Longer paths contribute penalties
for their skipped vertices. ``skip_vertex_penalty=float("inf")`` forbids skipping.

Both unordered functions accept ``roots=(left_root, right_root)`` to fix ambient
orientations, and ``root_to_root=True`` to require those roots to match. See the
`algorithm guide <docs/source/common_subtree_algorithm_families.rst>`_ and API
reference for these distinct root contracts.

Exact integer matching
----------------------

.. code:: python

    >>> optimum = networkx_algo_common_subtree.min_cost_assignment([[3, -2], [0, 4]])
    >>> optimum.cost, optimum.column_for_row
    (-2, (1, 0))
    >>> matching = networkx_algo_common_subtree.max_weight_partial_matching([[None, 5], [-2, 3]])
    >>> matching.pairs, matching.weight
    (((0, 1),), 5)

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
``networkx_algo_common_subtree.available_unordered_backends()`` to inspect availability.

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

* Lozano and Valiente (2004), `On the maximum common embedded subtree problem
  for ordered trees <https://www.cs.upc.edu/~antoni/subtree.pdf>`_.
* Droschinsky, Kriege and Mutzel (2016), `Faster Algorithms for the Maximum
  Common Subtree Isomorphism Problem <https://arxiv.org/abs/1602.07210v4>`_.
* Droschinsky, Kriege and Mutzel (2018), `Largest Weight Common Subtree
  Embeddings with Distance Penalties <https://arxiv.org/abs/1805.00821>`_.

.. |Pypi| image:: https://img.shields.io/pypi/v/networkx_algo_common_subtree.svg
   :target: https://pypi.org/project/networkx-algo-common-subtree/

.. |GithubActions| image:: https://github.com/Erotemic/networkx_algo_common_subtree/actions/workflows/tests.yml/badge.svg?branch=main
   :target: https://github.com/Erotemic/networkx_algo_common_subtree/actions/workflows/tests.yml
