The networkx_algo_common_subtree Module
=======================================

|Pypi| |PypiDownloads| |GithubActions| |Codecov|

Networkx algorithms for maximum common ordered subtree minors (or embedding)
and maximum common subtree isomorphism. Contains pure python and cython
optimized versions, plus Rust/PyO3 backends. Weighted unordered isomorphism
(Droschinsky 2016), distance-penalized embedding (2018), and exact integer
assignment/partial matching are also available from Python.

The default build includes Rust and Cython. An opt-in Rust-only ``cp310-abi3``
wheel is tested across CPython 3.10–3.14; see `build and validation details
<docs/packaging.md>`_. This does not change the package's partial verification
status.

Weighted unordered trees
------------------------

Install with ``python -m pip install .`` (Rust/Cargo and a C/C++ toolchain are
needed for source builds). The default build includes Rust and Cython.

.. code:: python

    import networkx as nx
    import networkx_algo_common_subtree as common

    left, right = nx.path_graph(3), nx.path_graph(4)
    result = common.maximum_common_subtree_isomorphism(left, right, impl="rust")
    assert result.weight == 5  # three vertices plus two edges
    assert common.score_common_subtree_isomorphism(left, right, result) == 5
    print(result.mapping)  # original input vertices

    embedded = common.largest_weight_common_subtree_embedding_with_distance_penalty(
        left, right, skip_vertex_penalty=0.25, impl="rust")
    print(embedded.edge_paths)  # aligned paths, including skipped vertices

Inputs are undirected simple connected NetworkX trees, or empty graphs.
``node_label="name"`` and ``edge_label="name"`` require equality of the named
attributes; omitted labels allow any pair. ``node_weight`` and ``edge_weight``
accept finite signed numbers or callbacks on original nodes/endpoint pairs;
a callback may return ``None`` to forbid a pair. Callbacks are evaluated once
per compatible pair before the Rust solver. ``allow_empty=False`` preserves
negative nonempty optima and returns ``None`` when no nonempty solution exists.
The default ``impl="auto"`` selects Rust if installed; ``impl="python"`` is
an independent exhaustive reference suitable for small inputs.

The 2018 objective rewards and checks edge labels only when both matched paths
are single edges. Longer paths incur penalties for their skipped vertices.
The independent ``score_common_subtree_embedding`` validates the mapping and
paths and recomputes this objective. Ties are deterministic within a backend
for fixed input iteration order; witnesses can differ between backends.
Graph weights use f64, with nonfinite inputs/overflow rejected. These graph
Rust implementations are tested reference dynamic programs; their production
source refinement and published optimized complexity are still pending.

Exact weighted matching
-----------------------

.. code:: python

    optimum = common.min_cost_assignment([[3, -2], [0, 4]])
    assert optimum.cost == -2
    assert optimum.column_for_row == (1, 0)
    matching = common.max_weight_partial_matching([[None, 5], [-2, 3]])
    assert matching.pairs == ((0, 1),)
    assert matching.weight == 5

These Rust-only APIs accept i64 integer entries and return exact checked i128
totals as Python integers. Assignment requires a square matrix and returns
attaining dual potentials; partial matching permits rectangular matrices,
forbidden ``None`` edges and unmatched vertices. The actual integer Rust cores
have Lean correctness/refinement proofs. The Python conversion and wrappers
are tested, and the floating-point matching used inside the graph algorithms
has a separate assurance boundary.


At its core the ``maximum_common_ordered_subtree_embedding`` function is an implementation of:

.. code::

    Lozano, Antoni, and Gabriel Valiente.
        "On the maximum common embedded subtree problem for ordered trees."
        String Algorithmics (2004): 155-170.
        https://pdfs.semanticscholar.org/0b6e/061af02353f7d9b887f9a378be70be64d165.pdf


And ``maximum_common_ordered_subtree_isomorphism`` is a variant of the above
algorithm that returns common subtree ismorphism instead of subtree minors.

For ordered isomorphism, ``rooted=True`` preserves the input root level:
every nonempty result for connected input trees retains both original roots.
The default allows descendant roots. The balanced-sequence isomorphism API
accepts the same option to preserve its implicit forest parent. Both modes
support the existing affinity scoring and original-node mappings.


Demo
----

Consider two directed ordered trees (the algorithm also works on undirected
ordered trees):

.. code:: python

    >>> import networkx as nx
    >>> tree1 = nx.DiGraph()
    >>> tree2 = nx.DiGraph()
    >>> tree1.add_edges_from([(0, 2), (5, 7), (5, 4), (5, 3), (2, 5), (2, 6), (3, 1)])
    >>> tree2.add_edges_from([(0, 6), (0, 1), (1, 5), (6, 2), (5, 4), (5, 3), (5, 7)])
    >>> print('Tree 1:')
    >>> nx.write_network_text(tree1)
    >>> print('Tree 2:')
    >>> nx.write_network_text(tree2)
    Tree 1:
    ╙── 0
        └─╼ 2
            ├─╼ 5
            │   ├─╼ 7
            │   ├─╼ 4
            │   └─╼ 3
            │       └─╼ 1
            └─╼ 6
    Tree 2:
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
    >>> print(f'{score=}')
    >>> print('Isomorphic Subtree 1:')
    >>> nx.write_network_text(subtree1)
    >>> print('Isomorphic Subtree 2:')
    >>> nx.write_network_text(subtree2)
    score=3
    Isomorphic Subtree 1:
    ╙── 5
        ├─╼ 4
        └─╼ 3
    Isomorphic Subtree 2:
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
    >>> print(f'{score=}')
    >>> print('Embedded Subtree 1:')
    >>> nx.write_network_text(subtree1)
    >>> print('Embedded Subtree 2:')
    >>> nx.write_network_text(subtree2)
    score=4
    Embedded Subtree 1:
    ╙── 0
        └─╼ 5
            ├─╼ 4
            └─╼ 3
    Embedded Subtree 2:
    ╙── 0
        └─╼ 5
            ├─╼ 4
            └─╼ 3

In this example, the edges (0, 2) and (2, 5) in first tree were collapsed into
(0, 5). Similarly in the second tree the edges (0, 1) and (1, 5) were collapsed
into (0, 5), thus increasing the size of the common ordered subtree.

Other Information
-----------------

Standalone versions of code were originally submitted as PRs to networkx
proper:

https://github.com/networkx/networkx/pull/4350
https://github.com/networkx/networkx/pull/4327

However, these algorithms are roughly ``O(N⁴)``, they require a a fast binary
(e.g. C / cython) implementation to work on graphs of reasonable size. Thus
they are unlikely to be added to mainline networkx.


These algorithms are components of algorithms in ``torch_liberator``, see related
information:

+----------------------+------------------------------------------------------------+
| TorchLiberator       | https://gitlab.kitware.com/computer-vision/torch_liberator |
+----------------------+------------------------------------------------------------+
| Torch Hackathon 2021 | `Youtube Video`_ and `Google Slides`_                      |
+----------------------+------------------------------------------------------------+

.. _Youtube Video: https://www.youtube.com/watch?v=GQqtn61iNsc
.. _Google Slides: https://docs.google.com/presentation/d/1w9XHkPjtLRj29dw50WP0rSHRRlEfhksP_Sf8XldTSYE




.. |Pypi| image:: https://img.shields.io/pypi/v/networkx_algo_common_subtree.svg
    :target: https://pypi.python.org/pypi/networkx_algo_common_subtree

.. |PypiDownloads| image:: https://img.shields.io/pypi/dm/networkx_algo_common_subtree.svg
    :target: https://pypistats.org/packages/networkx_algo_common_subtree

.. |GithubActions| image:: https://github.com/Erotemic/networkx_algo_common_subtree/actions/workflows/tests.yml/badge.svg?branch=main
    :target: https://github.com/Erotemic/networkx_algo_common_subtree/actions?query=branch%3Amain

.. |Codecov| image:: https://codecov.io/github/Erotemic/networkx_algo_common_subtree/badge.svg?branch=main&service=github
    :target: https://codecov.io/github/Erotemic/networkx_algo_common_subtree?branch=main


Build Notes
-----------

This project now uses ``scikit-build-core`` as its PEP 517 backend. Typical
local workflows are:

.. code:: bash

    pip install -e .
    pip wheel .

Build toggles:

* ``DISABLE_C_EXTENSIONS=1`` disables Cython extension builds.
* ``DISABLE_RUST_EXTENSIONS=1`` disables the Rust extension build.

Rust backend notes:

* The Rust extension module is ``networkx_algo_common_subtree._rust``.
* If built, ``impl="auto"`` prefers Rust, then Cython, then pure Python.

* ``impl="verified-rust", node_affinity=None`` opts into the proved unweighted
  Boolean contraction core. Typed bracket pairs are validated and original
  string/list/tuple values are preserved. It is a reference implementation with
  shared-memo guided reconstruction; automatic dispatch continues to use the existing
  general affinity backend. Include restricted implementations in discovery with
  ``available_impls_longest_common_balanced_embedding(include_restricted=True)``.
  The Lean theorem covers the Rust Boolean core and original token indices;
  Python token conversion, PyO3 and NetworkX graph conversion are tested
  integration boundaries. See ``proofs/PROOF_STATUS.md`` for exact coverage.
