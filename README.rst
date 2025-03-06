The networkx_algo_common_subtree Module
=======================================

|Pypi| |PypiDownloads| |GithubActions| |Codecov|

Networkx algorithms for maximum common ordered subtree minors (or embedding)
and maximum common subtree isomorphism. Contains pure python and cython
optimized versions.


At its core the ``maximum_common_ordered_subtree_embedding`` function is an implementation of:

.. code::

    Lozano, Antoni, and Gabriel Valiente.
        "On the maximum common embedded subtree problem for ordered trees."
        String Algorithmics (2004): 155-170.
        https://pdfs.semanticscholar.org/0b6e/061af02353f7d9b887f9a378be70be64d165.pdf


And ``maximum_common_ordered_subtree_isomorphism`` is a variant of the above
algorithm that returns common subtree ismorphism instead of subtree minors.


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
