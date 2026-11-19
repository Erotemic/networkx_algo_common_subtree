Weighted unordered common trees
===============================

Root conventions
----------------

Both algorithm families support three objectives:

* Omitting ``roots`` computes the unrestricted unrooted optimum.
* ``roots=(left_root, right_root)`` fixes the two ambient orientations. A
  nonempty common tree has one mapped highest pair ancestral to every selected
  vertex on both sides. Its common root may lie below either supplied root.
* Adding ``root_to_root=True`` requires the supplied vertices to map together.

Roots are original NetworkX vertices. Use ``allow_empty=False`` when a nonempty
root-constrained witness is required. Pass the same root and scoring options
to the independent rescorer. In rooted embeddings, skipped vertices below the
selected common root retain the usual distance penalty.

Distance penalties
------------------

The 2018 embedding API accepts any nonnegative finite penalty and
``skip_vertex_penalty=float("inf")``. Infinity forbids skipped vertices, so
the optimum equals the 2016 common subtree isomorphism objective with the same
weights and root policy. The Rust backend uses its optimized isomorphism
solver for this case. The independent Python oracle checks the path restriction
directly. Node and edge weights must still be finite.

Pass the same penalty to ``score_common_subtree_embedding``. Both structured
path witnesses and bare node mappings reject a skipped vertex under infinity.

The root objectives can have different optima, even on identical labeled paths:

.. code-block:: python

   import networkx as nx
   from networkx_algo_common_subtree import maximum_common_subtree_isomorphism

   tree = nx.path_graph(3)
   nx.set_node_attributes(tree, {u: u for u in tree}, "label")
   assert maximum_common_subtree_isomorphism(tree, tree, node_label="label").weight == 5
   assert maximum_common_subtree_isomorphism(
       tree, tree, node_label="label", roots=(0, 2)).weight == 1
   assert maximum_common_subtree_isomorphism(
       tree, tree, node_label="label", roots=(0, 2),
       root_to_root=True, allow_empty=False) is None

API reference
-------------

.. automodule:: networkx_algo_common_subtree.unordered
   :members:
   :show-inheritance:
