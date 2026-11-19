networkx\_algo\_common\_subtree.balanced\_embedding\_cython module
==================================================================

.. py:module:: networkx_algo_common_subtree.balanced_embedding_cython

Select this compiled comparison backend with ``impl="iter-cython"`` in
:func:`networkx_algo_common_subtree.balanced_embedding.longest_common_balanced_embedding`.
It supports string/tuple tokens, original-node mappings and finite nonnegative
f64 affinities through that public interface. The default build includes it;
Rust-only ABI3 wheels use the Rust and Python backends.
