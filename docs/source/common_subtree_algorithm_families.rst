Common subtree algorithm families
=================================

This repository now has two conceptually different families of common-subtree
algorithms. They share similar words in their names, but they solve different
modeling problems and use different algorithmic reductions.

Existing Lozano-Valiente ordered-tree algorithms
------------------------------------------------

The existing public Python API is centered on ordered trees:

* ``maximum_common_ordered_subtree_embedding``
* ``maximum_common_ordered_subtree_isomorphism``

These are based on Antoni Lozano and Gabriel Valiente, "On the maximum common
embedded subtree problem for ordered trees." The implementation converts ordered
trees into balanced sequences and solves longest-common-balanced-sequence style
subproblems. The child order is part of the input structure, so two trees with
the same unordered branching pattern can have different answers if their child
orders differ.

The embedding variant allows edge contractions, so the returned common structure
can be a minor of each input tree. The isomorphism variant is stricter and
returns proper subtrees, but it is still built on the ordered balanced-sequence
view.

New Droschinsky-Kriege-Mutzel weighted-tree algorithms
------------------------------------------------------

The experimental ``common_subtree_algorithms`` Rust crate targets the graph-only
algorithms described by Droschinsky, Kriege, and Mutzel:

* "Faster Algorithms for the Maximum Common Subtree Isomorphism Problem",
  arXiv:1602.07210.
* "Largest Weight Common Subtree Embeddings with Distance Penalties",
  arXiv:1805.00821.

The key modeling differences are:

* the trees are unordered, and the current implementation treats them as
  undirected labeled trees;
* matching compatible children is a maximum-weight bipartite matching problem,
  not a balanced-sequence subsequence problem;
* node and edge compatibility are represented by explicit weight functions;
* the 2018 embedding objective can penalize skipped vertices instead of treating
  every contraction as equally free.

Practical consequences
----------------------

The older ordered-tree algorithms are a good fit when sibling order is meaningful
or when the input is already naturally represented as a balanced sequence. They
are not designed to be invariant to arbitrary permutations of child order.

The newer paper-derived algorithms are a better fit when trees should be treated
as graph objects with unordered neighborhoods, explicit labels, and weighted
compatibility. A rooted dynamic-programming state still appears internally, but
root choices are used to solve an unordered tree problem rather than to encode an
ordered traversal.

A small example is a star with three labeled leaves. If the leaves appear in a
different sibling order, an ordered-tree algorithm may lose matches because the
sequence order changed. The unordered weighted-tree algorithm can still match all
three leaves by solving the child correspondence as a bipartite matching.

Correctness and validation
--------------------------

The page :doc:`common_subtree_correctness` records the proof-oriented
validation plan for the new weighted-tree algorithms.  It distinguishes the
mathematical recurrence, the slow executable specification, the optimized Rust
implementation, and the fixture/property tests used to connect them.

Status in this repository
-------------------------

The Lozano-Valiente family is the mature existing API. The
Droschinsky-Kriege-Mutzel family is currently sequestered as an experimental
Rust crate plus a slow Python reference implementation. It should remain behind
extra tests until the exact semantics and Python-facing API are stable.
