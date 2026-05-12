Correctness strategy for weighted common subtree algorithms
===========================================================

This page records the current proof-oriented validation plan for the
paper-derived weighted common subtree algorithms in
``rust/crates/common_subtree_algorithms`` and
``networkx_algo_common_subtree.common_subtree_reference``.

The goal is not yet a machine-checked proof.  The goal is to make a convincing,
auditable case that each implementation agrees with the mathematical problem it
claims to solve, while leaving clear seams for future Lean formalization.

Problem scope
-------------

The new implementation family targets graph-only algorithms for unordered,
weighted trees:

* maximum common subtree isomorphism, abbreviated **MCSI** only after it has been
  defined; and
* largest-weight common subtree embeddings with distance penalties.

The intended semantics come from the public papers by Droschinsky, Kriege, and
Mutzel, not from any application-specific codebase.  The implementation is
limited to ordinary labeled trees, scoring hooks for node and edge
compatibility, objective values, and witness mappings.

Definitions used by the implementation
--------------------------------------

Tree
    A finite, undirected, connected, acyclic graph.  The current reference data
    structures attach integer labels to nodes and edges.

Connected subtree
    A nonempty connected vertex subset together with all tree edges induced by
    that subset.

Subtree isomorphism witness
    A bijection between two connected vertex subsets that preserves adjacency
    and whose mapped node and edge pairs are compatible under the scoring
    function.

Rooted branch state
    A pair ``(u, parent_u)`` in the first tree and ``(v, parent_v)`` in the
    second tree.  The state only sees the components reachable from ``u`` and
    ``v`` without crossing the parent edges.

Embedding skeleton
    For a selected vertex set in a tree, connect two selected vertices when the
    path between them contains no other selected vertex.  These skeleton edges
    are the embedded common-tree edges; their realizations in the input trees may
    be longer paths.

Distance penalty
    A cost charged for skipped internal vertices along embedded paths.  In the
    current prototype this is represented by a single ``skip_vertex_penalty``.

Witness
    A concrete set of mapped node pairs.  A witness is stronger than a score
    alone because it can be independently checked for structural validity and
    rescored from first principles.

MCSI recurrence and proof obligations
-------------------------------------

For a rooted state that maps ``u`` to ``v``, the implementation obligation is to
compute::

    node_weight(u, v)
      + maximum_weight_matching(
          edge_weight((u, u_child), (v, v_child))
          + rooted_score(u_child, u, v_child, v)
        )

where the matching ranges over compatible child branches of ``u`` and ``v``.
Children may remain unmatched, which lets the optimum be a proper connected
subtree of either input.

The correctness argument has four main lemmas.

Feasibility lemma
    Every solution assembled by the recurrence is a valid subtree isomorphism:
    the root pair is compatible, each selected child subproblem is valid by
    induction, and the matching prevents two selected left branches from using
    the same right branch.

Branch-independence lemma
    In a tree, deleting a mapped root separates the remaining choices into
    independent neighbor branches.  Once ``u`` is mapped to ``v``, a branch of
    ``u`` can interact with at most one branch of ``v``.

Matching lemma
    Choosing the best compatible set of independent child-branch continuations is
    exactly a maximum-weight bipartite matching instance with optional unmatched
    vertices.

Induction theorem
    Assuming recursive child states are optimal, the matching over their optimal
    values is optimal for the rooted state.  Taking the best rooted state over
    all root pairs gives the unrooted optimum.

Distance-penalized embedding proof obligations
----------------------------------------------

The embedding prototype uses the same branch-matching idea, but a mapped common
edge may be realized by a path in either input tree.  The additional obligations
are:

Path-accounting lemma
    The weight of a skeleton edge must include the compatible endpoint-edge
    contribution and subtract the penalty for every skipped internal vertex on
    both realized paths.

Embedding branch-independence lemma
    Once a mapped root pair is fixed, each selected continuation still occupies a
    distinct branch in each tree.  Skipped internal vertices only change the
    continuation weight; they do not create interactions between different
    branches.

Penalty monotonicity check
    Increasing the skip penalty must not increase the optimal embedding score
    for fixed inputs and scoring functions.

High-penalty sanity check
    When skipping is made more expensive than any useful skipped continuation,
    the embedding score should agree with an unskipped subtree-isomorphism
    solution on the same examples.

Implementation proof map
------------------------

``rust/crates/common_subtree_algorithms/src/matching.rs``
    Implements optional-vertex maximum-weight bipartite matching.  Its tests
    compare the Hungarian-style solver against exhaustive enumeration over all
    compatible row/column assignments for small matrices.

``rust/crates/common_subtree_algorithms/src/tree.rs``
    Implements the rooted dynamic programs and returns witnesses.  Its tests
    compare MCSI scores against exhaustive subtree/bijection enumeration and
    independently validate returned witnesses.

``networkx_algo_common_subtree.common_subtree_reference``
    Provides the slow executable specification.  It directly enumerates small
    connected subtrees, embedding skeletons, and bijections.  It also exposes
    witness rescoring helpers so tests can check that a reported witness really
    has the reported objective value.

``tests/fixtures/common_subtree_cases.json``
    Contains small, named cases with expected scores and witnesses.  These
    examples are intentionally simple enough to audit by hand and stable enough
    to reuse later from Rust, Python, and formal proof experiments.

Mechanical checks currently targeted
------------------------------------

The current validation stack is intentionally redundant:

* brute-force matching versus optimized matching on deterministic matrices;
* brute-force MCSI versus optimized Rust MCSI on handwritten and exhaustive
  small generated trees;
* witness validation and rescoring for both MCSI and embedding examples;
* Python fixture tests with expected scores and witness mappings;
* metamorphic checks such as input symmetry, node-renaming invariance, identity
  scores, and penalty monotonicity.

These checks do not constitute a formal proof, but they make the failure modes
narrower.  A future Lean development can reuse the same decomposition: formalize
witness validity, prove the rooted recurrence, prove the matching reduction, and
then connect those theorems to executable extraction or audited implementation
boundaries.

Known limitations
-----------------

The Rust embedding routine is still described as a prototype.  Before treating
it as a final implementation of the 2018 algorithm, the scoring API and path
penalty semantics should be checked against paper examples and additional
fixtures.  In particular, richer edge/path scoring may require more information
than the current first-step edge compatibility hook exposes.
