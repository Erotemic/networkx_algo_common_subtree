from itertools import product

import pytest

from networkx_algo_common_subtree.common_subtree_reference import (
    ReferenceLabeledTree,
    largest_weight_common_subtree_embedding_with_distance_penalty_reference,
    maximum_common_subtree_isomorphism_reference,
    score_embedding_witness,
    score_subtree_isomorphism_witness,
)


def _prufer_edges(code):
    n = len(code) + 2
    degree = [1] * n
    for node in code:
        degree[node] += 1
    edges = []
    for node in code:
        leaf = min(idx for idx, deg in enumerate(degree) if deg == 1)
        edges.append((leaf, node, 1))
        degree[leaf] -= 1
        degree[node] -= 1
    last = [idx for idx, deg in enumerate(degree) if deg == 1]
    edges.append((last[0], last[1], 1))
    return tuple(sorted((min(u, v), max(u, v), label) for u, v, label in edges))


def _all_labeled_tree_shapes(n):
    if n == 1:
        return [()]
    seen = set()
    out = []
    for code in product(range(n), repeat=n - 2):
        edges = _prufer_edges(code)
        if edges not in seen:
            seen.add(edges)
            out.append(edges)
    return out


def _renumber_tree(tree, perm):
    inverse = {old: new for new, old in enumerate(perm)}
    labels = [tree.node_label(old) for old in perm]
    edges = []
    for u, v, label in tree.edges:
        nu = inverse[u]
        nv = inverse[v]
        edges.append((nu, nv, label))
    return ReferenceLabeledTree(labels, edges)


def _binary_label_tree(n, edges, offset=0):
    return ReferenceLabeledTree([(idx + offset) % 2 for idx in range(n)], edges)


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_mcsi_identity_score_on_all_small_labeled_tree_shapes(n):
    for edges in _all_labeled_tree_shapes(n):
        tree = _binary_label_tree(n, edges)
        result = maximum_common_subtree_isomorphism_reference(tree, tree)
        assert result.weight == pytest.approx(2 * n - 1)
        assert score_subtree_isomorphism_witness(tree, tree, result.node_pairs) == pytest.approx(result.weight)


def test_mcsi_symmetry_on_all_small_labeled_tree_shapes():
    shapes = []
    for n in range(1, 5):
        shapes.extend((_binary_label_tree(n, edges), n, edges) for edges in _all_labeled_tree_shapes(n))

    for left, _left_n, _left_edges in shapes:
        for right, _right_n, _right_edges in shapes:
            forward = maximum_common_subtree_isomorphism_reference(left, right)
            reverse = maximum_common_subtree_isomorphism_reference(right, left)
            assert forward.weight == pytest.approx(reverse.weight)
            assert score_subtree_isomorphism_witness(left, right, forward.node_pairs) == pytest.approx(forward.weight)
            assert score_subtree_isomorphism_witness(right, left, reverse.node_pairs) == pytest.approx(reverse.weight)


def test_mcsi_is_invariant_to_node_renumbering():
    tree = ReferenceLabeledTree([0, 1, 0, 1], [(0, 1, 1), (1, 2, 1), (1, 3, 1)])
    other = ReferenceLabeledTree([1, 0, 1, 0], [(0, 1, 1), (1, 2, 1), (1, 3, 1)])
    renamed_tree = _renumber_tree(tree, [2, 1, 3, 0])
    renamed_other = _renumber_tree(other, [3, 1, 0, 2])

    original = maximum_common_subtree_isomorphism_reference(tree, other)
    renamed = maximum_common_subtree_isomorphism_reference(renamed_tree, renamed_other)

    assert renamed.weight == pytest.approx(original.weight)


def test_embedding_penalty_monotonicity_and_witness_rescoring():
    left = ReferenceLabeledTree([1, 2, 3], [(0, 1, 1), (1, 2, 1)])
    right = ReferenceLabeledTree([1, 99, 2, 3], [(0, 1, 1), (1, 2, 1), (2, 3, 1)])

    previous = None
    for penalty in [0.0, 0.25, 1.0, 10.0]:
        result = largest_weight_common_subtree_embedding_with_distance_penalty_reference(
            left, right, skip_vertex_penalty=penalty
        )
        assert score_embedding_witness(left, right, result.node_pairs, skip_vertex_penalty=penalty) == pytest.approx(
            result.weight
        )
        if previous is not None:
            assert result.weight <= previous + 1.0e-9
        previous = result.weight
