import pytest

from networkx_algo_common_subtree.common_subtree_reference import (
    ExactLabelScoring,
    ReferenceLabeledTree,
    largest_weight_common_subtree_embedding_with_distance_penalty_reference,
    maximum_common_subtree_isomorphism_reference,
)


def test_reference_tree_validation():
    with pytest.raises(ValueError, match="must contain"):
        ReferenceLabeledTree([1, 2, 3], [(0, 1, 0)])
    with pytest.raises(ValueError, match="out of bounds"):
        ReferenceLabeledTree([1, 2], [(0, 9, 0)])
    with pytest.raises(ValueError, match="self-loops"):
        ReferenceLabeledTree([1, 2], [(0, 0, 0)])


def test_reference_mcsi_finds_common_labeled_path():
    left = ReferenceLabeledTree([1, 2, 3, 9], [(0, 1, 5), (1, 2, 5), (0, 3, 0)])
    right = ReferenceLabeledTree([4, 1, 2, 3], [(0, 1, 0), (1, 2, 5), (2, 3, 5)])

    result = maximum_common_subtree_isomorphism_reference(left, right)

    assert result.weight == 5.0
    assert result.node_pairs == ((0, 1), (1, 2), (2, 3))


def test_reference_mcsi_is_unordered_and_uses_child_matching():
    # The same rooted star appears with children in a different input order.
    # An ordered-tree sequence algorithm would have to account for order, but
    # this unordered formulation can map all children.
    left = ReferenceLabeledTree([0, 1, 2, 3], [(0, 1, 7), (0, 2, 7), (0, 3, 7)])
    right = ReferenceLabeledTree([0, 3, 2, 1], [(0, 1, 7), (0, 2, 7), (0, 3, 7)])

    result = maximum_common_subtree_isomorphism_reference(left, right)

    assert result.weight == 7.0
    assert result.node_pairs == ((0, 0), (1, 3), (2, 2), (3, 1))


def test_reference_mcsi_respects_edge_labels():
    left = ReferenceLabeledTree([1, 2], [(0, 1, 5)])
    right = ReferenceLabeledTree([1, 2], [(0, 1, 6)])

    result = maximum_common_subtree_isomorphism_reference(left, right)

    assert result.weight == 1.0
    assert len(result.node_pairs) == 1


def test_reference_embedding_can_skip_inserted_vertex():
    left = ReferenceLabeledTree([1, 2, 3], [(0, 1, 1), (1, 2, 1)])
    right = ReferenceLabeledTree([1, 99, 2, 3], [(0, 1, 1), (1, 2, 1), (2, 3, 1)])

    iso = maximum_common_subtree_isomorphism_reference(left, right)
    emb = largest_weight_common_subtree_embedding_with_distance_penalty_reference(
        left, right, skip_vertex_penalty=0.25
    )

    assert iso.weight == 3.0
    assert emb.weight == 4.75
    assert emb.node_pairs == ((0, 0), (1, 2), (2, 3))


def test_reference_embedding_high_penalty_falls_back_to_unskipped_solution():
    left = ReferenceLabeledTree([1, 2, 3], [(0, 1, 1), (1, 2, 1)])
    right = ReferenceLabeledTree([1, 99, 2, 3], [(0, 1, 1), (1, 2, 1), (2, 3, 1)])

    iso = maximum_common_subtree_isomorphism_reference(left, right)
    emb = largest_weight_common_subtree_embedding_with_distance_penalty_reference(
        left, right, skip_vertex_penalty=10.0
    )

    assert emb.weight == iso.weight
    assert emb.node_pairs == iso.node_pairs


def test_reference_embedding_zero_penalty_crosses_long_paths():
    left = ReferenceLabeledTree([1, 2], [(0, 1, 4)])
    right = ReferenceLabeledTree([1, 9, 8, 2], [(0, 1, 4), (1, 2, 4), (2, 3, 4)])

    iso = maximum_common_subtree_isomorphism_reference(left, right)
    emb = largest_weight_common_subtree_embedding_with_distance_penalty_reference(
        left, right, skip_vertex_penalty=0.0
    )

    assert iso.weight == 1.0
    assert emb.weight == 3.0
    assert emb.node_pairs == ((0, 0), (1, 3))


def test_reference_scoring_weights_change_objective():
    class LabelProductScoring(ExactLabelScoring):
        def node_weight(self, left, u, right, v):
            if left.node_label(u) % 2 == right.node_label(v) % 2:
                return float(left.node_label(u) * right.node_label(v))
            return None

    left = ReferenceLabeledTree([2, 4], [(0, 1, 1)])
    right = ReferenceLabeledTree([6, 8], [(0, 1, 1)])

    result = maximum_common_subtree_isomorphism_reference(left, right, LabelProductScoring())

    assert result.weight == 45.0  # 2*6 + 4*8 + edge weight 1
