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
    assert emb.weight == 3.75
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
    assert emb.weight == 2.0
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


@pytest.mark.parametrize("label", [5, 9])
def test_embedding_paper_skipped_path_discriminator(label):
    from networkx_algo_common_subtree.common_subtree_reference import score_embedding_witness
    left = ReferenceLabeledTree([1, 2], [(0, 1, 5)])
    right = ReferenceLabeledTree([1, 99, 2], [(0, 1, label), (1, 2, label)])
    result = largest_weight_common_subtree_embedding_with_distance_penalty_reference(
        left, right, skip_vertex_penalty=0.25)
    assert result.weight == 1.75
    assert score_embedding_witness(left, right, result.node_pairs,
                                   skip_vertex_penalty=0.25) == 1.75


def test_embedding_rejects_omitted_branch_point():
    from networkx_algo_common_subtree.common_subtree_reference import score_embedding_witness
    star = ReferenceLabeledTree([0, 1, 1, 1], [(0, 1, 5), (0, 2, 5), (0, 3, 5)])
    with pytest.raises(ValueError, match="overlap"):
        score_embedding_witness(star, star, [(1, 1), (2, 2), (3, 3)])
    result = largest_weight_common_subtree_embedding_with_distance_penalty_reference(star, star)
    assert result.weight == 7.0


@pytest.mark.parametrize("penalty", [-1, float("nan"), -float("inf")])
def test_embedding_rejects_invalid_penalty(penalty):
    tree = ReferenceLabeledTree([0], [])
    with pytest.raises(ValueError, match="nonnegative"):
        largest_weight_common_subtree_embedding_with_distance_penalty_reference(
            tree, tree, skip_vertex_penalty=penalty)


@pytest.mark.parametrize("weight", [-2.0, 0.0])
def test_nonempty_reference_retains_nonpositive_optima(weight):
    from networkx_algo_common_subtree.common_subtree_reference import (
        maximum_nonempty_common_subtree_isomorphism_reference,
        largest_weight_nonempty_common_subtree_embedding_with_distance_penalty_reference,
    )
    tree = ReferenceLabeledTree([1, 1], [(0, 1, 0)])
    scoring = ExactLabelScoring(node_match_weight=weight, edge_match_weight=-1.0)
    iso = maximum_nonempty_common_subtree_isomorphism_reference(tree, tree, scoring)
    emb = largest_weight_nonempty_common_subtree_embedding_with_distance_penalty_reference(
        tree, tree, scoring, 0.25)
    assert iso is not None and emb is not None
    assert iso.weight == emb.weight == weight
    assert len(iso.node_pairs) == len(emb.node_pairs) == 1
    assert maximum_common_subtree_isomorphism_reference(tree, tree, scoring).node_pairs == ()


def test_nonempty_reference_distinguishes_infeasible_mapping():
    from networkx_algo_common_subtree.common_subtree_reference import (
        maximum_nonempty_common_subtree_isomorphism_reference,
        largest_weight_nonempty_common_subtree_embedding_with_distance_penalty_reference,
    )
    left, right = ReferenceLabeledTree([1], []), ReferenceLabeledTree([2], [])
    assert maximum_nonempty_common_subtree_isomorphism_reference(left, right) is None
    assert largest_weight_nonempty_common_subtree_embedding_with_distance_penalty_reference(left, right) is None


@pytest.mark.parametrize("size", [1, 2])
def test_positive_gains_below_old_threshold_are_retained(size):
    tree = ReferenceLabeledTree([1] * size, [(0, 1, 0)] if size == 2 else [])
    tiny = 5.0e-12
    scoring = ExactLabelScoring(node_match_weight=tiny, edge_match_weight=0.0)
    iso = maximum_common_subtree_isomorphism_reference(tree, tree, scoring)
    emb = largest_weight_common_subtree_embedding_with_distance_penalty_reference(tree, tree, scoring)
    assert iso.weight == size * tiny
    assert emb.weight == size * tiny
    assert len(iso.node_pairs) == size
    assert len(emb.node_pairs) == size


def test_close_scores_are_not_treated_as_equal():
    class CloseScores(ExactLabelScoring):
        def node_weight(self, left, u, right, v):
            return 1.0 + v * 5.0e-10

        def edge_weight(self, *args):
            return None

    left = ReferenceLabeledTree([1], [])
    right = ReferenceLabeledTree([1, 1], [(0, 1, 0)])
    iso = maximum_common_subtree_isomorphism_reference(left, right, CloseScores())
    emb = largest_weight_common_subtree_embedding_with_distance_penalty_reference(left, right, CloseScores())
    assert iso.node_pairs == emb.node_pairs == ((0, 1),)
    assert iso.weight == emb.weight == 1.0 + 5.0e-10


@pytest.mark.parametrize("weight", [float("nan"), float("inf"), -float("inf")])
@pytest.mark.parametrize("component", ["node", "edge"])
def test_reference_rejects_nonfinite_scoring_values(weight, component):
    from networkx_algo_common_subtree.common_subtree_reference import (
        score_embedding_witness,
        score_subtree_isomorphism_witness,
    )

    tree = ReferenceLabeledTree([1, 1], [(0, 1, 0)])
    scoring = ExactLabelScoring(
        node_match_weight=weight if component == "node" else 1.0,
        edge_match_weight=weight if component == "edge" else 0.0,
    )
    for solve in [
        maximum_common_subtree_isomorphism_reference,
        largest_weight_common_subtree_embedding_with_distance_penalty_reference,
    ]:
        with pytest.raises(ValueError, match="scores must be finite"):
            solve(tree, tree, scoring)
    for rescore in [score_subtree_isomorphism_witness, score_embedding_witness]:
        with pytest.raises(ValueError, match="scores must be finite"):
            rescore(tree, tree, [(0, 0), (1, 1)], scoring)


def test_reference_rejects_accumulation_overflow():
    from sys import float_info

    tree = ReferenceLabeledTree([1, 1], [(0, 1, 0)])
    scoring = ExactLabelScoring(node_match_weight=float_info.max, edge_match_weight=0.0)
    for solve in [
        maximum_common_subtree_isomorphism_reference,
        largest_weight_common_subtree_embedding_with_distance_penalty_reference,
    ]:
        with pytest.raises(ValueError, match="scores must be finite"):
            solve(tree, tree, scoring)
