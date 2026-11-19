import json
from pathlib import Path

import pytest

from networkx_algo_common_subtree.common_subtree_reference import (
    ReferenceLabeledTree,
    largest_weight_common_subtree_embedding_with_distance_penalty_reference,
    maximum_common_subtree_isomorphism_reference,
    score_embedding_witness,
    score_subtree_isomorphism_witness,
)

_FIXTURE_FPATH = Path(__file__).parent / "fixtures" / "common_subtree_cases.json"


def _load_cases():
    return json.loads(_FIXTURE_FPATH.read_text())


def _tree(spec):
    return ReferenceLabeledTree(spec["node_labels"], spec["edges"])


@pytest.mark.parametrize("case", _load_cases(), ids=lambda case: case["name"])
def test_mcsi_fixture_scores_and_witnesses(case):
    left = _tree(case["left"])
    right = _tree(case["right"])
    expected = case["mcsi"]

    result = maximum_common_subtree_isomorphism_reference(left, right)

    assert result.weight == pytest.approx(expected["weight"])
    assert result.node_pairs == tuple(map(tuple, expected["node_pairs"]))
    assert score_subtree_isomorphism_witness(left, right, result.node_pairs) == pytest.approx(result.weight)
    assert score_subtree_isomorphism_witness(left, right, expected["node_pairs"]) == pytest.approx(
        expected["weight"]
    )


@pytest.mark.parametrize(
    "case", [case for case in _load_cases() if "embedding" in case], ids=lambda case: case["name"]
)
def test_embedding_fixture_scores_and_witnesses(case):
    left = _tree(case["left"])
    right = _tree(case["right"])
    expected = case["embedding"]
    penalty = expected["skip_vertex_penalty"]

    result = largest_weight_common_subtree_embedding_with_distance_penalty_reference(
        left, right, skip_vertex_penalty=penalty
    )

    assert result.weight == pytest.approx(expected["weight"])
    assert result.node_pairs == tuple(map(tuple, expected["node_pairs"]))
    assert score_embedding_witness(left, right, result.node_pairs, skip_vertex_penalty=penalty) == pytest.approx(
        result.weight
    )
    assert score_embedding_witness(left, right, expected["node_pairs"], skip_vertex_penalty=penalty) == pytest.approx(
        expected["weight"]
    )


def test_witness_validator_rejects_non_bijective_and_incompatible_mappings():
    left = ReferenceLabeledTree([1, 2, 3], [(0, 1, 1), (1, 2, 1)])
    right = ReferenceLabeledTree([1, 2, 3], [(0, 1, 1), (1, 2, 1)])

    with pytest.raises(ValueError, match="duplicate"):
        score_subtree_isomorphism_witness(left, right, [(0, 0), (0, 1)])
    with pytest.raises(ValueError, match="incompatible"):
        score_subtree_isomorphism_witness(left, right, [(0, 2)])
    swapped_right = ReferenceLabeledTree([1, 3, 2], [(0, 1, 1), (1, 2, 1)])
    with pytest.raises(ValueError, match="induced edges"):
        score_subtree_isomorphism_witness(left, swapped_right, [(0, 0), (1, 2), (2, 1)])
