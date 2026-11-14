"""Public ordered input/scoring contracts, including compiled backends."""
import math

import networkx as nx
import pytest

from networkx_algo_common_subtree import balanced_embedding, balanced_isomorphism
from networkx_algo_common_subtree import maximum_common_ordered_subtree_embedding, maximum_common_ordered_subtree_isomorphism
from networkx_algo_common_subtree.balanced_sequence import UnbalancedException
from test_backend_differential import _backends


@pytest.fixture(params=["embedding", "isomorphism"])
def algorithm(request):
    if request.param == "embedding":
        return request.param, balanced_embedding.longest_common_balanced_embedding
    return request.param, balanced_isomorphism.longest_common_balanced_isomorphism


def test_unhashable_mapped_affinity_values(algorithm):
    kind, solve = algorithm
    for impl in _backends(kind, unweighted=False):
        witness, score = solve((0, 1), (2, 3), {0: 1, 2: 3}, open_to_node={0: ["same"], 2: ["same"]},
                               node_affinity=lambda a, b: 2.5 if a == b else 0, impl=impl)
        assert witness == ((0, 1), (2, 3))
        assert score == 2.5


def test_missing_original_node_mapping_is_not_silently_ignored(algorithm):
    kind, solve = algorithm
    for impl in _backends(kind, unweighted=False):
        with pytest.raises(KeyError):
            solve((0, 1), (2, 3), {0: 1, 2: 3}, open_to_node={0: "left"},
                  node_affinity=lambda a, b: 1, impl=impl)


def test_malformed_sequences_rejected_even_against_empty(algorithm):
    kind, solve = algorithm
    for impl in _backends(kind, unweighted=True):
        for bad in [")", "((", "([)]", "()]"]:
            for left, right in [(bad, "()"), ("", bad), (bad, "")]:
                with pytest.raises(UnbalancedException):
                    solve(left, right, {"(": ")", "[": "]"}, node_affinity=None, impl=impl)


def test_invalid_affinity_values_and_total_overflow(algorithm):
    kind, solve = algorithm
    for impl in _backends(kind, unweighted=False):
        for value in [math.nan, math.inf, -math.inf, -1, None]:
            with pytest.raises(ValueError, match="finite|nonnegative"):
                solve("()", "()", {"(": ")"}, node_affinity=lambda a, b: value, impl=impl)
        with pytest.raises(ValueError, match="overflow|finite"):
            solve("()()", "()()", {"(": ")"}, node_affinity=lambda a, b: 1e308, impl=impl)


@pytest.mark.parametrize("solve", [maximum_common_ordered_subtree_embedding, maximum_common_ordered_subtree_isomorphism])
def test_ordered_graphs_reject_cycles_and_multiple_parents(solve):
    valid = nx.DiGraph([(0, 1)])
    invalid = [nx.DiGraph([(0, 1), (1, 0)]),
               nx.DiGraph([(0, 1), (2, 3), (3, 2)]),
               nx.DiGraph([(0, 2), (1, 2)]),
               nx.MultiDiGraph([(0, 1), (0, 1)])]
    for graph in invalid:
        with pytest.raises(TypeError, match="forest"):
            solve(graph, valid)
