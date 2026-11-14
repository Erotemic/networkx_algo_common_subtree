"""Public ordered input/scoring contracts, including compiled backends."""
import math

import networkx as nx
import pytest

from networkx_algo_common_subtree import balanced_embedding, balanced_isomorphism
from networkx_algo_common_subtree import maximum_common_ordered_subtree_embedding, maximum_common_ordered_subtree_isomorphism
from networkx_algo_common_subtree.balanced_sequence import UnbalancedException
from test_backend_differential import _backends, _subset_witnesses


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


def test_rooted_isomorphism_does_not_promote_a_descendant_root():
    solve = balanced_isomorphism.longest_common_balanced_isomorphism
    for impl in _backends("isomorphism", unweighted=False):
        general, score = solve("([])", "[]", {"(": ")", "[": "]"}, impl=impl)
        assert general == ("[]", "[]") and score == 1
        rooted, score = solve("([])", "[]", {"(": ")", "[": "]"}, impl=impl, rooted=True)
        assert rooted == ("", "") and score == 0
        with pytest.raises(TypeError, match="rooted"):
            solve("()", "()", {"(": ")"}, impl=impl, rooted="yes")


def test_rooted_ordered_graph_witnesses_retain_original_roots_and_scores():
    left, right = nx.DiGraph([("a", "b")]), nx.DiGraph([("x", "y")])
    weights = {("a", "x"): 1, ("b", "y"): 2.5, ("b", "x"): 10}
    for impl in _backends("isomorphism", unweighted=False):
        for item_type in ["chr", "number"]:
            options = dict(impl=impl, item_type=item_type, node_affinity=lambda a, b: weights.get((a, b), 0))
            _, _, general_score = maximum_common_ordered_subtree_isomorphism(left, right, **options)
            first, second, score = maximum_common_ordered_subtree_isomorphism(left, right, rooted=True, **options)
            assert score == 3.5 and general_score == 10
            assert list(first.nodes) == ["a", "b"]
            assert list(second.nodes) == ["x", "y"]
            assert set(first.edges) <= set(left.edges)
            assert set(second.edges) <= set(right.edges)
            assert sum(weights[u, v] for u, v in zip(first.nodes, second.nodes)) == score


def test_hashable_tokens_need_no_ordering_for_ties(algorithm):
    kind, solve = algorithm
    a, b, c, d = object(), object(), object(), object()
    left, right, pairs = (a, b, c, d), (c, d, a, b), {a: b, c: d}
    common = ({record[0] for record in _subset_witnesses(left, pairs, kind)}
              & {record[0] for record in _subset_witnesses(right, pairs, kind)})
    optimum = max(len(witness) // 2 for witness in common)
    for impl in _backends(kind, unweighted=False):
        result, score = solve(left, right, pairs, impl=impl)
        assert result[0] in common and result[1] == result[0]
        assert score == optimum == 1
        assert (result, score) == solve(left, right, pairs, impl=impl)


@pytest.mark.parametrize("opening,closing", [("é", "ø"), ("🌳", "🌲"), (chr(0xd800), chr(0xd801))])
def test_full_python_unicode_witness_roundtrip(algorithm, opening, closing):
    kind, solve = algorithm
    word = opening + closing
    for impl in _backends(kind, unweighted=True):
        for rooted in ([False, True] if kind == "isomorphism" else [False]):
            options = {"rooted": rooted} if kind == "isomorphism" else {}
            result, score = solve(word, word, {opening: closing}, node_affinity=None, impl=impl, **options)
            assert result == (word, word)
            assert score == 1
