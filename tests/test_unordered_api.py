"""Public graph APIs versus independent subset/bijection/path enumeration."""
from dataclasses import replace
import math
import os
import random

import networkx as nx
import pytest

import networkx_algo_common_subtree as common


@pytest.fixture(params=["python", "rust"])
def impl(request):
    if request.param not in common.available_unordered_backends():
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required weighted graph Rust bindings are missing")
        pytest.skip("optional weighted graph Rust bindings are missing")
    return request.param


def _graph(labels, edges, names=None):
    names = tuple(range(len(labels))) if names is None else names
    result = nx.Graph()
    result.add_nodes_from((u, {"label": label}) for u, label in zip(names, labels))
    result.add_edges_from((names[u], names[v], {"label": label}) for u, v, label in edges)
    return result


def test_original_nodes_and_independent_path_rescoring(impl):
    left = _graph([1, 2, 3], [(0, 1, 5), (1, 2, 5)], ("a", ("b", 2), -7))
    right = _graph([0, 1, 2, 3], [(0, 1, 9), (1, 2, 5), (2, 3, 5)], ("unused", "x", "y", "z"))
    for solver, scorer in [
        (common.maximum_common_subtree_isomorphism, common.score_common_subtree_isomorphism),
        (common.largest_weight_common_subtree_embedding_with_distance_penalty, common.score_common_subtree_embedding),
    ]:
        result = solver(left, right, node_label="label", edge_label="label", impl=impl)
        assert result.weight == 5
        assert result.mapping == {"a": "x", ("b", 2): "y", -7: "z"}
        assert len(result.edge_paths) == 2
        assert scorer(left, right, result, node_label="label", edge_label="label") == result.weight


def test_long_paths_ignore_edge_reward_and_compatibility(impl):
    left = _graph([1, 2], [(0, 1, 5)], ("a", "b"))
    right = _graph([1, 99, 2], [(0, 1, 6), (1, 2, 7)], ("x", "skip", "y"))
    kwargs = dict(node_label="label", edge_label="label", edge_weight=lambda e1, e2: None)
    result = common.largest_weight_common_subtree_embedding_with_distance_penalty(
        left, right, skip_vertex_penalty=.25, impl=impl, **kwargs)
    assert result.weight == 1.75
    assert result.mapping == {"a": "x", "b": "y"}
    assert result.edge_paths == ((("a", "b"), ("x", "skip", "y")),)
    assert common.score_common_subtree_embedding(left, right, result, skip_vertex_penalty=.25, **kwargs) == 1.75
    assert common.maximum_common_subtree_isomorphism(left, right, impl=impl, **kwargs).weight == 1


@pytest.mark.parametrize("kind", ["iso", "embedding"])
def test_empty_incompatible_and_signed_nonempty_objectives(impl, kind):
    solver = (common.maximum_common_subtree_isomorphism if kind == "iso" else
              common.largest_weight_common_subtree_embedding_with_distance_penalty)
    empty, one = nx.Graph(), nx.empty_graph(1)
    assert solver(empty, one, impl=impl).node_pairs == ()
    assert solver(empty, one, impl=impl, allow_empty=False) is None
    assert solver(one, one, node_weight=-2.5, impl=impl).weight == 0
    negative = solver(one, one, node_weight=-2.5, impl=impl, allow_empty=False)
    assert negative.weight == -2.5
    assert negative.node_pairs == ((0, 0),)
    assert solver(one, one, node_weight=lambda u, v: None, impl=impl, allow_empty=False) is None
    assert solver(one, one, node_weight=0, impl=impl, allow_empty=False).weight == 0


def test_callbacks_are_precomputed_once_and_have_original_endpoints(impl):
    left = nx.path_graph(["a", "b", "c"])
    right = nx.path_graph([("x", 0), ("x", 1)])
    nodes, edges = [], []
    def node_weight(u, v):
        nodes.append((u, v))
        return 1.25 if u != "b" else -0.25
    def edge_weight(left_edge, right_edge):
        edges.append((left_edge, right_edge))
        return .125
    result = common.maximum_common_subtree_isomorphism(left, right, node_weight=node_weight, edge_weight=edge_weight, impl=impl)
    assert len(nodes) == 6 and len(set(nodes)) == 6
    assert len(edges) == 2 and len(set(edges)) == 2
    assert all(u in left and v in right for u, v in nodes)
    assert math.isfinite(result.weight)
    assert common.score_common_subtree_isomorphism(left, right, result, node_weight=node_weight, edge_weight=edge_weight) == result.weight


@pytest.mark.parametrize("bad", [nx.DiGraph([(0, 1)]), nx.MultiGraph([(0, 1)]), nx.cycle_graph(3), nx.empty_graph(2)])
def test_invalid_graphs(bad, impl):
    with pytest.raises(ValueError, match="tree"):
        common.maximum_common_subtree_isomorphism(bad, nx.empty_graph(1), impl=impl)


@pytest.mark.parametrize("value", [float("nan"), float("inf"), -float("inf")])
def test_invalid_weights_and_penalties(value, impl):
    tree = nx.path_graph(2)
    with pytest.raises(ValueError, match="finite"):
        common.maximum_common_subtree_isomorphism(tree, tree, node_weight=value, impl=impl)
    with pytest.raises(ValueError, match="finite"):
        common.maximum_common_subtree_isomorphism(tree, tree, edge_weight=lambda a, b: value, impl=impl)
    with pytest.raises(ValueError):
        common.largest_weight_common_subtree_embedding_with_distance_penalty(tree, tree, skip_vertex_penalty=value, impl=impl)
    with pytest.raises(ValueError, match="nonnegative"):
        common.largest_weight_common_subtree_embedding_with_distance_penalty(tree, tree, skip_vertex_penalty=-1, impl=impl)


def test_overflow_is_a_python_error_instead_of_aborting(impl):
    tree = nx.path_graph(2)
    with pytest.raises(ValueError, match="finite|overflow"):
        common.maximum_common_subtree_isomorphism(tree, tree, node_weight=1e308, edge_weight=1e308, impl=impl)


def test_tampered_witness_paths_and_unknown_backend(impl):
    tree = nx.path_graph(3)
    result = common.maximum_common_subtree_isomorphism(tree, tree, impl=impl)
    with pytest.raises(ValueError, match="paths"):
        common.score_common_subtree_isomorphism(tree, tree, replace(result, edge_paths=()))
    with pytest.raises(ValueError, match="unknown unordered"):
        common.maximum_common_subtree_isomorphism(tree, tree, impl="unavailable")


def test_rust_matches_independent_exhaustive_oracles_on_signed_labeled_trees():
    if "rust" not in common.available_unordered_backends():
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required weighted graph Rust bindings are missing")
        pytest.skip("optional weighted graph Rust bindings are missing")
    rng = random.Random(20261114)
    for case in range(36):
        trees = []
        for side in range(2):
            n = rng.randrange(5)
            tree = nx.Graph()
            tree.add_nodes_from((f"{side}:{i}", {"label": rng.randrange(2)}) for i in range(n))
            for i in range(1, n):
                tree.add_edge(f"{side}:{i}", f"{side}:{rng.randrange(i)}", label=rng.randrange(2))
            trees.append(tree)
        left, right = trees
        kwargs = dict(node_label="label", edge_label="label", node_weight=rng.choice([-1.25, 0, .125, 1.5]),
                      edge_weight=rng.choice([-2.0, 0, .25, 2.0]), allow_empty=bool(case % 2))
        for solver, scorer, extra in [
            (common.maximum_common_subtree_isomorphism, common.score_common_subtree_isomorphism, {}),
            (common.largest_weight_common_subtree_embedding_with_distance_penalty, common.score_common_subtree_embedding,
             {"skip_vertex_penalty": rng.choice([0, .25, 2.0])}),
        ]:
            native = solver(left, right, impl="rust", **kwargs, **extra)
            oracle = solver(left, right, impl="python", **kwargs, **extra)
            if oracle is None:
                assert native is None
            else:
                assert native.weight == pytest.approx(oracle.weight)
                score_kwargs = {k: v for k, v in kwargs.items() if k != "allow_empty"}
                assert scorer(left, right, native, **score_kwargs, **extra) == pytest.approx(native.weight)
                assert native == solver(left, right, impl="rust", **kwargs, **extra)


def test_native_low_level_validation_and_exact_matching():
    if "rust" not in common.available_unordered_backends():
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required weighted graph Rust bindings are missing")
        pytest.skip("optional weighted graph Rust bindings are missing")
    from networkx_algo_common_subtree import _rust
    with pytest.raises(ValueError, match="shape"):
        _rust.maximum_common_subtree_isomorphism([0], [], [0], [], node_weights=[])
    with pytest.raises(ValueError, match="finite"):
        _rust.maximum_common_subtree_isomorphism([0], [], [0], [], node_weights=[[float("nan")]])
    with pytest.raises(ValueError):
        _rust.maximum_common_subtree_isomorphism([0, 0], [], [0], [])
    assignment, cost, u, v = _rust.min_cost_assignment([[3, -2], [0, 4]])
    assert assignment == [1, 0] and cost == -2
    assert cost == sum(u) + sum(v)
    assert all(u[i] + v[j] <= [[3, -2], [0, 4]][i][j] for i in range(2) for j in range(2))
    pairs, weight = _rust.max_weight_partial_matching([[None, 5], [-2, 3]])
    assert pairs == [(0, 1)] and weight == 5


def test_signed_optional_callback_tables_against_exhaustive_objectives():
    if "rust" not in common.available_unordered_backends():
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required weighted graph Rust bindings are missing")
        pytest.skip("optional weighted graph Rust bindings are missing")
    rng = random.Random(180500821)
    for case in range(32):
        left, right = nx.Graph(), nx.Graph()
        for tree, side in [(left, "left"), (right, "right")]:
            n = rng.randrange(1, 5)
            tree.add_nodes_from((side, i) for i in range(n))
            tree.add_edges_from(((side, i), (side, rng.randrange(i))) for i in range(1, n))
        nodes = {(u, v): rng.choice([None, -.5, 0, .125, 1.25]) for u in left for v in right}
        edges = {(u, v): rng.choice([None, -1, 0, .25, 2.5]) for u in left.edges for v in right.edges}
        kwargs = dict(node_weight=lambda u, v: nodes[u, v], edge_weight=lambda u, v: edges[u, v],
                      allow_empty=bool(case % 2))
        for solver, scorer, extra in [
            (common.maximum_common_subtree_isomorphism, common.score_common_subtree_isomorphism, {}),
            (common.largest_weight_common_subtree_embedding_with_distance_penalty, common.score_common_subtree_embedding,
             {"skip_vertex_penalty": rng.choice([0, .125, 1.0])}),
        ]:
            result = solver(left, right, impl="rust", **kwargs, **extra)
            oracle = solver(left, right, impl="python", **kwargs, **extra)
            if oracle is None:
                assert result is None
            else:
                # Dyadic weights and these sizes make equality exact in f64.
                assert result.weight == oracle.weight
                scoring = {k: v for k, v in kwargs.items() if k != "allow_empty"}
                assert scorer(left, right, result, **scoring, **extra) == result.weight
                # Bare pairs take the separate exhaustive path/skeleton
                # validator, independent of the supplied-path fast path.
                assert scorer(left, right, result.node_pairs, **scoring, **extra) == result.weight


@pytest.mark.parametrize("leaves", [2, 5])
@pytest.mark.parametrize("kind", ["iso", "embedding"])
def test_high_degree_parent_deletion_preserves_original_matching_indices(leaves, kind):
    if "rust" not in common.available_unordered_backends():
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required weighted graph Rust bindings are missing")
        pytest.skip("optional weighted graph Rust bindings are missing")
    left = nx.Graph()
    left.add_nodes_from(range(2 + 2 * leaves))
    left.add_edge(0, 1)
    left.add_edges_from((0, 2 + i) for i in range(leaves))
    left.add_edges_from((1, 2 + leaves + i) for i in range(leaves))
    right = nx.star_graph(4)
    def weight(u, v):
        if (u, v) == (1, 1):
            return 10
        if (u, v) == (0, 0) or (2 <= u < 2 + leaves and v > 0):
            return 1
        return None
    if kind == "iso":
        solver, scorer = common.maximum_common_subtree_isomorphism, common.score_common_subtree_isomorphism
        kwargs = {}
    else:
        solver, scorer = (common.largest_weight_common_subtree_embedding_with_distance_penalty,
                          common.score_common_subtree_embedding)
        kwargs = {"skip_vertex_penalty": 100}
    result = solver(left, right, node_weight=weight, impl="rust", **kwargs)
    # At most one vertex pair weighs 10; every other vertex/edge weighs at
    # most one. Injectivity bounds the retained count, giving this independent
    # upper bound, attained by the returned connected witness.
    retained = min(leaves + 2, len(right))
    optimum = 10 + 2 * (retained - 1)
    assert result.weight == optimum
    assert len(result.node_pairs) == retained
    assert result.mapping[1] == 1
    assert scorer(left, right, result, node_weight=weight, **kwargs) == optimum
    if leaves == 2:
        exhaustive = solver(left, right, node_weight=weight, impl="python", **kwargs)
        assert exhaustive.weight == optimum


@pytest.mark.parametrize("active_leaves", [1, 3])
def test_embedding_crosses_skipped_highest_vertex_in_distinct_branches(impl, active_leaves):
    left, right = nx.star_graph(4), nx.path_graph(2)
    kwargs = dict(node_weight=lambda u, v: 1 if 1 <= u <= active_leaves else None,
                  edge_weight=100, skip_vertex_penalty=.25)
    result = common.largest_weight_common_subtree_embedding_with_distance_penalty(
        left, right, impl=impl, **kwargs)
    # The fixed highest left vertex is forbidden. Two distinct leaf branches
    # can cross it, paying one skip and earning no direct-edge reward.
    count = min(active_leaves, 2)
    assert result.weight == (1 if count == 1 else 1.75)
    assert len(result.node_pairs) == count
    assert len(set(result.mapping)) == count
    assert common.score_common_subtree_embedding(left, right, result, **kwargs) == result.weight


def test_embedding_matching_families_against_signed_high_degree_oracle():
    if "rust" not in common.available_unordered_backends():
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required weighted graph Rust bindings are missing")
        pytest.skip("optional weighted graph Rust bindings are missing")
    rng = random.Random(180500821)
    left, right = nx.star_graph(5), nx.star_graph(4)
    for case in range(12):
        nodes = {(u, v): rng.choice([None, -.5, 0, .125, 1.5]) for u in left for v in right}
        edges = {(frozenset(a), frozenset(b)): rng.choice([None, -1, 0, .25, 2.5])
                 for a in left.edges for b in right.edges}
        kwargs = dict(node_weight=lambda u, v: nodes[u, v],
                      edge_weight=lambda a, b: edges[frozenset(a), frozenset(b)],
                      skip_vertex_penalty=rng.choice([0, .125, 2.0]))
        native = common.largest_weight_common_subtree_embedding_with_distance_penalty(
            left, right, impl="rust", allow_empty=bool(case % 2), **kwargs)
        oracle = common.largest_weight_common_subtree_embedding_with_distance_penalty(
            left, right, impl="python", allow_empty=bool(case % 2), **kwargs)
        if oracle is None:
            assert native is None
        else:
            assert native.weight == oracle.weight
            assert common.score_common_subtree_embedding(left, right, native, **kwargs) == native.weight


@pytest.mark.parametrize("kind", ["iso", "embedding"])
def test_reordered_edges_keep_callback_indices_and_optima(kind):
    if "rust" not in common.available_unordered_backends():
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required weighted graph Rust bindings are missing")
        pytest.skip("optional weighted graph Rust bindings are missing")
    left_edges = [(3, 4), (0, 3), (1, 3), (1, 2)]
    right_edges = [(0, 4), (2, 4), (1, 2), (2, 3)]
    rng = random.Random(20162018)
    nodes = {(u, v): rng.choice([None, -.5, .125, 1.25]) for u in range(5) for v in range(5)}
    edges = {(frozenset(a), frozenset(b)): rng.choice([None, -1, .25, 2.5])
             for a in left_edges for b in right_edges}
    kwargs = dict(node_weight=lambda u, v: nodes[u, v],
                  edge_weight=lambda a, b: edges[frozenset(a), frozenset(b)])
    if kind == "iso":
        solver, scorer = common.maximum_common_subtree_isomorphism, common.score_common_subtree_isomorphism
    else:
        solver, scorer = (common.largest_weight_common_subtree_embedding_with_distance_penalty,
                          common.score_common_subtree_embedding)
        kwargs["skip_vertex_penalty"] = .125
    optima = []
    for reverse in [False, True]:
        left, right = nx.Graph(), nx.Graph()
        left.add_nodes_from(range(5))
        right.add_nodes_from(range(5))
        left.add_edges_from(left_edges[::-1] if reverse else left_edges)
        right.add_edges_from(right_edges[::-1] if reverse else right_edges)
        result = solver(left, right, impl="rust", **kwargs)
        oracle = solver(left, right, impl="python", **kwargs)
        assert result.weight == oracle.weight
        assert scorer(left, right, result, **kwargs) == result.weight
        optima.append(result.weight)
    assert optima[0] == optima[1]


@pytest.mark.parametrize("kind", ["iso", "embedding"])
def test_path_witness_validation_and_reordering(kind):
    tree = nx.path_graph(3)
    scorer = (common.score_common_subtree_isomorphism if kind == "iso" else
              common.score_common_subtree_embedding)
    result = common.CommonSubtreeResult(999, ((0, 0), (1, 1), (2, 2)),
                                       (((0, 1), (0, 1)), ((1, 2), (1, 2))))
    assert scorer(tree, tree, result) == 5  # Rescore independently of claimed weight.
    reversed_paths = tuple((a[::-1], b[::-1]) for a, b in reversed(result.edge_paths))
    assert scorer(tree, tree, replace(result, edge_paths=reversed_paths)) == 5
    bad = [
        replace(result, node_pairs=((0, 0), (0, 1), (2, 2))),
        replace(result, node_pairs=((0, 0), (1, 0), (2, 2))),
        replace(result, node_pairs=((0, 0), (1, 1), (99, 2))),
        replace(result, edge_paths=()),
        replace(result, edge_paths=(((0, 99, 1), (0, 1)), ((1, 2), (1, 2)))),
        replace(result, edge_paths=(((0, 1, 0, 1), (0, 1)), ((1, 2), (1, 2)))),
        replace(result, edge_paths=(((0, 2), (0, 2)), ((1, 2), (1, 2)))),
        replace(result, edge_paths=(((0, 1, 2), (0, 1, 2)), ((1, 2), (1, 2)))),
        replace(result, edge_paths=(((0, 1), (0, 1)), ((0, 1), (0, 1)))),
        replace(result, edge_paths=(((0, 1), (1, 0)), ((1, 2), (1, 2)))),
    ]
    for witness in bad:
        with pytest.raises(ValueError):
            scorer(tree, tree, witness)
    for kwargs in [dict(node_weight=lambda u, v: None), dict(edge_weight=lambda a, b: None),
                   dict(node_weight=1e308)]:
        with pytest.raises(ValueError):
            scorer(tree, tree, result, **kwargs)


@pytest.mark.parametrize("overlap_side", ["left", "right"])
def test_path_witness_rejects_unselected_branch_overlap(overlap_side):
    star, path = nx.star_graph(3), nx.path_graph(3)
    pairs = ((1, 0), (2, 1), (3, 2))
    paths = (((1, 0, 2), (0, 1)), ((2, 0, 3), (1, 2)))
    left, right = star, path
    if overlap_side == "right":
        left, right = path, star
        pairs = tuple((v, u) for u, v in pairs)
        paths = tuple((b, a) for a, b in paths)
    witness = common.CommonSubtreeResult(0, pairs, paths)
    with pytest.raises(ValueError, match="overlap"):
        common.score_common_subtree_embedding(left, right, witness)
    with pytest.raises(ValueError):
        common.score_common_subtree_embedding(left, right, pairs)
