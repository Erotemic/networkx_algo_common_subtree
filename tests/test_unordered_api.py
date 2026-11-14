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
    if value != math.inf:
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
    for name in ["maximum_common_subtree_isomorphism", "largest_weight_common_subtree_embedding_with_distance_penalty"]:
        native = getattr(_rust, name)
        with pytest.raises(ValueError, match="roots"):
            native([0], [], [0], [], roots=(1, 0))
        with pytest.raises(ValueError, match="roots"):
            native([0], [], [0], [], root_to_root=True)
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
@pytest.mark.parametrize("root_mode", ["unrooted", "rooted", "root-to-root"])
def test_high_degree_parent_deletion_preserves_original_matching_indices(leaves, kind, root_mode):
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
    if root_mode != "unrooted":
        kwargs.update(roots=(1, 1), root_to_root=root_mode == "root-to-root")
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


@pytest.mark.parametrize("kind", ["iso", "embedding"])
def test_rooted_modes_distinguish_three_optima_and_original_roots(impl, kind):
    left = _graph([0, 1, 2], [(0, 1, 0), (1, 2, 0)], ("left", ("mid", 1), 8))
    right = _graph([0, 1, 2], [(0, 1, 0), (1, 2, 0)], ("x", "y", "z"))
    if kind == "iso":
        solver, scorer = common.maximum_common_subtree_isomorphism, common.score_common_subtree_isomorphism
    else:
        solver, scorer = (common.largest_weight_common_subtree_embedding_with_distance_penalty,
                          common.score_common_subtree_embedding)
    kwargs = dict(node_label="label")
    unrestricted = solver(left, right, impl=impl, **kwargs)
    assert unrestricted.weight == 5
    roots = ("left", "z")
    rooted = solver(left, right, impl=impl, roots=roots, **kwargs)
    assert rooted.weight == 1
    assert scorer(left, right, rooted, roots=roots, **kwargs) == 1
    with pytest.raises(ValueError, match="highest"):
        scorer(left, right, unrestricted, roots=roots, **kwargs)
    assert solver(left, right, impl=impl, roots=roots, root_to_root=True, allow_empty=False, **kwargs) is None
    assert solver(left, right, impl=impl, roots=roots, root_to_root=True, **kwargs).node_pairs == ()
    below = solver(left, right, impl=impl, roots=(("mid", 1), "x"), **kwargs)
    assert below.weight == 3 and below.mapping == {("mid", 1): "y", 8: "z"}
    fixed = solver(left, right, impl=impl, roots=(("mid", 1), "y"), root_to_root=True, **kwargs)
    assert fixed.weight == 5 and fixed.mapping[("mid", 1)] == "y"
    assert scorer(left, right, fixed, roots=(("mid", 1), "y"), root_to_root=True, **kwargs) == 5


def test_rooted_embedding_excludes_only_the_skipped_highest_case(impl):
    left, right = nx.star_graph(4), nx.path_graph(2)
    kwargs = dict(node_weight=lambda u, v: 1 if u else None, edge_weight=100,
                  skip_vertex_penalty=.25, impl=impl)
    solver = common.largest_weight_common_subtree_embedding_with_distance_penalty
    assert solver(left, right, **kwargs).weight == 1.75
    assert solver(left, right, roots=(0, 0), **kwargs).weight == 1
    assert solver(left, right, roots=(0, 0), root_to_root=True, allow_empty=False, **kwargs) is None
    result = solver(left, right, roots=(1, 0), root_to_root=True, **kwargs)
    assert result.weight == 1.75 and result.mapping[1] == 0
    scoring = {k: v for k, v in kwargs.items() if k != "impl"}
    assert common.score_common_subtree_embedding(left, right, result, roots=(1, 0), root_to_root=True, **scoring) == 1.75


def test_signed_rooted_contracts_against_exhaustive_oracles():
    if "rust" not in common.available_unordered_backends():
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required weighted graph Rust bindings are missing")
        pytest.skip("optional weighted graph Rust bindings are missing")
    rng = random.Random(201618)
    for case in range(32):
        trees = []
        for side in range(2):
            n = rng.randrange(1, 5)
            graph = nx.Graph()
            graph.add_nodes_from(((side, i), {"label": rng.randrange(2)}) for i in range(n))
            graph.add_edges_from(((side, i), (side, rng.randrange(i)), {"label": rng.randrange(2)}) for i in range(1, n))
            trees.append(graph)
        left, right = trees
        nodes = {(u, v): rng.choice([None, -.5, 0, .125, 1.5]) for u in left for v in right}
        edges = {(frozenset(a), frozenset(b)): rng.choice([None, -1, .25, 2.5]) for a in left.edges for b in right.edges}
        kwargs = dict(node_label="label", edge_label="label", node_weight=lambda u, v: nodes[u, v],
                      edge_weight=lambda a, b: edges[frozenset(a), frozenset(b)],
                      roots=(rng.choice(list(left)), rng.choice(list(right))), allow_empty=bool(case % 2))
        for root_to_root in [False, True]:
            for solver, scorer, extra in [
                (common.maximum_common_subtree_isomorphism, common.score_common_subtree_isomorphism, {}),
                (common.largest_weight_common_subtree_embedding_with_distance_penalty, common.score_common_subtree_embedding,
                 {"skip_vertex_penalty": rng.choice([0, .125, 2.0])}),
            ]:
                result = solver(left, right, impl="rust", root_to_root=root_to_root, **kwargs, **extra)
                oracle = solver(left, right, impl="python", root_to_root=root_to_root, **kwargs, **extra)
                if oracle is None:
                    assert result is None
                else:
                    assert result.weight == oracle.weight
                    if result.node_pairs:
                        # Check the root contract directly through NetworkX
                        # paths, separately from the interval-based rescorer.
                        a, b = kwargs["roots"]
                        assert any(all(u in nx.shortest_path(left, a, x) and v in nx.shortest_path(right, b, y)
                                       for x, y in result.node_pairs) for u, v in result.node_pairs)
                        if root_to_root:
                            assert (a, b) in result.node_pairs
                    scoring = {k: v for k, v in kwargs.items() if k != "allow_empty"}
                    assert scorer(left, right, result, root_to_root=root_to_root, **scoring, **extra) == result.weight
                    assert scorer(left, right, result.node_pairs, root_to_root=root_to_root, **scoring, **extra) == result.weight


@pytest.mark.parametrize("kind", ["iso", "embedding"])
def test_invalid_root_modes(impl, kind):
    tree = nx.path_graph(2)
    solver = (common.maximum_common_subtree_isomorphism if kind == "iso" else
              common.largest_weight_common_subtree_embedding_with_distance_penalty)
    for kwargs in [dict(root_to_root=True), dict(roots=()), dict(roots=(0,)), dict(roots=(0, 1, 0)),
                   dict(roots=(0, "unknown")), dict(roots=("unknown", 0))]:
        with pytest.raises(ValueError, match="roots"):
            solver(tree, tree, impl=impl, **kwargs)
    with pytest.raises(TypeError, match="bool"):
        solver(tree, tree, impl=impl, roots=(0, 0), root_to_root=1)
    with pytest.raises(ValueError, match="roots"):
        solver(nx.Graph(), tree, impl=impl, roots=(0, 0))


@pytest.mark.parametrize("kind", ["iso", "embedding"])
def test_forced_roots_retain_negative_parents(impl, kind):
    tree = nx.path_graph(2)
    if kind == "iso":
        solver, scorer = common.maximum_common_subtree_isomorphism, common.score_common_subtree_isomorphism
    else:
        solver, scorer = (common.largest_weight_common_subtree_embedding_with_distance_penalty,
                          common.score_common_subtree_embedding)
    kwargs = dict(roots=(0, 0), root_to_root=True,
                  node_weight=lambda u, v: (-5 if u == 0 else 1) if u == v else None)
    result = solver(tree, tree, impl=impl, allow_empty=False, edge_weight=0, **kwargs)
    assert result.weight == -4 and result.mapping == {0: 0, 1: 1}
    assert scorer(tree, tree, result, edge_weight=0, **kwargs) == -4
    assert solver(tree, tree, impl=impl, edge_weight=0, **kwargs).node_pairs == ()
    assert solver(tree, tree, impl=impl, allow_empty=False, edge_weight=6, **kwargs).weight == 2


@pytest.mark.parametrize("root_mode", ["unrooted", "rooted", "root-to-root"])
def test_infinite_penalty_matches_independent_isomorphism_optimum(impl, root_mode):
    rng = random.Random(2018)
    for case in range(24):
        trees = []
        for side in range(2):
            n = rng.randrange(1, 5)
            graph = _graph([rng.randrange(2) for _ in range(n)],
                           [(u, rng.randrange(u), rng.randrange(2)) for u in range(1, n)],
                           tuple((side, u) for u in range(n)))
            trees.append(graph)
        left, right = trees
        nodes = {(u, v): rng.choice([None, -.5, 0, .125, 1.5]) for u in left for v in right}
        edges = {(frozenset(a), frozenset(b)): rng.choice([None, -1, .25, 2.5])
                 for a in left.edges for b in right.edges}
        scoring = dict(node_label="label", edge_label="label", node_weight=lambda u, v: nodes[u, v],
                       edge_weight=lambda a, b: edges[frozenset(a), frozenset(b)])
        if root_mode != "unrooted":
            scoring.update(roots=(rng.choice(list(left)), rng.choice(list(right))),
                           root_to_root=root_mode == "root-to-root")
        extra = dict(allow_empty=bool(case % 2))
        expected = common.maximum_common_subtree_isomorphism(left, right, impl="python", **scoring, **extra)
        actual = common.largest_weight_common_subtree_embedding_with_distance_penalty(
            left, right, skip_vertex_penalty=math.inf, impl=impl, **scoring, **extra)
        if expected is None:
            assert actual is None
            continue
        assert actual.weight == expected.weight
        assert all(len(lp) == len(rp) == 2 for lp, rp in actual.edge_paths)
        for witness in [actual, actual.node_pairs]:
            assert common.score_common_subtree_embedding(
                left, right, witness, skip_vertex_penalty=math.inf, **scoring) == actual.weight
            assert common.score_common_subtree_isomorphism(left, right, witness, **scoring) == actual.weight


def test_infinite_penalty_forbids_long_paths_without_overflow(impl):
    left = _graph([1, 2], [(0, 1, 5)], ("a", "b"))
    right = _graph([1, 99, 2], [(0, 1, 6), (1, 2, 7)], ("x", "skip", "y"))
    kwargs = dict(node_label="label", edge_label="label", edge_weight=lambda a, b: None)
    finite = common.largest_weight_common_subtree_embedding_with_distance_penalty(
        left, right, skip_vertex_penalty=.25, impl=impl, **kwargs)
    assert finite.weight == 1.75
    for node_weight in [1, 1e308]:
        actual = common.largest_weight_common_subtree_embedding_with_distance_penalty(
            left, right, skip_vertex_penalty=math.inf, node_weight=node_weight, impl=impl, **kwargs)
        assert actual.weight == node_weight
        assert len(actual.node_pairs) == 1
        for witness in [finite, finite.node_pairs]:
            with pytest.raises(ValueError, match="infinite distance penalty forbids"):
                common.score_common_subtree_embedding(
                    left, right, witness, skip_vertex_penalty=math.inf, node_weight=node_weight, **kwargs)
    empty = nx.Graph()
    for allow_empty in [False, True]:
        result = common.largest_weight_common_subtree_embedding_with_distance_penalty(
            empty, right, skip_vertex_penalty=math.inf, impl=impl, allow_empty=allow_empty)
        assert result == (common.CommonSubtreeResult(0, (), ()) if allow_empty else None)


def test_raw_infinite_penalty_and_invalid_penalties(impl):
    for invalid in ["invalid", None, object(), -math.inf, math.nan]:
        with pytest.raises(ValueError, match="nonnegative"):
            common.largest_weight_common_subtree_embedding_with_distance_penalty(
                nx.empty_graph(1), nx.empty_graph(1), skip_vertex_penalty=invalid, impl=impl)
    if impl != "rust":
        return
    from networkx_algo_common_subtree import _rust
    solve = _rust.largest_weight_common_subtree_embedding_with_distance_penalty
    assert solve([1, 2], [(0, 1, 0)], [1, 99, 2], [(0, 1, 0), (1, 2, 0)], math.inf)[0] == 1
    for invalid in [math.nan, -math.inf, -1]:
        with pytest.raises(ValueError, match="nonnegative"):
            solve([1], [], [1], [], invalid)


@pytest.mark.parametrize("kind", ["isomorphism", "embedding", "embedding-infinite"])
@pytest.mark.parametrize("root_mode", ["unrooted", "rooted", "root-to-root"])
def test_uniform_native_stars_attain_independent_vertex_edge_upper_bound(kind, root_mode):
    if "rust" not in common.available_unordered_backends():
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required Rust graph bindings are missing")
        pytest.skip("optional Rust graph bindings are missing")
    solver, scorer = common.maximum_common_subtree_isomorphism, common.score_common_subtree_isomorphism
    kwargs = dict(node_weight=1.25, edge_weight=.375)
    if root_mode != "unrooted":
        kwargs.update(roots=(0, 0), root_to_root=root_mode == "root-to-root")
    if kind != "isomorphism":
        solver, scorer = (common.largest_weight_common_subtree_embedding_with_distance_penalty,
                          common.score_common_subtree_embedding)
        kwargs["skip_vertex_penalty"] = math.inf if kind == "embedding-infinite" else .25
    for n, m in [(3, 5), (5, 3), (9, 9)]:
        left, right = nx.star_graph(n - 1), nx.star_graph(m - 1)
        result = solver(left, right, impl="rust", **kwargs)
        # At most k mapped vertices and k-1 common edges. The entire smaller
        # star attains both bounds; skipping cannot increase either reward.
        k = min(n, m)
        assert result.weight == 1.25 * k + .375 * (k - 1)
        assert len(result.node_pairs) == k and len(result.edge_paths) == k - 1
        assert scorer(left, right, result, **kwargs) == result.weight
        assert scorer(left, right, result.node_pairs, **kwargs) == result.weight
