"""Exact public API, original witnesses and an independent subset oracle."""
from fractions import Fraction
import itertools
import os
import random
from concurrent.futures import ThreadPoolExecutor

import networkx as nx
import pytest

from networkx_algo_common_subtree import maximum_common_ordered_subtree_isomorphism
from networkx_algo_common_subtree.balanced_isomorphism import longest_common_balanced_isomorphism as solve
from networkx_algo_common_subtree.balanced_sequence import UnbalancedException
from networkx_algo_common_subtree.balanced_isomorphism_lean import _lean_executable


@pytest.fixture(autouse=True)
def require_lean():
    if _lean_executable() is None:
        if os.environ.get("COMMON_SUBTREE_REQUIRE_LEAN") == "1":
            pytest.fail("required compiled exact Lean backend is unavailable")
        pytest.skip("optional compiled Lean backend is unavailable")


def _typed(word, offset):
    sequence, stack, pairs, ids = [], [], {}, {}
    for token in word:
        if token == "(":
            opening = offset + 2 * len(ids)
            ids[opening] = len(ids)
            pairs[opening] = opening + 1
            sequence.append(opening)
            stack.append(opening)
        else:
            sequence.append(stack.pop() + 1)
    return tuple(sequence), pairs, ids


def _selections(sequence, pairs, rooted):
    """Enumerate original subsets by parent edges, independently of the DP."""
    stack, parents, tokens, opens = [], {}, [], []
    for token in sequence:
        if token in pairs:
            parents[token] = stack[-1] if stack else None
            opens.append(token)
            stack.append(token)
            tokens.append((token, 0))
        else:
            tokens.append((stack.pop(), 1))
    results = []
    for mask in range(1 << len(opens)):
        selected = {v for i, v in enumerate(opens) if mask & (1 << i)}
        outside = {parents[v] for v in selected if parents[v] not in selected}
        if selected and (len(outside) != 1 or (rooted and outside != {None})):
            continue
        shape = tuple(side for v, side in tokens if v in selected)
        results.append((shape, [v for v in opens if v in selected]))
    return results


@pytest.mark.parametrize("rooted", [False, True])
def test_fractional_optimum_against_independent_subsets(rooted):
    rng = random.Random(4701)
    words = ["", "()", "()()", "(())", "(()())", "((()))", "()(())"]
    for first, second in itertools.product(words, repeat=2):
        left, lp, li = _typed(first, 0)
        right, rp, ri = _typed(second, 100)
        mapping = {**lp, **rp}
        weights = [[Fraction(rng.randrange(7), rng.randrange(1, 6)) for _ in ri] for _ in li]
        affinity = lambda a, b: weights[li[a]][ri[b]]
        ls, rs = _selections(left, mapping, rooted), _selections(right, mapping, rooted)
        expected = Fraction()
        for shape1, selection1 in ls:
            for shape2, selection2 in rs:
                if shape1 == shape2:
                    scores = [affinity(a, b) for a, b in zip(selection1, selection2)]
                    if all(score > 0 for score in scores):
                        expected = max(expected, sum(scores, Fraction()))
        (out1, out2), score = solve(left, right, mapping, node_affinity=affinity,
                                    impl="verified-lean", rooted=rooted)
        selected1 = [v for v in out1 if v in li]
        selected2 = [v for v in out2 if v in ri]
        shapes1 = {shape for shape, selection in ls if selection == selected1}
        shapes2 = {shape for shape, selection in rs if selection == selected2}
        assert shapes1 & shapes2
        assert isinstance(score, Fraction) and score == expected
        assert score == sum((affinity(a, b) for a, b in zip(selected1, selected2)), Fraction())


@pytest.mark.parametrize("container", [str, list, tuple])
def test_unicode_mapping_and_root_policy(container):
    pairs = {"(": ")", "\ud800": "\udfff", "[": "]"}
    left, right = container("(\ud800\udfff)"), container("[]")
    affinity = lambda a, b: Fraction(1, 3) if a == ["inner"] else 0
    mapped = {"(": ["outer"], "\ud800": ["inner"], "[": ["right"]}
    (a, b), score = solve(left, right, pairs, open_to_node=mapped,
                          node_affinity=affinity, impl="verified-lean")
    assert (a, b, score) == (container("\ud800\udfff"), container("[]"), Fraction(1, 3))
    assert solve(left, right, pairs, open_to_node=mapped, node_affinity=affinity,
                 rooted=True, impl="verified-lean") == ((container(""), container("")), 0)


def test_large_integers_and_near_ties_are_exact():
    left, lp, li = _typed("()()", 0)
    right, rp, ri = _typed("()", 100)
    big = 2 ** 200
    for delta in [Fraction(1), Fraction(1, 10 ** 60)]:
        affinity = lambda a, b: big + (delta if li[a] else 0)
        (out1, out2), score = solve(left, right, {**lp, **rp}, node_affinity=affinity,
                                    impl="verified-lean", rooted=True)
        assert out1 == left[2:] and out2 == right and score == big + delta


def test_exact_types_errors_and_no_silent_fallback(monkeypatch):
    pairs = {"(": ")", "[": "]"}
    for bad in [")", "((", "([)]", "()x"]:
        for left, right in [(bad, ""), ("", bad)]:
            with pytest.raises(UnbalancedException):
                solve(left, right, pairs, impl="verified-lean")
    for value in [1.0, float("nan"), None, "1/3"]:
        with pytest.raises(TypeError, match="Rational"):
            solve("()", "()", pairs, node_affinity=lambda a,b: value, impl="verified-lean")
    with pytest.raises(ValueError, match="nonnegative"):
        solve("()", "()", pairs, node_affinity=lambda a,b: -1, impl="verified-lean")
    with pytest.raises(TypeError, match="rooted"):
        solve("()", "()", pairs, impl="verified-lean", rooted=1)
    monkeypatch.setenv("COMMON_SUBTREE_VERIFIED_LEAN", "/nonexistent/verified_ordered")
    with pytest.raises(ImportError, match="requires the compiled"):
        solve("()", "()", pairs, impl="verified-lean")


def test_networkx_original_nodes_and_exact_score():
    left = nx.DiGraph([("root", ("inner", 1)), (("inner", 1), -7)])
    right = nx.DiGraph([("x", "y")])
    for rooted in [False, True]:
        first, second, score = maximum_common_ordered_subtree_isomorphism(
            left, right, node_affinity=lambda a,b: Fraction(2, 7),
            impl="verified-lean", rooted=rooted)
        assert score == Fraction(4, 7)
        assert set(first) <= set(left) and set(second) <= set(right)
        assert set(first.edges) <= set(left.edges) and set(second.edges) <= set(right.edges)
        assert len(first) == len(second) == 2
        if rooted:
            assert "root" in first and "x" in second


def _concurrent_solve(weight):
    return solve("()()", "()()", {"(": ")"}, node_affinity=lambda a,b: weight,
                 impl="verified-lean", rooted=True)[1]


def test_worker_threads_restart_and_fork():
    from networkx_algo_common_subtree import balanced_isomorphism_lean as backend
    weights = [Fraction(i, 7) for i in range(1, 9)]
    with ThreadPoolExecutor(4) as executor:
        assert list(executor.map(_concurrent_solve, weights)) == [2*w for w in weights]
    backend._worker.kill()
    backend._worker.wait()
    assert _concurrent_solve(Fraction(1, 3)) == Fraction(2, 3)
    if hasattr(os, "fork"):
        import multiprocessing
        with multiprocessing.get_context("fork").Pool(1) as pool:
            assert pool.apply(_concurrent_solve, (Fraction(2, 5),)) == Fraction(4, 5)
        assert _concurrent_solve(1) == 2


def test_native_hash_collisions_retain_distinct_forest_shapes():
    from networkx_algo_common_subtree import balanced_isomorphism_lean as backend
    # This native model supports repeated labels (uniqueness is a separate
    # theorem premise). Different forests deliberately share first-label hashes.
    leaf = [0, [], []]
    left = [0, leaf, leaf]
    right = [0, [0, leaf, []], []]
    request = dict(protocol=1, left=left, right=right, rooted=True,
                   weights=[[["1", "1"] for _ in range(3)] for _ in range(3)])
    result = backend._request(backend._lean_executable(), request)
    assert Fraction(int(result["numerator"]), int(result["denominator"])) == 2
    assert len(result["pairs"]) == 2
