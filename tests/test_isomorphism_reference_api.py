"""Expose the source-proved structural reference without overstating readback proofs."""
import os

import networkx as nx
import pytest

from networkx_algo_common_subtree import balanced_isomorphism as iso
from networkx_algo_common_subtree import maximum_common_ordered_subtree_isomorphism
from networkx_algo_common_subtree.balanced_sequence import UnbalancedException


@pytest.fixture
def backend():
    try:
        from networkx_algo_common_subtree import _rust
        assert hasattr(_rust, "maximum_common_token_isomorphism")
    except (ImportError, AssertionError):
        if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
            pytest.fail("required structural reference Rust entry point is missing")
        pytest.skip("optional structural reference Rust binding is missing")
    return _rust


@pytest.mark.parametrize("container", [str, tuple, list])
def test_reference_typed_tokens_and_root_restrictions(backend, container):
    solve = iso.longest_common_balanced_isomorphism
    pairs = {"(": ")", "[": "]", "\ud800": "\udfff"}
    for rooted, expected in [(False, 1), (True, 1)]:
        (left, right), score = solve(container("(\ud800\udfff)"), container("[]"), pairs,
                                    node_affinity=None, impl="reference-rust", rooted=rooted)
        assert type(left) is type(right) is container
        assert score == expected
        if rooted:
            assert left == container("()")
        else:
            assert left in [container("()"), container("\ud800\udfff")]
        assert right == container("[]")
    # Equality would reject both roots: this mode explicitly ignores labels.
    assert solve(container("()"), container("[]"), pairs, node_affinity=None,
                 impl="reference-rust", rooted=True)[1] == 1
    assert solve(container(""), container("[]"), pairs, node_affinity=None,
                 impl="reference-rust") == ((container(""), container("")), 0)
    for bad in [")", "(", "([)]", "()x", "(()"]:
        for left, right in [(container(bad), container("")), (container(""), container(bad))]:
            with pytest.raises(UnbalancedException):
                solve(left, right, pairs, node_affinity=None, impl="reference-rust")


def test_reference_original_graph_vertices_and_discovery(backend, monkeypatch):
    left = nx.DiGraph([("root", ("child", 1)), (("child", 1), -7)])
    right = nx.DiGraph([("x", "y")])
    for rooted in [False, True]:
        first, second, score = maximum_common_ordered_subtree_isomorphism(
            left, right, node_affinity=None, impl="reference-rust", rooted=rooted)
        assert score == 2
        assert set(first) <= set(left) and set(second) <= set(right)
        assert len(first.edges) == len(second.edges) == 1
        if rooted:
            assert "root" in first and "x" in second
    assert "reference-rust" not in iso.available_impls_longest_common_balanced_isomorphism()
    assert "reference-rust" in iso.available_impls_longest_common_balanced_isomorphism(include_restricted=True)
    monkeypatch.setattr(iso, "_rust_lcsi_backend", lambda *a, **kw: None)
    assert "reference-rust" not in iso.available_impls_longest_common_balanced_isomorphism(include_restricted=True)


@pytest.mark.parametrize("affinity", ["auto", "eq", lambda a, b: 2])
def test_reference_rejects_unsupported_weight_modes(affinity):
    with pytest.raises(ValueError, match="requires node_affinity=None"):
        iso.longest_common_balanced_isomorphism("()", "()", {"(": ")"},
                                              node_affinity=affinity, impl="reference-rust")


def test_reference_raw_original_token_indices_and_malformed_sides(backend):
    solve = backend.maximum_common_token_isomorphism
    left = [False, False, True, True, False, True]
    right = [False, True, False, True]
    li, ri, score = solve(left, right, rooted=True)
    assert li == [0, 3, 4, 5] and ri == [0, 1, 2, 3] and score == 2
    for a, b, message in [([True], [], "left input: unexpected closing"),
                          ([], [False], "right input: missing closing")]:
        with pytest.raises(ValueError, match=message):
            solve(a, b)
