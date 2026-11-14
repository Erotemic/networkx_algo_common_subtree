"""Integration boundary between typed Python tokens and the proved Boolean core."""

import itertools

import pytest

from networkx_algo_common_subtree import balanced_embedding
from networkx_algo_common_subtree.balanced_sequence import UnbalancedException, generate_balance


def _backend():
    backend = pytest.importorskip("networkx_algo_common_subtree._rust")
    if not hasattr(backend, "maximum_common_token_embedding"):
        pytest.skip("Rust extension predates the verified token API")
    return backend


def _solve(left, right, pairs):
    _backend()
    return balanced_embedding.longest_common_balanced_embedding(
        left, right, pairs, node_affinity=None, impl="verified-rust"
    )


@pytest.mark.parametrize("container", [str, tuple, list])
def test_verified_typed_tokens_preserve_original_values_and_container(container):
    left, right = container("[({})]{}"), container("{[[]]}()")
    pairs = {"[": "]", "{": "}", "(": ")"}
    (out_left, out_right), score = _solve(left, right, pairs)
    assert type(out_left) is container
    assert type(out_right) is container
    assert len(out_left) == len(out_right) == 2 * score
    assert list(generate_balance(out_left, pairs))
    assert list(generate_balance(out_right, pairs))
    expected = balanced_embedding.longest_common_balanced_embedding(
        tuple(left), tuple(right), pairs, node_affinity=None, impl="iter"
    )[1]
    assert score == expected
    # Distinct alphabets can match because this API deliberately ignores labels.
    assert _solve(container("[]"), container("{}"), pairs) == (
        (container("[]"), container("{}")), 1
    )


@pytest.mark.parametrize("left,right", [("", ""), ("", "()"), ("()", "")])
def test_verified_empty_inputs(left, right):
    assert _solve(left, right, {"(": ")"}) == (("", ""), 0)


@pytest.mark.parametrize("bad", [")", "(", "([)]", "()x", "(()"])
def test_verified_typed_input_rejection(bad):
    _backend()
    with pytest.raises(UnbalancedException):
        _solve(bad, "()", {"(": ")", "[": "]"})
    with pytest.raises(UnbalancedException):
        _solve("()", bad, {"(": ")", "[": "]"})


@pytest.mark.parametrize("affinity", ["auto", "eq", lambda a, b: 2])
def test_verified_rejects_weighted_or_label_matching(affinity):
    with pytest.raises(ValueError, match="requires node_affinity=None"):
        balanced_embedding.longest_common_balanced_embedding(
            "()", "()", {"(": ")"}, node_affinity=affinity, impl="verified-rust"
        )


def test_verified_raw_ffi_indices_and_input_error_side():
    backend = _backend()
    indices_left, indices_right, score = backend.maximum_common_token_embedding(
        [False, True, False, True], [False, False, True, True]
    )
    assert score == 1
    assert len(indices_left) == len(indices_right) == 2
    assert [False, True, False, True][indices_left[0]] is False
    assert [False, True, False, True][indices_left[1]] is True
    with pytest.raises(ValueError, match="left input: unexpected closing"):
        backend.maximum_common_token_embedding([True], [False])
    with pytest.raises(ValueError, match="right input: missing closing"):
        backend.maximum_common_token_embedding([], [False])


def test_verified_all_balanced_words_through_four_pairs():
    backend = _backend()
    words = []
    for size in range(5):
        for word in itertools.product((False, True), repeat=2 * size):
            balance = 0
            for closing in word:
                balance += -1 if closing else 1
                if balance < 0:
                    break
            else:
                if balance == 0:
                    words.append(word)
    pairs = {False: True}
    for left, right in itertools.product(words, repeat=2):
        indices_left, indices_right, score = backend.maximum_common_token_embedding(left, right)
        out_left = tuple(left[index] for index in indices_left)
        out_right = tuple(right[index] for index in indices_right)
        assert out_left == out_right
        assert indices_left == sorted(set(indices_left))
        assert indices_right == sorted(set(indices_right))
        assert len(out_left) == 2 * score
        expected = 0 if not left or not right else balanced_embedding.longest_common_balanced_embedding(
            left, right, pairs, node_affinity=None, impl="iter"
        )[1]
        assert score == expected


def test_verified_discovery_is_explicit_and_optional(monkeypatch):
    _backend()
    assert "verified-rust" not in balanced_embedding.available_impls_longest_common_balanced_embedding()
    assert "verified-rust" in balanced_embedding.available_impls_longest_common_balanced_embedding(include_restricted=True)
    monkeypatch.setattr(balanced_embedding, "_rust_lcse_backend", lambda *args, **kwargs: None)
    assert "verified-rust" not in balanced_embedding.available_impls_longest_common_balanced_embedding(include_restricted=True)
    # An older installed extension still supports its established affinity API.
    monkeypatch.setattr(balanced_embedding, "_rust_lcse_backend", lambda *args, **kwargs: object())
    available = balanced_embedding.available_impls_longest_common_balanced_embedding(include_restricted=True)
    assert "iter-rust" in available
    assert "verified-rust" not in available


def test_verified_integer_tokens_and_original_readback():
    left, right = [10, 20, 10, 20], [30, 30, 40, 40]
    (out_left, out_right), score = _solve(left, right, {10: 20, 30: 40})
    assert (out_left, out_right, score) == ([10, 20], [30, 40], 1)


def test_verified_missing_extension_error(monkeypatch):
    from networkx_algo_common_subtree import balanced_embedding_rust

    def missing(error):
        raise ImportError("simulated absent Rust extension")

    monkeypatch.setattr(balanced_embedding_rust, "_rust_lcse_backend", missing)
    with pytest.raises(ImportError, match="simulated absent"):
        balanced_embedding.longest_common_balanced_embedding(
            "()", "()", {"(": ")"}, node_affinity=None, impl="verified-rust"
        )
