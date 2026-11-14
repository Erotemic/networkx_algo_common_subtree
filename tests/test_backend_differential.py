"""Independent small-input oracle and cross-backend parity checks.

The oracle enumerates balanced pair deletions directly; it never calls the
implementation's dynamic-programming recurrence. Compiled backends participate
when installed. Set COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS=1 in wheel CI to
require Cython and legacy Rust, rather than silently test Python alone.
"""

from __future__ import annotations

from functools import lru_cache
import os
import random

import pytest

from networkx_algo_common_subtree import balanced_embedding, balanced_isomorphism


BRACKETS = (("0", "1"), ("(", ")"))


@lru_cache(maxsize=None)
def _dyck_words(edge_count: int, alphabet: tuple[tuple[str, str], ...]):
    if edge_count == 0:
        return ("",)
    results = []
    for head_size in range(edge_count):
        tail_size = edge_count - head_size - 1
        for left, right in alphabet:
            for head in _dyck_words(head_size, alphabet):
                for tail in _dyck_words(tail_size, alphabet):
                    results.append(left + head + right + tail)
    return tuple(results)


@lru_cache(maxsize=None)
def _one_pair_deletions(word: str, alphabet: tuple[tuple[str, str], ...]):
    opener_to_closer = dict(alphabet)
    stack = []
    results = []
    for pos, token in enumerate(word):
        if token in opener_to_closer:
            stack.append((pos, opener_to_closer[token]))
        else:
            assert stack, (word, pos)
            begin, expected = stack.pop()
            assert token == expected, (word, pos)
            results.append(word[:begin] + word[begin + 1 : pos] + word[pos + 1 :])
    assert not stack, word
    return tuple(results)


@lru_cache(maxsize=None)
def _deletion_closure(word: str, alphabet: tuple[tuple[str, str], ...]):
    result = {word}
    for smaller in _one_pair_deletions(word, alphabet):
        result.update(_deletion_closure(smaller, alphabet))
    return frozenset(result)


def _embedding_oracle(left: str, right: str, alphabet):
    common = _deletion_closure(left, alphabet) & _deletion_closure(right, alphabet)
    return max(len(word) // 2 for word in common)


def _backends(kind: str, unweighted: bool):
    if kind == "embedding":
        available = balanced_embedding.available_impls_longest_common_balanced_embedding(
            include_restricted=unweighted
        )
    else:
        available = balanced_isomorphism.available_impls_longest_common_balanced_isomorphism()
    enabled = [p for p in ("iter", "recurse", "iter-cython", "iter-rust", "verified-rust") if p in available]
    if os.environ.get("COMMON_SUBTREE_REQUIRE_PARITY_BACKENDS") == "1":
        required = {"iter", "recurse", "iter-cython", "iter-rust"}
        if kind == "embedding" and unweighted:
            required.add("verified-rust")
        assert required <= set(enabled), f"missing required {kind} backends: {sorted(required - set(enabled))}"
    return enabled


def _solve(kind: str, left: str, right: str, alphabet, affinity: str | None, impl: str):
    solver = (
        balanced_embedding.longest_common_balanced_embedding
        if kind == "embedding"
        else balanced_isomorphism.longest_common_balanced_isomorphism
    )
    return solver(left, right, dict(alphabet), node_affinity=affinity, impl=impl)


def _check_case(kind: str, left: str, right: str, alphabet, affinity: str | None):
    backends = _backends(kind, unweighted=affinity is None)
    scores = {}
    left_closure = _deletion_closure(left, alphabet)
    right_closure = _deletion_closure(right, alphabet)
    for impl in backends:
        (out_left, out_right), score = _solve(kind, left, right, alphabet, affinity, impl)
        assert out_left in left_closure, (kind, impl, left, out_left)
        assert out_right in right_closure, (kind, impl, right, out_right)
        assert len(out_left) == len(out_right) == 2 * score, (kind, impl, score, out_left, out_right)
        assert out_left == out_right, (kind, impl, left, right, out_left, out_right)
        scores[impl] = score
    assert len(set(scores.values())) == 1, (kind, left, right, scores)
    if kind == "embedding":
        assert next(iter(scores.values())) == _embedding_oracle(left, right, alphabet), (left, right, scores)


@pytest.mark.parametrize("kind", ["embedding", "isomorphism"])
def test_exhaustive_single_label_through_four_edges(kind):
    alphabet = BRACKETS[:1]
    words = [word for n in range(5) for word in _dyck_words(n, alphabet)]
    for left in words:
        for right in words:
            _check_case(kind, left, right, alphabet, None)


@pytest.mark.parametrize("kind", ["embedding", "isomorphism"])
def test_labeled_equality_affinity_and_adversarial_shapes(kind):
    alphabet = BRACKETS
    rng = random.Random(20261114)
    words = [word for n in range(4) for word in _dyck_words(n, alphabet)]
    samples = [(left, right) for left in words[:11] for right in words[:11]]
    samples += [(rng.choice(words), rng.choice(words)) for _ in range(120)]
    for left, right in samples:
        _check_case(kind, left, right, alphabet, "eq")


@pytest.mark.parametrize("kind", ["embedding", "isomorphism"])
def test_empty_word_iterative_regression(kind):
    for left, right in [("", ""), ("", "01"), ("01", "")]:
        _check_case(kind, left, right, BRACKETS[:1], None)
