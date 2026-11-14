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


@lru_cache(maxsize=None)
def _isomorphism_closure(word: str, alphabet, rooted=False):
    """Enumerate adjacency-preserving selections with one common parent.

    Parse the original parent relation, then inspect every vertex subset.
    Every retained component root must have the same original parent (possibly
    the virtual parent of the whole forest). Missing intermediate ancestors
    are therefore forbidden. This is subset enumeration, not the DP's
    head/tail or level/general recurrence. The parent is not itself scored.
    """
    stack, parents, pair_ids = [], [], []
    for token in word:
        if token in dict(alphabet):
            index = len(parents)
            parents.append(stack[-1] if stack else -1)
            stack.append(index)
            pair_ids.append(index)
        else:
            pair_ids.append(stack.pop())
    result = {""}
    for mask in range(1, 1 << len(parents)):
        selected = {i for i in range(len(parents)) if mask & (1 << i)}
        external_parents = {parents[i] for i in selected if parents[i] not in selected}
        if len(external_parents) == 1 and (not rooted or external_parents == {-1}):
            result.add("".join(token for token, i in zip(word, pair_ids) if i in selected))
    return frozenset(result)


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


def _solve(kind: str, left: str, right: str, alphabet, affinity: str | None, impl: str, *, rooted=False):
    solver = (
        balanced_embedding.longest_common_balanced_embedding
        if kind == "embedding"
        else balanced_isomorphism.longest_common_balanced_isomorphism
    )
    options = {"rooted": rooted} if kind == "isomorphism" else {}
    return solver(left, right, dict(alphabet), node_affinity=affinity, impl=impl, **options)


def _check_case(kind: str, left: str, right: str, alphabet, affinity: str | None, *, rooted=False):
    backends = _backends(kind, unweighted=affinity is None)
    scores = {}
    closure = _deletion_closure if kind == "embedding" else _isomorphism_closure
    options = {"rooted": rooted} if kind == "isomorphism" else {}
    left_closure = closure(left, alphabet, **options)
    right_closure = closure(right, alphabet, **options)
    for impl in backends:
        (out_left, out_right), score = _solve(kind, left, right, alphabet, affinity, impl, rooted=rooted)
        assert out_left in left_closure, (kind, impl, left, out_left)
        assert out_right in right_closure, (kind, impl, right, out_right)
        assert len(out_left) == len(out_right) == 2 * score, (kind, impl, score, out_left, out_right)
        assert out_left == out_right, (kind, impl, left, right, out_left, out_right)
        scores[impl] = score
    assert len(set(scores.values())) == 1, (kind, left, right, scores)
    if kind == "embedding":
        assert next(iter(scores.values())) == _embedding_oracle(left, right, alphabet), (left, right, scores)
    else:
        optimum = max(len(word) // 2 for word in left_closure & right_closure)
        assert next(iter(scores.values())) == optimum, (left, right, scores)


@pytest.mark.parametrize("kind", ["embedding", "isomorphism"])
def test_exhaustive_single_label_through_four_edges(kind):
    alphabet = BRACKETS[:1]
    words = [word for n in range(5) for word in _dyck_words(n, alphabet)]
    for left in words:
        for right in words:
            _check_case(kind, left, right, alphabet, None)


def test_exhaustive_rooted_isomorphism_through_four_pairs():
    alphabet = BRACKETS[:1]
    words = [word for n in range(5) for word in _dyck_words(n, alphabet)]
    for left in words:
        for right in words:
            _check_case("isomorphism", left, right, alphabet, None, rooted=True)


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


def _indexed_word(word, offset):
    """Give each original pair a unique opening/closing token."""
    stack, sequence, mapping = [], [], {}
    for token in word:
        if token == "0":
            opening = offset + 2 * len(mapping)
            mapping[opening] = opening + 1
            stack.append(opening)
            sequence.append(opening)
        else:
            sequence.append(stack.pop() + 1)
    return tuple(sequence), mapping


def _subset_witnesses(sequence, pairs, kind, *, rooted=False):
    """Original-index subsets and their shape, with explicit parent checks."""
    stack, parents, ids = [], {}, []
    for token in sequence:
        if token in pairs:
            parents[token] = stack[-1] if stack else None
            stack.append(token)
            ids.append(token)
        else:
            ids.append(stack.pop())
    vertices = tuple(parents)
    records = []
    for mask in range(1 << len(vertices)):
        selected = {v for i, v in enumerate(vertices) if mask & (1 << i)}
        if kind == "isomorphism" and selected:
            external = {parents[v] for v in selected if parents[v] not in selected}
            if len(external) != 1 or (rooted and external != {None}):
                continue
        witness = tuple(token for token, v in zip(sequence, ids) if v in selected)
        shape = tuple(token in pairs for token in witness)
        records.append((witness, shape, tuple(v for v in vertices if v in selected)))
    return records


@pytest.mark.parametrize("kind", ["embedding", "isomorphism", "rooted-isomorphism"])
def test_fractional_affinity_optima_original_indices_and_rescoring(kind):
    rooted = kind == "rooted-isomorphism"
    oracle_kind = "embedding" if kind == "embedding" else "isomorphism"
    rng = random.Random(20042016)
    words = [w for n in range(5) for w in _dyck_words(n, BRACKETS[:1])]
    for _ in range(80):
        left, lp = _indexed_word(rng.choice(words), 0)
        right, rp = _indexed_word(rng.choice(words), 100)
        pairs = lp | rp
        # Distinct non-token original objects expose mapping/index confusion.
        nodes = {v: ("original", v) for v in pairs}
        weights = {(nodes[u], nodes[v]): rng.choice([0, .125, 1.0, 3.75]) for u in lp for v in rp}
        affinity = lambda u, v: weights[u, v]
        ls = _subset_witnesses(left, pairs, oracle_kind, rooted=rooted)
        rs = _subset_witnesses(right, pairs, oracle_kind, rooted=rooted)
        optimum = 0
        for _, lshape, lvertices in ls:
            for _, rshape, rvertices in rs:
                if lshape == rshape:
                    values = [weights[nodes[u], nodes[v]] for u, v in zip(lvertices, rvertices)]
                    if all(values):
                        optimum = max(optimum, sum(values))
        solver = (balanced_embedding.longest_common_balanced_embedding if kind == "embedding" else
                  balanced_isomorphism.longest_common_balanced_isomorphism)
        for impl in _backends(kind, unweighted=False):
            options = {"rooted": rooted} if oracle_kind == "isomorphism" else {}
            (out_left, out_right), score = solver(left, right, pairs, open_to_node=nodes,
                                                 node_affinity=affinity, impl=impl, **options)
            assert out_left in {x[0] for x in ls}, (kind, impl, left, out_left)
            assert out_right in {x[0] for x in rs}, (kind, impl, right, out_right)
            assert tuple(t in pairs for t in out_left) == tuple(t in pairs for t in out_right)
            values = [weights[nodes[u], nodes[v]] for u, v in
                      zip((t for t in out_left if t in pairs), (t for t in out_right if t in pairs))]
            assert all(values)
            assert sum(values) == score == optimum, (kind, impl, left, right, score, optimum)


@pytest.mark.parametrize("kind", ["embedding", "isomorphism"])
@pytest.mark.parametrize("weight", [1 + 2**-40, 1e-100, 1e100])
def test_affinity_preserves_double_precision_and_range(kind, weight):
    solver = (balanced_embedding.longest_common_balanced_embedding if kind == "embedding" else
              balanced_isomorphism.longest_common_balanced_isomorphism)
    for impl in _backends(kind, unweighted=False):
        witness, score = solver("01", "01", {"0": "1"}, node_affinity=lambda u, v: weight, impl=impl)
        assert witness == ("01", "01")
        assert score == weight, (impl, score, weight)
