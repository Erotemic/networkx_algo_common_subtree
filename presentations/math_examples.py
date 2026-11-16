"""Tiny, dependency-free mathematical examples for the animated lectures.

This module intentionally does not import the repository's DP solvers. Its
small exhaustive contraction oracle is used to validate examples drawn in
slides. It is not a replacement for the repository's independent Lean proofs.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Optional


@dataclass(frozen=True)
class OrderedTree:
    label: str
    children: tuple["OrderedTree", ...] = ()

    @property
    def edge_count(self) -> int:
        return sum(1 + c.edge_count for c in self.children)

    @property
    def vertex_depth(self) -> int:
        """Root-to-leaf vertex count, including the singleton's root."""
        return 1 + max((c.vertex_depth for c in self.children), default=0)

    @property
    def leaf_count(self) -> int:
        return sum(c.leaf_count for c in self.children) if self.children else 1


def node(label: str, *children: OrderedTree) -> OrderedTree:
    return OrderedTree(label, tuple(children))


def encode_tree(tree: OrderedTree) -> str:
    """One matched pair per non-root vertex; ordered depth-first encoding."""
    return "".join("0" + encode_tree(child) + "1" for child in tree.children)


def decode_tree(word: str) -> OrderedTree:
    """Decode a balanced word; use its implicit root as the outer tree root."""
    root: list = ["root", []]
    stack = [root]
    for token in word:
        if token == "0":
            child: list = ["v", []]
            stack[-1][1].append(child)
            stack.append(child)
        elif token == "1":
            if len(stack) == 1:
                raise ValueError("unmatched closing token")
            stack.pop()
        else:
            raise ValueError("expected only 0 and 1")
    if len(stack) != 1:
        raise ValueError("unmatched opening token")

    def freeze(mutable: list) -> OrderedTree:
        return node(mutable[0], *(freeze(c) for c in mutable[1]))

    return freeze(root)


def all_dyck_words(edges: int) -> tuple[str, ...]:
    if edges < 0:
        raise ValueError(edges)
    return _all_dyck_words(edges)


@lru_cache(maxsize=None)
def _all_dyck_words(edges: int) -> tuple[str, ...]:
    if edges == 0:
        return ("",)
    return tuple(
        "0" + inside + "1" + outside
        for inside_size in range(edges)
        for inside in _all_dyck_words(inside_size)
        for outside in _all_dyck_words(edges - 1 - inside_size)
    )


def contract_edge(tree: OrderedTree, path: tuple[int, ...]) -> OrderedTree:
    """Delete a non-root vertex, splicing its ordered children into its parent."""
    if not path:
        raise ValueError("The implicit root cannot be contracted")
    index = path[0]
    if index < 0 or index >= len(tree.children):
        raise IndexError(path)
    if len(path) == 1:
        child = tree.children[index]
        return node(
            tree.label,
            *tree.children[:index],
            *child.children,
            *tree.children[index + 1 :],
        )
    updated = contract_edge(tree.children[index], path[1:])
    children = tree.children[:index] + (updated,) + tree.children[index + 1 :]
    return OrderedTree(tree.label, children)


def contraction_paths(tree: OrderedTree, prefix: tuple[int, ...] = ()) -> tuple[tuple[int, ...], ...]:
    return tuple(
        path
        for index, child in enumerate(tree.children)
        for path in ((prefix + (index,),) + contraction_paths(child, prefix + (index,)))
    )


def contract_once(tree: OrderedTree) -> set[OrderedTree]:
    return {contract_edge(tree, p) for p in contraction_paths(tree)}


def all_contractions(tree: OrderedTree) -> set[OrderedTree]:
    """Exhaustive tiny-tree oracle; labels are normalized to ignore vertex IDs."""
    normalized = decode_tree(encode_tree(tree))
    visited = {normalized}
    frontier = [normalized]
    while frontier:
        curr = frontier.pop()
        for next_tree in contract_once(curr):
            if next_tree not in visited:
                visited.add(next_tree)
                frontier.append(next_tree)
    return visited


def common_embedding_oracle(a: OrderedTree, b: OrderedTree) -> tuple[int, str]:
    possible = all_contractions(a) & all_contractions(b)
    best = max(possible, key=lambda t: (t.edge_count, encode_tree(t)))
    return best.edge_count, encode_tree(best)


def split_first_pair(word: str) -> tuple[str, str]:
    if not word:
        raise ValueError("empty word has no first pair")
    balance = 0
    for idx, token in enumerate(word):
        balance += 1 if token == "0" else -1
        if balance == 0:
            return word[1:idx], word[idx + 1 :]
    raise ValueError("unbalanced word")


@lru_cache(maxsize=None)
def lozano_dp_word(a: str, b: str) -> str:
    """The operational three-branch recurrence; independent oracle is above."""
    if not a or not b:
        return ""
    x, y = split_first_pair(a)
    u, v = split_first_pair(b)
    candidates = (
        "0" + lozano_dp_word(x, u) + "1" + lozano_dp_word(y, v),
        lozano_dp_word(x + y, b),
        lozano_dp_word(a, u + v),
    )
    return max(candidates, key=lambda word: (len(word), word))


def max_weight_partial_matching(
    weights: tuple[tuple[Optional[int], ...], ...],
) -> tuple[int, tuple[tuple[int, int], ...]]:
    """Enumerate all feasible small partial matchings; None forbids a pair."""
    ncols = len(weights[0]) if weights else 0
    if any(len(row) != ncols for row in weights):
        raise ValueError("ragged matrix")

    def search(row: int, used: frozenset[int]) -> tuple[int, tuple[tuple[int, int], ...]]:
        if row == len(weights):
            return 0, ()
        best = search(row + 1, used)
        for col, weight in enumerate(weights[row]):
            if col in used or weight is None:
                continue
            tail_score, tail_pairs = search(row + 1, used | {col})
            candidate = (weight + tail_score, ((row, col),) + tail_pairs)
            if candidate[0] > best[0]:
                best = candidate
        return best

    return search(0, frozenset())


def path_contribution(
    edge_reward: float, left_length: int, right_length: int, penalty: float
) -> float:
    """2018 Definition 4 direct-path rule for finite nonnegative penalties."""
    if left_length < 1 or right_length < 1 or penalty < 0:
        raise ValueError("paths must be positive; penalty nonnegative")
    if left_length == right_length == 1:
        return edge_reward
    return -penalty * ((left_length - 1) + (right_length - 1))


EXAMPLE_BRANCHING = node("r", node("a", node("b"), node("c")))
EXAMPLE_REDUCED = node("r", node("a", node("b")))
EXAMPLE_MATCHING = ((8, 1, 4), (3, 7, 2))


# Source-derived, checked examples used in the click-by-click lecture.
EXAMPLE_SPLICED = contract_edge(EXAMPLE_BRANCHING, (0,))


def lozano_recurrence_candidate_scores(a: str, b: str) -> tuple[int, int, int]:
    """Scores of the three operational branches for nonempty Dyck words."""
    x, y = split_first_pair(a)
    u, v = split_first_pair(b)
    return (
        1 + len(lozano_dp_word(x, u)) // 2 + len(lozano_dp_word(y, v)) // 2,
        len(lozano_dp_word(x + y, b)) // 2,
        len(lozano_dp_word(a, u + v)) // 2,
    )


def first_child_next_sibling(tree: OrderedTree):
    """Path identities mapped to (first child, next sibling), including root."""
    links = {}

    def visit(item, path, sibling):
        links[path] = (path + (0,) if item.children else None, sibling)
        for i, child in enumerate(item.children):
            next_path = path + (i + 1,) if i + 1 < len(item.children) else None
            visit(child, path + (i,), next_path)

    visit(tree, (), None)
    return links


def memoized_recurrence_trace(a: str, b: str):
    """Didactic request trace, checked separately against contraction optima.

    Each event is (expand/hit, key, score). Empty states are cached too.
    This is not instrumentation of the production Rust implementation.
    """
    cache = {}
    events = []

    def solve(left, right):
        key = (left, right)
        if key in cache:
            events.append(("hit", key, cache[key]))
            return cache[key]
        if not left or not right:
            score = 0
        else:
            x, y = split_first_pair(left)
            u, v = split_first_pair(right)
            score = max(1 + solve(x, u) + solve(y, v),
                        solve(x + y, right), solve(left, u + v))
        cache[key] = score
        events.append(("expand", key, score))
        return score

    return solve(a, b), tuple(events)


def flip_augmenting_path(matching, vertices):
    """Flip a simple alternating path from a free row to a free column.

    Vertices are ('L', row)/('R', column); every other edge must already be
    matched. Return a checked matching with one additional pair.
    """
    pairs = set(matching)
    if len({r for r, _ in pairs}) != len(pairs) or len({c for _, c in pairs}) != len(pairs):
        raise ValueError("input is not a matching")
    if len(vertices) < 2 or len(vertices) % 2 or len(set(vertices)) != len(vertices):
        raise ValueError("expected a simple augmenting path")
    if any(side != ("L" if i % 2 == 0 else "R") for i, (side, _) in enumerate(vertices)):
        raise ValueError("path must alternate row/column vertices")
    if vertices[0][1] in {r for r, _ in pairs} or vertices[-1][1] in {c for _, c in pairs}:
        raise ValueError("path endpoints must be free")
    for i, (a, b) in enumerate(zip(vertices, vertices[1:])):
        edge = (a[1], b[1]) if i % 2 == 0 else (b[1], a[1])
        if (edge in pairs) != (i % 2 == 1):
            raise ValueError("path edges do not alternate outside/inside the matching")
        pairs.symmetric_difference_update({edge})
    if len({r for r, _ in pairs}) != len(pairs) or len({c for _, c in pairs}) != len(pairs):
        raise ValueError("path flip did not produce a matching")
    return tuple(sorted(pairs))


def skipped_path_conflicts(paths, mapped):
    """Skipped vertices shared by paths, or used as mapped vertices.

    This diagnoses the collision drawn in the lecture. Host adjacency, endpoint
    identities and full embedding feasibility are separate conditions.
    """
    seen = set()
    conflicts = set()
    for path in paths:
        interior = set(path[1:-1])
        conflicts.update(interior & (seen | set(mapped)))
        seen.update(interior)
    return frozenset(conflicts)
