"""
Slow reference implementations for weighted common subtree algorithms.

This module is intentionally optimized for clarity instead of speed.  It is a
small executable specification for the graph-only algorithms described in:

* Droschinsky, Kriege, and Mutzel, "Faster Algorithms for the Maximum Common
  Subtree Isomorphism Problem", arXiv:1602.07210.
* Droschinsky, Kriege, and Mutzel, "Largest Weight Common Subtree Embeddings
  with Distance Penalties", arXiv:1805.00821.

The production-oriented Rust crate solves the same kinds of subproblems with
rooted dynamic programs and bipartite matchings.  The functions here instead
enumerate candidate vertex sets and bijections directly.  That makes them useful
as test oracles for very small trees, but unsuitable for normal workloads.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from itertools import combinations, permutations
from typing import Callable, Iterable

Weight = float
NodeId = int
Edge = tuple[NodeId, NodeId, int]
NodeWeightFn = Callable[["ReferenceLabeledTree", NodeId, "ReferenceLabeledTree", NodeId], Weight | None]
EdgeWeightFn = Callable[
    ["ReferenceLabeledTree", NodeId, NodeId, "ReferenceLabeledTree", NodeId, NodeId],
    Weight | None,
]

_EPS = 1.0e-9


@dataclass(frozen=True)
class ReferenceCommonSubtree:
    """Result returned by the slow reference algorithms."""

    weight: Weight
    node_pairs: tuple[tuple[NodeId, NodeId], ...]


@dataclass(frozen=True)
class ReferenceLabeledTree:
    """A minimal undirected labeled tree used by the reference algorithms.

    Parameters
    ----------
    node_labels:
        Label for each node.  Nodes are the integer positions in this tuple.
    edges:
        Undirected edges encoded as ``(u, v, label)`` triples.

    Notes
    -----
    The constructor validates the tree invariant.  This keeps the reference
    implementation explicit and avoids depending on NetworkX traversal details.
    """

    node_labels: tuple[int, ...]
    edges: tuple[Edge, ...]

    def __init__(self, node_labels: Iterable[int], edges: Iterable[Edge]):
        labels = tuple(node_labels)
        edge_tuple = tuple((int(u), int(v), int(label)) for u, v, label in edges)
        _validate_tree(labels, edge_tuple)
        object.__setattr__(self, "node_labels", labels)
        object.__setattr__(self, "edges", edge_tuple)

    @property
    def n(self) -> int:
        """Number of nodes."""

        return len(self.node_labels)

    def node_label(self, node: NodeId) -> int:
        """Return a node label."""

        return self.node_labels[node]

    def neighbors(self, node: NodeId) -> tuple[tuple[NodeId, int], ...]:
        """Return ``(neighbor, edge_label)`` pairs incident to ``node``."""

        out = []
        for u, v, label in self.edges:
            if u == node:
                out.append((v, label))
            elif v == node:
                out.append((u, label))
        return tuple(out)

    def edge_label(self, u: NodeId, v: NodeId) -> int | None:
        """Return the label of edge ``u-v`` if it exists."""

        for a, b, label in self.edges:
            if (a == u and b == v) or (a == v and b == u):
                return label
        return None

    def path(self, start: NodeId, stop: NodeId) -> tuple[NodeId, ...]:
        """Return the unique simple path from ``start`` to ``stop``."""

        if start == stop:
            return (start,)
        parent: dict[int, int | None] = {start: None}
        queue = deque([start])
        while queue:
            u = queue.popleft()
            for v, _label in self.neighbors(u):
                if v not in parent:
                    parent[v] = u
                    if v == stop:
                        queue.clear()
                        break
                    queue.append(v)
        if stop not in parent:  # pragma: no cover - constructor prevents this
            raise ValueError("tree is disconnected")
        rev = [stop]
        while rev[-1] != start:
            prev = parent[rev[-1]]
            assert prev is not None
            rev.append(prev)
        return tuple(reversed(rev))


class ExactLabelScoring:
    """Default exact node-label and edge-label scoring.

    A compatible node pair contributes ``node_match_weight``.  A compatible edge
    pair contributes ``edge_match_weight``.  Label mismatches are incompatible.
    """

    def __init__(self, node_match_weight: Weight = 1.0, edge_match_weight: Weight = 1.0):
        self.node_match_weight = float(node_match_weight)
        self.edge_match_weight = float(edge_match_weight)

    def node_weight(
        self,
        left: ReferenceLabeledTree,
        u: NodeId,
        right: ReferenceLabeledTree,
        v: NodeId,
    ) -> Weight | None:
        if left.node_label(u) == right.node_label(v):
            return self.node_match_weight
        return None

    def edge_weight(
        self,
        left: ReferenceLabeledTree,
        u: NodeId,
        u_child: NodeId,
        right: ReferenceLabeledTree,
        v: NodeId,
        v_child: NodeId,
    ) -> Weight | None:
        if left.edge_label(u, u_child) == right.edge_label(v, v_child):
            return self.edge_match_weight
        return None


def maximum_common_subtree_isomorphism_reference(
    left: ReferenceLabeledTree,
    right: ReferenceLabeledTree,
    scoring: ExactLabelScoring | None = None,
) -> ReferenceCommonSubtree:
    """Brute-force maximum common subtree isomorphism.

    This directly enumerates every connected vertex subset of each tree and
    every bijection between equal-sized subsets.  A bijection is accepted only
    when node compatibility holds and every chosen edge in the first subtree is
    mapped to a chosen edge in the second subtree.  The best accepted bijection
    is returned.

    The algorithm is exponential and should only be used for small tests.
    """

    scoring = ExactLabelScoring() if scoring is None else scoring
    best = ReferenceCommonSubtree(0.0, ())
    for left_subset in _connected_subsets(left):
        left_edges = _induced_edges(left, left_subset)
        for right_subset in _connected_subsets(right):
            if len(left_subset) != len(right_subset):
                continue
            right_subset_set = frozenset(right_subset)
            for right_perm in permutations(right_subset):
                node_map = dict(zip(left_subset, right_perm))
                candidate = _score_exact_subtree_bijection(
                    left, right, scoring, left_subset, left_edges, right_subset_set, node_map
                )
                if candidate is not None:
                    best = _keep_better(best, candidate)
    return best


def largest_weight_common_subtree_embedding_with_distance_penalty_reference(
    left: ReferenceLabeledTree,
    right: ReferenceLabeledTree,
    scoring: ExactLabelScoring | None = None,
    skip_vertex_penalty: Weight = 0.0,
) -> ReferenceCommonSubtree:
    """Brute-force common subtree embedding with skipped-vertex penalties.

    The reference enumerates a set of mapped vertices in each input tree and a
    bijection between the two sets.  For a selected vertex set, the embedding
    skeleton connects two selected vertices when the path between them contains
    no other selected vertex.  A bijection is accepted when it is an isomorphism
    between the two embedding skeletons.

    The objective is the sum of compatible mapped-node weights and compatible
    skeleton-edge weights, minus ``skip_vertex_penalty`` for every internal path
    vertex skipped by the two skeleton-edge embeddings.

    This is exponential and intended only for small correctness tests.
    """

    scoring = ExactLabelScoring() if scoring is None else scoring
    best = ReferenceCommonSubtree(0.0, ())
    for left_subset in _nonempty_subsets(left.n):
        left_skeleton = _embedding_skeleton_edges(left, left_subset)
        for right_subset in _nonempty_subsets(right.n):
            if len(left_subset) != len(right_subset):
                continue
            right_skeleton = _embedding_skeleton_edges(right, right_subset)
            right_skeleton_set = frozenset(_normalized_edge(u, v) for u, v in right_skeleton)
            for right_perm in permutations(right_subset):
                node_map = dict(zip(left_subset, right_perm))
                candidate = _score_embedding_bijection(
                    left,
                    right,
                    scoring,
                    left_subset,
                    left_skeleton,
                    right_skeleton_set,
                    node_map,
                    skip_vertex_penalty,
                )
                if candidate is not None:
                    best = _keep_better(best, candidate)
    return best


def _validate_tree(labels: tuple[int, ...], edges: tuple[Edge, ...]) -> None:
    n = len(labels)
    if n == 0:
        if edges:
            raise ValueError("an empty tree cannot contain edges")
        return
    if len(edges) != n - 1:
        raise ValueError(f"a tree with {n} nodes must contain {n - 1} edges")
    adj = [[] for _ in range(n)]
    for u, v, _label in edges:
        if not (0 <= u < n and 0 <= v < n):
            raise ValueError(f"edge ({u}, {v}) is out of bounds for {n} nodes")
        if u == v:
            raise ValueError("self-loops are not tree edges")
        adj[u].append(v)
        adj[v].append(u)
    seen = {0}
    queue = deque([0])
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    if len(seen) != n:
        raise ValueError("input graph is disconnected")


def _nonempty_subsets(n: int) -> Iterable[tuple[int, ...]]:
    nodes = tuple(range(n))
    for size in range(1, n + 1):
        yield from combinations(nodes, size)


def _connected_subsets(tree: ReferenceLabeledTree) -> Iterable[tuple[int, ...]]:
    for subset in _nonempty_subsets(tree.n):
        if _is_connected_subset(tree, subset):
            yield subset


def _is_connected_subset(tree: ReferenceLabeledTree, subset: tuple[int, ...]) -> bool:
    wanted = frozenset(subset)
    seen = {subset[0]}
    queue = deque([subset[0]])
    while queue:
        u = queue.popleft()
        for v, _label in tree.neighbors(u):
            if v in wanted and v not in seen:
                seen.add(v)
                queue.append(v)
    return len(seen) == len(wanted)


def _induced_edges(tree: ReferenceLabeledTree, subset: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    wanted = frozenset(subset)
    out = []
    for u, v, _label in tree.edges:
        if u in wanted and v in wanted:
            out.append(_normalized_edge(u, v))
    return tuple(sorted(out))


def _embedding_skeleton_edges(tree: ReferenceLabeledTree, subset: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    selected = frozenset(subset)
    out = []
    for u, v in combinations(subset, 2):
        path = tree.path(u, v)
        interior = path[1:-1]
        if not any(node in selected for node in interior):
            out.append(_normalized_edge(u, v))
    # Every nonempty selected set in a tree induces a tree-shaped embedding
    # skeleton, so exactly |subset| - 1 skeleton edges should be present.
    assert len(out) == len(subset) - 1
    return tuple(sorted(out))


def _score_exact_subtree_bijection(
    left: ReferenceLabeledTree,
    right: ReferenceLabeledTree,
    scoring: ExactLabelScoring,
    left_subset: tuple[int, ...],
    left_edges: tuple[tuple[int, int], ...],
    right_subset_set: frozenset[int],
    node_map: dict[int, int],
) -> ReferenceCommonSubtree | None:
    del right_subset_set  # The connectivity invariant is checked before this helper is called.
    weight = 0.0
    for u in left_subset:
        node_w = scoring.node_weight(left, u, right, node_map[u])
        if node_w is None:
            return None
        weight += node_w
    for u, u2 in left_edges:
        v = node_map[u]
        v2 = node_map[u2]
        if right.edge_label(v, v2) is None:
            return None
        edge_w = scoring.edge_weight(left, u, u2, right, v, v2)
        if edge_w is None:
            return None
        weight += edge_w
    return ReferenceCommonSubtree(weight, tuple(sorted(node_map.items())))


def _score_embedding_bijection(
    left: ReferenceLabeledTree,
    right: ReferenceLabeledTree,
    scoring: ExactLabelScoring,
    left_subset: tuple[int, ...],
    left_skeleton: tuple[tuple[int, int], ...],
    right_skeleton_set: frozenset[tuple[int, int]],
    node_map: dict[int, int],
    skip_vertex_penalty: Weight,
) -> ReferenceCommonSubtree | None:
    weight = 0.0
    for u in left_subset:
        node_w = scoring.node_weight(left, u, right, node_map[u])
        if node_w is None:
            return None
        weight += node_w
    for u, u2 in left_skeleton:
        v = node_map[u]
        v2 = node_map[u2]
        if _normalized_edge(v, v2) not in right_skeleton_set:
            return None
        left_path = left.path(u, u2)
        right_path = right.path(v, v2)
        left_next = left_path[1]
        right_next = right_path[1]
        edge_w = scoring.edge_weight(left, u, left_next, right, v, right_next)
        if edge_w is None:
            return None
        skipped = (len(left_path) - 2) + (len(right_path) - 2)
        weight += edge_w - skip_vertex_penalty * skipped
    return ReferenceCommonSubtree(weight, tuple(sorted(node_map.items())))


def _normalized_edge(u: int, v: int) -> tuple[int, int]:
    return (u, v) if u < v else (v, u)


def _keep_better(best: ReferenceCommonSubtree, candidate: ReferenceCommonSubtree) -> ReferenceCommonSubtree:
    if candidate.weight <= _EPS:
        return best
    if candidate.weight > best.weight + _EPS:
        return candidate
    if abs(candidate.weight - best.weight) <= _EPS and candidate.node_pairs < best.node_pairs:
        return candidate
    return best


__all__ = [
    "ExactLabelScoring",
    "ReferenceCommonSubtree",
    "ReferenceLabeledTree",
    "largest_weight_common_subtree_embedding_with_distance_penalty_reference",
    "maximum_common_subtree_isomorphism_reference",
]
