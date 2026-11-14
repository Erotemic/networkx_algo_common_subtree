"""Weighted unordered common trees (Droschinsky 2016 and 2018).

``impl="rust"`` runs the existing Rust dynamic programs. ``impl="python"``
enumerates vertex subsets and bijections and is intended for small references.
Weights are finite floats; ``None`` returned by a weight callback forbids a
pair. Signed weights and the nonempty objective are supported. Undirected edge
callbacks receive endpoint tuples in input edge-iteration order.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import isfinite

import networkx as nx

from . import common_subtree_reference as reference


@dataclass(frozen=True)
class CommonSubtreeResult:
    """An optimum and witness using the original input node objects.

    ``node_pairs`` is an injective mapping. Each ``edge_paths`` entry contains
    aligned left/right paths for one edge of the common tree; skipped vertices
    are retained in those paths. Empty solutions have weight zero.
    """
    weight: float
    node_pairs: tuple
    edge_paths: tuple

    @property
    def mapping(self):
        """Return the original-node mapping as a dictionary."""
        return dict(self.node_pairs)


def available_unordered_backends():
    """Return usable weighted graph backends, fastest default first."""
    try:
        from . import _rust
    except ImportError:
        return ["python"]
    return ["rust", "python"] if hasattr(_rust, "maximum_common_subtree_isomorphism") else ["python"]


def _finite(value):
    try:
        value = float(value)
    except (OverflowError, TypeError, ValueError) as ex:
        raise ValueError("weights must be finite numbers or callback results must be None") from ex
    if not isfinite(value):
        raise ValueError("weights must be finite")
    return value


def _tree_data(graph, node_label, edge_label, node_codes, edge_codes):
    if not isinstance(graph, nx.Graph):
        raise TypeError("expected a NetworkX undirected tree")
    if graph.is_directed() or graph.is_multigraph():
        raise ValueError("expected an undirected simple tree")
    if len(graph) and not nx.is_tree(graph):
        raise ValueError("input graph must be a connected tree")
    nodes = tuple(graph.nodes)
    indices = {node: index for index, node in enumerate(nodes)}
    def encode(value, codes):
        try:
            return codes.setdefault(value, len(codes))
        except TypeError as ex:
            raise TypeError("node and edge labels must be hashable") from ex
    labels = tuple(encode(graph.nodes[u][node_label], node_codes) if node_label is not None else 0 for u in nodes)
    edges = tuple((indices[u], indices[v], encode(data[edge_label], edge_codes) if edge_label is not None else 0)
                  for u, v, data in graph.edges(data=True))
    return nodes, labels, edges


class _Scoring(reference.ExactLabelScoring):
    def __init__(self, node_weight, edge_weight, node_table, edge_table, left_edges, right_edges):
        super().__init__(node_weight, edge_weight)
        self.node_table = node_table
        self.edge_table = edge_table
        self.left_edges = {frozenset((u, v)): i for i, (u, v, _) in enumerate(left_edges)}
        self.right_edges = {frozenset((u, v)): i for i, (u, v, _) in enumerate(right_edges)}

    def node_weight(self, left, u, right, v):
        if self.node_table is not None:
            return self.node_table[u][v]
        return super().node_weight(left, u, right, v)

    def edge_weight(self, left, u, uc, right, v, vc):
        if self.edge_table is not None:
            return self.edge_table[self.left_edges[frozenset((u, uc))]][self.right_edges[frozenset((v, vc))]]
        return super().edge_weight(left, u, uc, right, v, vc)


class _Problem:
    def __init__(self, left, right, node_label, edge_label, node_weight, edge_weight):
        node_codes, edge_codes = {}, {}
        self.left = _tree_data(left, node_label, edge_label, node_codes, edge_codes)
        self.right = _tree_data(right, node_label, edge_label, node_codes, edge_codes)
        ln, ll, le = self.left
        rn, rl, re = self.right
        self.node_scalar = 1.0 if callable(node_weight) else _finite(node_weight)
        self.edge_scalar = 1.0 if callable(edge_weight) else _finite(edge_weight)
        def weight(callback, *args):
            value = callback(*args)
            return None if value is None else _finite(value)
        self.node_table = ([[weight(node_weight, u, v) if ll[i] == rl[j] else None
                             for j, v in enumerate(rn)] for i, u in enumerate(ln)]
                           if callable(node_weight) else None)
        self.edge_table = ([[weight(edge_weight, (ln[u], ln[v]), (rn[x], rn[y])) if label == other else None
                             for x, y, other in re] for u, v, label in le]
                           if callable(edge_weight) else None)
        self.scoring = _Scoring(self.node_scalar, self.edge_scalar, self.node_table, self.edge_table, le, re)

    def references(self):
        return (reference.ReferenceLabeledTree(self.left[1], self.left[2]),
                reference.ReferenceLabeledTree(self.right[1], self.right[2]))

    def result(self, weight, pairs, paths):
        left, right = self.left[0], self.right[0]
        return CommonSubtreeResult(float(weight), tuple((left[u], right[v]) for u, v in pairs),
                                   tuple((tuple(left[u] for u in lp), tuple(right[v] for v in rp)) for lp, rp in paths))


def _solve(problem, impl, allow_empty, penalty):
    if impl == "auto":
        impl = available_unordered_backends()[0]
    if impl not in {"rust", "python"}:
        raise ValueError(f"unknown unordered-tree backend: {impl!r}")
    if penalty is not None:
        penalty = _finite(penalty)
        if penalty < 0:
            raise ValueError("skip vertex penalty must be finite and nonnegative")
    if impl == "rust":
        from . import _rust
        name = ("maximum_common_subtree_isomorphism" if penalty is None else
                "largest_weight_common_subtree_embedding_with_distance_penalty")
        solver = getattr(_rust, name, None)
        if solver is None:
            raise ImportError("the Rust extension must be rebuilt for weighted graph algorithms")
        kwargs = dict(node_weights=problem.node_table, edge_weights=problem.edge_table,
                      node_match_weight=problem.node_scalar, edge_match_weight=problem.edge_scalar, allow_empty=allow_empty)
        if penalty is not None:
            kwargs["skip_vertex_penalty"] = penalty
        raw = solver(problem.left[1], problem.left[2], problem.right[1], problem.right[2], **kwargs)
        return None if raw is None else problem.result(*raw)
    left, right = problem.references()
    if penalty is None:
        solver = (reference.maximum_common_subtree_isomorphism_reference if allow_empty else
                  reference.maximum_nonempty_common_subtree_isomorphism_reference)
        raw = solver(left, right, problem.scoring)
    else:
        solver = (reference.largest_weight_common_subtree_embedding_with_distance_penalty_reference if allow_empty else
                  reference.largest_weight_nonempty_common_subtree_embedding_with_distance_penalty_reference)
        raw = solver(left, right, problem.scoring, penalty)
    if raw is None:
        return None
    mapping = dict(raw.node_pairs)
    paths = []
    if len(mapping) > 1:
        for u, v in reference._embedding_skeleton_edges(left, tuple(sorted(mapping))):
            paths.append((left.path(u, v), right.path(mapping[u], mapping[v])))
    return problem.result(raw.weight, raw.node_pairs, paths)


def maximum_common_subtree_isomorphism(tree1, tree2, *, node_label=None, edge_label=None,
                                       node_weight=1.0, edge_weight=1.0, allow_empty=True, impl="auto"):
    """Maximum-weight connected unordered subtree isomorphism (2016).

    Inputs are undirected NetworkX trees, including empty trees. Label options
    name attributes whose values must match; omitted labels allow any pairing.
    Weights are finite numbers or callbacks: ``node_weight(u, v)`` and
    ``edge_weight((u, uc), (v, vc))``. Callbacks may return ``None`` to forbid a
    pair and are evaluated once per compatible input pair before the Rust DP.
    Zero and negative scores are meaningful. The empty score-zero witness is
    allowed by default; ``allow_empty=False`` retains negative optima and
    returns ``None`` only when no compatible nonempty witness exists.

    Ties are deterministic for a fixed input iteration order and backend;
    different backends may choose different optimal witnesses. Rust uses f64
    arithmetic; it is tested against independent oracles, not yet source proved.
    """
    problem = _Problem(tree1, tree2, node_label, edge_label, node_weight, edge_weight)
    return _solve(problem, impl, allow_empty, None)


def largest_weight_common_subtree_embedding_with_distance_penalty(
        tree1, tree2, *, skip_vertex_penalty=0.0, node_label=None, edge_label=None,
        node_weight=1.0, edge_weight=1.0, allow_empty=True, impl="auto"):
    """Largest-weight unordered topological tree embedding (2018).

    Scoring/backend options follow :func:`maximum_common_subtree_isomorphism`.
    ``skip_vertex_penalty`` is finite and nonnegative. An edge reward and edge
    compatibility apply only when **both** matched paths consist of one edge.
    Every longer path contributes only the penalty for its skipped vertices.
    The result includes aligned original-node paths for independent inspection.
    """
    problem = _Problem(tree1, tree2, node_label, edge_label, node_weight, edge_weight)
    return _solve(problem, impl, allow_empty, skip_vertex_penalty)


def _rescore(problem, witness, penalty):
    left, right = problem.references()
    li = {node: i for i, node in enumerate(problem.left[0])}
    ri = {node: i for i, node in enumerate(problem.right[0])}
    pairs = witness.node_pairs if isinstance(witness, CommonSubtreeResult) else tuple(witness)
    try:
        indexed = tuple((li[u], ri[v]) for u, v in pairs)
    except KeyError as ex:
        raise ValueError("witness contains a node outside its input tree") from ex
    if penalty is None:
        score = reference.score_subtree_isomorphism_witness(left, right, indexed, problem.scoring)
    else:
        score = reference.score_embedding_witness(left, right, indexed, problem.scoring, penalty)
    if isinstance(witness, CommonSubtreeResult):
        if len(witness.edge_paths) != max(0, len(pairs)-1):
            raise ValueError("witness paths do not describe a tree on its mapped vertices")
        mapping = dict(indexed)
        seen = set()
        for lp, rp in witness.edge_paths:
            try:
                lp, rp = tuple(li[u] for u in lp), tuple(ri[v] for v in rp)
            except KeyError as ex:
                raise ValueError("witness path contains an unknown vertex") from ex
            if len(lp) < 2 or len(rp) < 2 or mapping.get(lp[0]) != rp[0] or mapping.get(lp[-1]) != rp[-1]:
                raise ValueError("witness path endpoints disagree with its mapping")
            if lp != left.path(lp[0], lp[-1]) or rp != right.path(rp[0], rp[-1]):
                raise ValueError("witness paths must be original simple tree paths")
            if any(u in mapping for u in lp[1:-1]) or any(v in mapping.values() for v in rp[1:-1]):
                raise ValueError("witness path contains an interior mapped vertex")
            key = frozenset((lp[0], lp[-1]))
            if key in seen or (penalty is None and (len(lp) != 2 or len(rp) != 2)):
                raise ValueError("witness paths repeat an edge or violate isomorphism adjacency")
            seen.add(key)
    return score


def score_common_subtree_isomorphism(tree1, tree2, witness, *, node_label=None, edge_label=None, node_weight=1.0, edge_weight=1.0):
    """Independently validate and rescore an original-node 2016 witness."""
    return _rescore(_Problem(tree1, tree2, node_label, edge_label, node_weight, edge_weight), witness, None)


def score_common_subtree_embedding(tree1, tree2, witness, *, skip_vertex_penalty=0.0, node_label=None, edge_label=None, node_weight=1.0, edge_weight=1.0):
    """Independently validate/rescore original-node paths using the 2018 rule."""
    penalty = _finite(skip_vertex_penalty)
    if penalty < 0:
        raise ValueError("skip vertex penalty must be finite and nonnegative")
    return _rescore(_Problem(tree1, tree2, node_label, edge_label, node_weight, edge_weight), witness, penalty)


__all__ = ["CommonSubtreeResult", "available_unordered_backends", "maximum_common_subtree_isomorphism",
           "largest_weight_common_subtree_embedding_with_distance_penalty", "score_common_subtree_isomorphism", "score_common_subtree_embedding"]
