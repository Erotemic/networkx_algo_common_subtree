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


def _distance_penalty(value):
    try:
        value = float(value)
    except (OverflowError, TypeError, ValueError) as ex:
        raise ValueError("skip vertex penalty must be nonnegative or positive infinity") from ex
    if not value >= 0:
        raise ValueError("skip vertex penalty must be nonnegative or positive infinity")
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
        a = self.left_edges.get(frozenset((u, uc)))
        b = self.right_edges.get(frozenset((v, vc)))
        if a is None or b is None:
            return None
        if self.edge_table is not None:
            return self.edge_table[a][b]
        if left.edges[a][2] == right.edges[b][2]:
            return self.edge_match_weight
        return None


class _Problem:
    def __init__(self, left, right, node_label, edge_label, node_weight, edge_weight,
                 *, roots=None, root_to_root=False):
        node_codes, edge_codes = {}, {}
        self.left = _tree_data(left, node_label, edge_label, node_codes, edge_codes)
        self.right = _tree_data(right, node_label, edge_label, node_codes, edge_codes)
        ln, ll, le = self.left
        rn, rl, re = self.right
        if not isinstance(root_to_root, bool):
            raise TypeError("root_to_root must be a bool")
        self.root_to_root = root_to_root
        self.roots = None
        if roots is None:
            if root_to_root:
                raise ValueError("root_to_root requires a pair of roots")
        else:
            try:
                u, v = roots
                self.roots = ({node: i for i, node in enumerate(ln)}[u],
                              {node: i for i, node in enumerate(rn)}[v])
            except (KeyError, TypeError, ValueError) as ex:
                raise ValueError("roots must be a pair of input tree vertices") from ex
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
    if impl == "rust":
        from . import _rust
        name = ("maximum_common_subtree_isomorphism" if penalty is None else
                "largest_weight_common_subtree_embedding_with_distance_penalty")
        solver = getattr(_rust, name, None)
        if solver is None:
            raise ImportError("the Rust extension must be rebuilt for weighted graph algorithms")
        kwargs = dict(node_weights=problem.node_table, edge_weights=problem.edge_table,
                      node_match_weight=problem.node_scalar, edge_match_weight=problem.edge_scalar, allow_empty=allow_empty)
        if problem.roots is not None:
            kwargs.update(roots=problem.roots, root_to_root=problem.root_to_root)
        if penalty is not None:
            kwargs["skip_vertex_penalty"] = penalty
        raw = solver(problem.left[1], problem.left[2], problem.right[1], problem.right[2], **kwargs)
        return None if raw is None else problem.result(*raw)
    left, right = problem.references()
    if penalty is None:
        solver = (reference.maximum_common_subtree_isomorphism_reference if allow_empty else
                  reference.maximum_nonempty_common_subtree_isomorphism_reference)
        raw = solver(left, right, problem.scoring, roots=problem.roots, root_to_root=problem.root_to_root)
    else:
        solver = (reference.largest_weight_common_subtree_embedding_with_distance_penalty_reference if allow_empty else
                  reference.largest_weight_nonempty_common_subtree_embedding_with_distance_penalty_reference)
        raw = solver(left, right, problem.scoring, penalty, roots=problem.roots, root_to_root=problem.root_to_root)
    if raw is None:
        return None
    mapping = dict(raw.node_pairs)
    paths = []
    if len(mapping) > 1:
        for u, v in reference._embedding_skeleton_edges(left, tuple(sorted(mapping))):
            paths.append((left.path(u, v), right.path(mapping[u], mapping[v])))
    return problem.result(raw.weight, raw.node_pairs, paths)


def maximum_common_subtree_isomorphism(tree1, tree2, *, node_label=None, edge_label=None,
                                       node_weight=1.0, edge_weight=1.0, allow_empty=True, impl="auto",
                                       roots=None, root_to_root=False):
    """Maximum-weight connected unordered subtree isomorphism (2016).

    Inputs are undirected NetworkX trees, including empty trees. Label options
    name attributes whose values must match; omitted labels allow any pairing.
    Weights are finite numbers or callbacks: ``node_weight(u, v)`` and
    ``edge_weight((u, uc), (v, vc))``. Callbacks may return ``None`` to forbid a
    pair and are evaluated once per compatible input pair before the Rust DP.
    Zero and negative scores are meaningful. The empty score-zero witness is
    allowed by default; ``allow_empty=False`` retains negative optima and
    returns ``None`` only when no compatible nonempty witness exists.

    ``roots=(left_root, right_root)`` fixes ambient orientations: a nonempty
    common tree must have one mapped pair ancestral to every selected vertex
    on both sides. Its root may occur below either supplied root. With
    ``root_to_root=True`` that pair must be the supplied roots themselves.
    Roots are original input vertices; omitting them gives the unrooted problem.
    The optional empty optimum remains permitted in each mode.

    Ties are deterministic for a fixed input iteration order and backend;
    different backends may choose different optimal witnesses. Rust uses f64
    arithmetic; it is tested against independent oracles, not yet source proved.
    """
    problem = _Problem(tree1, tree2, node_label, edge_label, node_weight, edge_weight,
                       roots=roots, root_to_root=root_to_root)
    return _solve(problem, impl, allow_empty, None)


def largest_weight_common_subtree_embedding_with_distance_penalty(
        tree1, tree2, *, skip_vertex_penalty=0.0, node_label=None, edge_label=None,
        node_weight=1.0, edge_weight=1.0, allow_empty=True, impl="auto",
        roots=None, root_to_root=False):
    """Largest-weight unordered topological tree embedding (2018).

    Scoring/backend options follow :func:`maximum_common_subtree_isomorphism`.
    ``skip_vertex_penalty`` is nonnegative or positive infinity. Infinity forbids
    skipped vertices and gives the common subtree isomorphism objective.
    An edge reward and edge
    compatibility apply only when **both** matched paths consist of one edge.
    Every longer path contributes only the penalty for its skipped vertices.
    The result includes aligned original-node paths for independent inspection.
    ``roots`` fixes ambient orientations, while ``root_to_root=True`` additionally
    requires the supplied root pair. These restrictions follow the distinct
    rooted and root-to-root contracts; they do not include unrooted paths whose
    highest ambient vertex is skipped between different branches.
    """
    problem = _Problem(tree1, tree2, node_label, edge_label, node_weight, edge_weight,
                       roots=roots, root_to_root=root_to_root)
    return _solve(problem, impl, allow_empty, _distance_penalty(skip_vertex_penalty))


def _score_path_witness(problem, left, right, indexed, paths, li, ri, penalty):
    """Check supplied paths directly, independently of the optimization DP."""
    if len(paths) != max(0, len(indexed) - 1):
        raise ValueError("witness paths do not describe a tree on its mapped vertices")
    mapping = dict(indexed)
    selected_right = set(mapping.values())
    skeleton = {u: [] for u in mapping}
    used_left, used_right, seen = set(), set(), set()
    contributions = []
    for lp, rp in paths:
        try:
            lp, rp = tuple(li[u] for u in lp), tuple(ri[v] for v in rp)
        except KeyError as ex:
            raise ValueError("witness path contains an unknown vertex") from ex
        if len(lp) < 2 or len(rp) < 2 or mapping.get(lp[0]) != rp[0] or mapping.get(lp[-1]) != rp[-1]:
            raise ValueError("witness path endpoints disagree with its mapping")
        if len(set(lp)) != len(lp) or len(set(rp)) != len(rp):
            raise ValueError("witness paths must be original simple tree paths")
        if (any(frozenset(edge) not in problem.scoring.left_edges for edge in zip(lp, lp[1:])) or
                any(frozenset(edge) not in problem.scoring.right_edges for edge in zip(rp, rp[1:]))):
            raise ValueError("witness paths must be original simple tree paths")
        left_interior, right_interior = set(lp[1:-1]), set(rp[1:-1])
        if left_interior.intersection(mapping) or right_interior.intersection(selected_right):
            raise ValueError("witness path contains an interior mapped vertex")
        if left_interior & used_left or right_interior & used_right:
            raise ValueError("witness paths overlap at an interior vertex")
        used_left.update(left_interior)
        used_right.update(right_interior)
        key = tuple(sorted((lp[0], lp[-1])))
        if key in seen or (penalty is None and (len(lp) != 2 or len(rp) != 2)):
            raise ValueError("witness paths repeat an edge or violate isomorphism adjacency")
        seen.add(key)
        skeleton[lp[0]].append(lp[-1])
        skeleton[lp[-1]].append(lp[0])
        if len(lp) == 2 and len(rp) == 2:
            weight = problem.scoring.edge_weight(left, lp[0], lp[-1], right, rp[0], rp[-1])
            if weight is None:
                raise ValueError("incompatible mapped edges in witness paths")
            contribution = _finite(weight)
        else:
            if penalty == float("inf"):
                raise ValueError("infinite distance penalty forbids skipped vertices")
            contribution = _finite(-penalty * (len(lp) + len(rp) - 4))
        contributions.append((key, contribution))
    if mapping:
        reached, pending = set(), [next(iter(mapping))]
        while pending:
            u = pending.pop()
            if u not in reached:
                reached.add(u)
                pending.extend(skeleton[u])
        if len(reached) != len(mapping):
            raise ValueError("witness paths do not connect its mapped vertices")
    score = 0.0
    for u, v in indexed:
        weight = problem.scoring.node_weight(left, u, right, v)
        if weight is None:
            raise ValueError("incompatible mapped nodes in witness")
        score = _finite(score + _finite(weight))
    # Preserve the independent reference's summation order, including when
    # callers reorder or reverse their otherwise equivalent path witnesses.
    for _, contribution in sorted(contributions):
        score = _finite(score + contribution)
    return score


def _check_rooted_mapping(problem, left, right, pairs):
    if problem.roots is None or not pairs:
        return
    if problem.root_to_root:
        if problem.roots not in pairs:
            raise ValueError("witness does not map the supplied roots together")
        return
    def intervals(tree, root):
        adjacency = [[] for _ in range(tree.n)]
        for u, v, _ in tree.edges:
            adjacency[u].append(v)
            adjacency[v].append(u)
        begin, end = [0] * tree.n, [0] * tree.n
        stack, clock = [(root, -1, False)], 0
        while stack:
            u, parent, exiting = stack.pop()
            if exiting:
                end[u] = clock
            else:
                begin[u] = clock
                clock += 1
                stack.append((u, parent, True))
                stack.extend((v, u, False) for v in adjacency[u] if v != parent)
        return begin, end
    lb, le = intervals(left, problem.roots[0])
    rb, re = intervals(right, problem.roots[1])
    u, v = min(pairs, key=lambda pair: lb[pair[0]])
    if any(not (lb[u] <= lb[x] < le[u] and rb[v] <= rb[y] < re[v]) for x, y in pairs):
        raise ValueError("witness has no common highest pair in the supplied root orientations")


def _rescore(problem, witness, penalty):
    left, right = problem.references()
    li = {node: i for i, node in enumerate(problem.left[0])}
    ri = {node: i for i, node in enumerate(problem.right[0])}
    pairs = witness.node_pairs if isinstance(witness, CommonSubtreeResult) else tuple(witness)
    try:
        indexed = reference._canonical_pairs((li[u], ri[v]) for u, v in pairs)
    except KeyError as ex:
        raise ValueError("witness contains a node outside its input tree") from ex
    _check_rooted_mapping(problem, left, right, indexed)
    if isinstance(witness, CommonSubtreeResult):
        return _score_path_witness(problem, left, right, indexed, witness.edge_paths, li, ri, penalty)
    if penalty is None:
        score = reference.score_subtree_isomorphism_witness(left, right, indexed, problem.scoring)
    else:
        score = reference.score_embedding_witness(left, right, indexed, problem.scoring, penalty)
    return score


def score_common_subtree_isomorphism(tree1, tree2, witness, *, node_label=None, edge_label=None, node_weight=1.0, edge_weight=1.0,
                                    roots=None, root_to_root=False):
    """Independently validate and rescore an original-node 2016 witness.

    Result objects validate their supplied paths directly. Bare node-pair
    iterables use the separate reference validator.
    """
    return _rescore(_Problem(tree1, tree2, node_label, edge_label, node_weight, edge_weight,
                            roots=roots, root_to_root=root_to_root), witness, None)


def score_common_subtree_embedding(tree1, tree2, witness, *, skip_vertex_penalty=0.0, node_label=None, edge_label=None, node_weight=1.0, edge_weight=1.0,
                                  roots=None, root_to_root=False):
    """Independently validate/rescore original-node paths using the 2018 rule.

    Result objects check original edges, simple paths, disjoint interiors and
    the connected common skeleton without enumerating every mapped pair.
    Bare node-pair iterables retain the small reference path/skeleton validator.
    """
    penalty = _distance_penalty(skip_vertex_penalty)
    return _rescore(_Problem(tree1, tree2, node_label, edge_label, node_weight, edge_weight,
                            roots=roots, root_to_root=root_to_root), witness, penalty)


__all__ = ["CommonSubtreeResult", "available_unordered_backends", "maximum_common_subtree_isomorphism",
           "largest_weight_common_subtree_embedding_with_distance_penalty", "score_common_subtree_isomorphism", "score_common_subtree_embedding"]
