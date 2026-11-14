//! Labeled tree algorithms.
//!
//! This module implements graph-only tree recurrences for maximum common subtree
//! isomorphism, abbreviated **MCSI** in the 2016 paper context, and an
//! the 2018 distance-penalized common subtree embedding recurrence. The algorithms
//! operate on ordinary labeled trees and
//! compose maximum-weight child matchings.

use std::collections::VecDeque;
use std::num::NonZeroUsize;

use crate::matching::{
    max_weight_bipartite_matching, max_weight_bipartite_matching_with_right_deletions,
    WeightedMatching,
};
use crate::Weight;

fn finite_weight(weight: Weight) -> Weight {
    assert!(
        weight.is_finite(),
        "tree scores must be finite: invalid scoring value or arithmetic overflow"
    );
    weight
}

/// Node index in a [`LabeledTree`].
pub type NodeId = usize;

/// Neighbor reference in an undirected labeled tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct EdgeRef {
    pub to: NodeId,
    pub label: i64,
    /// Original undirected edge-list index, shared by both directions.
    pub index: usize,
}

/// A compact undirected labeled tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabeledTree {
    node_labels: Vec<i64>,
    adj: Vec<Vec<EdgeRef>>,
    // Whole views precede consecutive pairs of opposite directed-edge views.
    views: Vec<(NodeId, Option<NodeId>)>,
    excluded_views: Vec<Vec<usize>>,
}

impl LabeledTree {
    /// Construct a tree from node labels and undirected labeled edges.
    ///
    /// Each edge is `(u, v, label)`. The constructor validates node bounds,
    /// connectivity, and the tree edge count invariant.
    pub fn new(node_labels: Vec<i64>, edges: &[(NodeId, NodeId, i64)]) -> Result<Self, String> {
        let n = node_labels.len();
        if n == 0 {
            if edges.is_empty() {
                return Ok(Self {
                    node_labels,
                    adj: Vec::new(),
                    views: Vec::new(),
                    excluded_views: Vec::new(),
                });
            }
            return Err("non-empty edge list for an empty tree".to_string());
        }
        if edges.len() + 1 != n {
            return Err(format!(
                "a tree with {n} nodes must have {} edges, got {}",
                n - 1,
                edges.len()
            ));
        }

        let mut adj = vec![Vec::new(); n];
        let mut views: Vec<_> = (0..n).map(|u| (u, None)).collect();
        let mut excluded_views = vec![Vec::new(); n];
        for (index, &(u, v, label)) in edges.iter().enumerate() {
            if u >= n || v >= n {
                return Err(format!("edge ({u}, {v}) is out of bounds for {n} nodes"));
            }
            if u == v {
                return Err(format!("self-loop at node {u} is not a tree edge"));
            }
            adj[u].push(EdgeRef {
                to: v,
                label,
                index,
            });
            adj[v].push(EdgeRef {
                to: u,
                label,
                index,
            });
            excluded_views[u].push(views.len());
            views.push((u, Some(v)));
            excluded_views[v].push(views.len());
            views.push((v, Some(u)));
        }

        let mut seen = vec![false; n];
        let mut queue = VecDeque::from([0usize]);
        seen[0] = true;
        while let Some(u) = queue.pop_front() {
            for edge in &adj[u] {
                if !seen[edge.to] {
                    seen[edge.to] = true;
                    queue.push_back(edge.to);
                }
            }
        }
        if seen.iter().any(|&flag| !flag) {
            return Err("input graph is disconnected".to_string());
        }

        Ok(Self {
            node_labels,
            adj,
            views,
            excluded_views,
        })
    }

    /// Number of nodes.
    pub fn len(&self) -> usize {
        self.node_labels.len()
    }

    /// Whether the tree has no nodes.
    pub fn is_empty(&self) -> bool {
        self.node_labels.is_empty()
    }

    /// Label of a node.
    pub fn node_label(&self, node: NodeId) -> i64 {
        self.node_labels[node]
    }

    /// Adjacent edges of a node, in input edge order.
    pub fn neighbors(&self, node: NodeId) -> &[EdgeRef] {
        &self.adj[node]
    }

    /// Label of the edge between two adjacent nodes.
    pub fn edge_label(&self, u: NodeId, v: NodeId) -> Option<i64> {
        self.adj[u]
            .iter()
            .find(|edge| edge.to == v)
            .map(|edge| edge.label)
    }

    // Edge, view at this node excluding the neighbor, and opposite view.
    fn neighbor_views(&self, node: NodeId) -> impl Iterator<Item = (EdgeRef, usize, usize)> + '_ {
        self.adj[node]
            .iter()
            .zip(&self.excluded_views[node])
            .map(|(&edge, &excluded)| {
                let opposite = self.len() + ((excluded - self.len()) ^ 1);
                (edge, excluded, opposite)
            })
    }
}

/// Scoring / compatibility hook for labeled tree algorithms.
///
/// Queries must be deterministic and return finite weights or `None` for
/// incompatibility. Signed weights are supported. Solvers panic when a queried
/// weight or accumulated score is nonfinite; IEEE rounding still applies.
/// Edge scores describe undirected mapped edges: reversing both endpoint
/// orders must preserve compatibility and weight.
pub trait Scoring {
    /// Weight for mapping a node pair. `None` means incompatible.
    fn node_weight(
        &self,
        left: &LabeledTree,
        u: NodeId,
        right: &LabeledTree,
        v: NodeId,
    ) -> Option<Weight>;

    /// Weight for mapping an edge pair. `None` means incompatible.
    fn edge_weight(
        &self,
        left: &LabeledTree,
        u: NodeId,
        u_child: NodeId,
        right: &LabeledTree,
        v: NodeId,
        v_child: NodeId,
    ) -> Option<Weight>;

    /// The same edge-pair score with known adjacency metadata. Overrides must
    /// agree with `edge_weight`; they can avoid looking up labels a second time.
    fn branch_weight(
        &self,
        left: &LabeledTree,
        u: NodeId,
        left_edge: EdgeRef,
        right: &LabeledTree,
        v: NodeId,
        right_edge: EdgeRef,
    ) -> Option<Weight> {
        self.edge_weight(left, u, left_edge.to, right, v, right_edge.to)
    }
}

/// Exact node-label and edge-label scoring.
#[derive(Clone, Copy, Debug)]
pub struct ExactLabelScoring {
    pub node_match_weight: Weight,
    pub edge_match_weight: Weight,
}

impl Default for ExactLabelScoring {
    fn default() -> Self {
        Self {
            node_match_weight: 1.0,
            edge_match_weight: 1.0,
        }
    }
}

impl Scoring for ExactLabelScoring {
    fn node_weight(
        &self,
        left: &LabeledTree,
        u: NodeId,
        right: &LabeledTree,
        v: NodeId,
    ) -> Option<Weight> {
        if left.node_label(u) == right.node_label(v) {
            Some(self.node_match_weight)
        } else {
            None
        }
    }

    fn edge_weight(
        &self,
        left: &LabeledTree,
        u: NodeId,
        u_child: NodeId,
        right: &LabeledTree,
        v: NodeId,
        v_child: NodeId,
    ) -> Option<Weight> {
        match (left.edge_label(u, u_child), right.edge_label(v, v_child)) {
            (Some(a), Some(b)) if a == b => Some(self.edge_match_weight),
            _ => None,
        }
    }

    fn branch_weight(
        &self,
        _left: &LabeledTree,
        _u: NodeId,
        left_edge: EdgeRef,
        _right: &LabeledTree,
        _v: NodeId,
        right_edge: EdgeRef,
    ) -> Option<Weight> {
        (left_edge.label == right_edge.label).then_some(self.edge_match_weight)
    }
}

/// Common subtree result.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CommonSubtree {
    /// Objective value.
    pub weight: Weight,
    /// Node mapping pairs `(left_node, right_node)`.
    pub node_pairs: Vec<(NodeId, NodeId)>,
}

// Memo/skip states carry constant-size choices. Rooted choices refer only to
// earlier choices, and the winning mapping is expanded once at the API boundary.
type WitnessId = NonZeroUsize;

struct WitnessNode {
    pair: (NodeId, NodeId),
    children: Vec<WitnessId>,
}

#[derive(Clone, Copy)]
struct SolverResult {
    weight: Weight,
    witness: WitnessId,
}

impl SolverResult {
    fn into_public(self, choices: &[WitnessNode]) -> CommonSubtree {
        CommonSubtree {
            weight: self.weight,
            node_pairs: reconstruct_mapping(choices, vec![self.witness]),
        }
    }
}

fn reconstruct_mapping(
    choices: &[WitnessNode],
    mut pending: Vec<WitnessId>,
) -> Vec<(NodeId, NodeId)> {
    let mut pairs = Vec::new();
    while let Some(id) = pending.pop() {
        let choice = &choices[id.get() - 1];
        pairs.push(choice.pair);
        pending.extend_from_slice(&choice.children);
    }
    pairs.sort_unstable();
    pairs
}

fn fixed_orientation(tree: &LabeledTree) -> (Vec<Option<NodeId>>, Vec<NodeId>, Vec<usize>) {
    let mut parents = vec![None; tree.len()];
    let mut order = Vec::with_capacity(tree.len());
    let mut views: Vec<_> = (0..tree.len()).collect();
    if let Some(root) = (0..tree.len()).max_by_key(|&u| tree.neighbors(u).len()) {
        let mut stack = vec![root];
        while let Some(u) = stack.pop() {
            order.push(u);
            for (edge, _, child_view) in tree.neighbor_views(u) {
                if Some(edge.to) != parents[u] {
                    parents[edge.to] = Some(u);
                    views[edge.to] = child_view;
                    stack.push(edge.to);
                }
            }
        }
    }
    (parents, order, views)
}

fn keep_two(best: &mut [Option<(usize, SolverResult)>; 2], branch: usize, candidate: SolverResult) {
    if best[0].is_none_or(|(_, current)| candidate.weight > current.weight) {
        best[1] = best[0];
        best[0] = Some((branch, candidate));
    } else if best[1].is_none_or(|(_, current)| candidate.weight > current.weight) {
        best[1] = Some((branch, candidate));
    }
}

#[derive(Clone, Copy, Debug)]
struct State {
    u: NodeId,
    parent_u: Option<NodeId>,
    view: usize,
}

// Each table fixes the left orientation and uses 3*m-2 right views.
// None is uncomputed; Some(None) is a computed incompatible state.
#[derive(Default)]
struct OrientedTable {
    stride: usize,
    entries: Vec<Option<Option<SolverResult>>>,
}

impl OrientedTable {
    fn new(left_size: usize, right: &LabeledTree) -> Self {
        let stride = right.views.len();
        let length = left_size
            .checked_mul(stride)
            .expect("oriented table dimension overflow");
        Self {
            stride,
            entries: vec![None; length],
        }
    }

    fn index(&self, state: State) -> usize {
        state.u * self.stride + state.view
    }

    fn insert(&mut self, state: State, value: Option<SolverResult>) {
        let index = self.index(state);
        self.entries[index] = Some(value);
    }

    fn get(&self, state: State) -> Option<SolverResult> {
        self.entries[self.index(state)].expect("oriented dependency was computed")
    }
}

struct RootedSolver<'a, S: Scoring> {
    left: &'a LabeledTree,
    right: &'a LabeledTree,
    scoring: &'a S,
    iso_memo: OrientedTable,
    embedding_memo: OrientedTable,
    skipped_memo: OrientedTable,
    choices: Vec<WitnessNode>,
    skip_vertex_penalty: Weight,
}

impl<'a, S: Scoring> RootedSolver<'a, S> {
    fn new(left: &'a LabeledTree, right: &'a LabeledTree, scoring: &'a S) -> Self {
        Self {
            left,
            right,
            scoring,
            iso_memo: OrientedTable::new(left.len(), right),
            embedding_memo: OrientedTable::default(),
            skipped_memo: OrientedTable::default(),
            choices: Vec::new(),
            skip_vertex_penalty: 0.0,
        }
    }

    fn with_skip_penalty(
        left: &'a LabeledTree,
        right: &'a LabeledTree,
        scoring: &'a S,
        skip_vertex_penalty: Weight,
    ) -> Self {
        Self {
            left,
            right,
            scoring,
            iso_memo: OrientedTable::default(),
            embedding_memo: OrientedTable::new(left.len(), right),
            skipped_memo: OrientedTable::new(left.len(), right),
            choices: Vec::new(),
            skip_vertex_penalty,
        }
    }

    fn child_edges(tree: &LabeledTree, node: NodeId, parent: Option<NodeId>) -> Vec<EdgeRef> {
        tree.neighbors(node)
            .iter()
            .copied()
            .filter(|edge| Some(edge.to) != parent)
            .collect()
    }

    fn retain_root(
        &mut self,
        state: State,
        weight: Weight,
        children: Vec<WitnessId>,
    ) -> SolverResult {
        self.choices.push(WitnessNode {
            pair: (state.u, self.right.views[state.view].0),
            children,
        });
        SolverResult {
            weight,
            witness: NonZeroUsize::new(self.choices.len()).expect("a retained root exists"),
        }
    }

    fn rooted_isomorphism(&mut self, state: State) -> Option<SolverResult> {
        let index = self.iso_memo.index(state);
        if let Some(found) = self.iso_memo.entries[index] {
            return found;
        }

        let result = self.compute_rooted_isomorphism(state);
        self.iso_memo.entries[index] = Some(result);
        result
    }

    fn compute_rooted_isomorphism(&mut self, state: State) -> Option<SolverResult> {
        let (v, parent_v) = self.right.views[state.view];
        let root_weight = finite_weight(
            self.scoring
                .node_weight(self.left, state.u, self.right, v)?,
        );
        let left_children = Self::child_edges(self.left, state.u, state.parent_u);
        if left_children.is_empty()
            || !self
                .right
                .neighbors(v)
                .iter()
                .any(|edge| Some(edge.to) != parent_v)
        {
            return Some(self.retain_root(state, root_weight, Vec::new()));
        }
        let family = state.parent_u.is_some() && self.right.neighbors(v).len() >= 4;
        let right_children: Vec<_> = self
            .right
            .neighbor_views(v)
            .filter(|(edge, _, _)| family || Some(edge.to) != parent_v)
            .collect();
        let mut matrix = vec![vec![None; right_children.len()]; left_children.len()];
        let mut child_results = vec![vec![None; right_children.len()]; left_children.len()];
        for (i, &left_edge) in left_children.iter().enumerate() {
            for (j, &(right_edge, _, child_view)) in right_children.iter().enumerate() {
                if let Some(edge_weight) = self
                    .scoring
                    .branch_weight(self.left, state.u, left_edge, self.right, v, right_edge)
                {
                    let edge_weight = finite_weight(edge_weight);
                    if let Some(child) = self.rooted_isomorphism(State {
                        u: left_edge.to,
                        parent_u: Some(state.u),
                        view: child_view,
                    }) {
                        let value = finite_weight(edge_weight + child.weight);
                        if value > 0.0 {
                            matrix[i][j] = Some(value);
                            child_results[i][j] = Some(child);
                        }
                    }
                }
            }
        }
        if family {
            let matchings = max_weight_bipartite_matching_with_right_deletions(&matrix);
            let whole = State { view: v, ..state };
            let full =
                self.combine_rooted_matches(whole, root_weight, &matchings.base, &child_results);
            self.iso_memo.insert(whole, Some(full));
            for ((_, excluded, _), changed) in right_children.iter().zip(&matchings.deletions) {
                let partial = State {
                    view: *excluded,
                    ..state
                };
                let result = match changed {
                    None => full,
                    Some(matching) => {
                        self.combine_rooted_matches(partial, root_weight, matching, &child_results)
                    }
                };
                self.iso_memo.insert(partial, Some(result));
            }
            return self.iso_memo.get(state);
        }
        let matching = max_weight_bipartite_matching(&matrix);
        Some(self.combine_rooted_matches(state, root_weight, &matching, &child_results))
    }

    fn combine_rooted_matches(
        &mut self,
        state: State,
        root_weight: Weight,
        matching: &WeightedMatching,
        child_results: &[Vec<Option<SolverResult>>],
    ) -> SolverResult {
        let children = matching
            .pairs
            .iter()
            .map(|&(i, j)| {
                child_results[i][j]
                    .as_ref()
                    .expect("matched branch has a witness")
                    .witness
            })
            .collect();
        self.retain_root(
            state,
            finite_weight(root_weight + matching.weight),
            children,
        )
    }

    fn continuation(&self, state: State) -> Option<SolverResult> {
        let mut best = self.embedding_memo.get(state);
        if let Some(candidate) = self.skipped_memo.get(state) {
            Self::keep_candidate(&mut best, candidate);
        }
        best
    }

    // All mapped states at u use only left children, so their tables are
    // complete before processing u. This separates matching from the same-u
    // right-skip dependencies and avoids recursive rerooting cycles.
    fn embedding_matching_family(&mut self, state: State, left_children: &[EdgeRef]) {
        let v = state.view; // This phase receives whole views, indexed by vertex.
        let root_weight = self.scoring.node_weight(self.left, state.u, self.right, v);
        let Some(root_weight) = root_weight else {
            self.embedding_memo.insert(state, None);
            for (_, excluded, _) in self.right.neighbor_views(v) {
                self.embedding_memo.insert(
                    State {
                        view: excluded,
                        ..state
                    },
                    None,
                );
            }
            return;
        };
        let root_weight = finite_weight(root_weight);
        if left_children.is_empty() || self.right.neighbors(v).is_empty() {
            let leaf = self.retain_root(state, root_weight, Vec::new());
            self.embedding_memo.insert(state, Some(leaf));
            for (_, excluded, _) in self.right.neighbor_views(v) {
                self.embedding_memo.insert(
                    State {
                        view: excluded,
                        ..state
                    },
                    Some(leaf),
                );
            }
            return;
        }
        let right_degree = self.right.neighbors(v).len();
        let mut matrix = vec![vec![None; right_degree]; left_children.len()];
        let mut child_results = vec![vec![None; right_degree]; left_children.len()];
        for (i, &left_edge) in left_children.iter().enumerate() {
            for (j, (right_edge, _, child_view)) in self.right.neighbor_views(v).enumerate() {
                let child_state = State {
                    u: left_edge.to,
                    parent_u: Some(state.u),
                    view: child_view,
                };
                let mut continuation = self.skipped_memo.get(child_state);
                if let Some(edge_weight) = self
                    .scoring
                    .branch_weight(self.left, state.u, left_edge, self.right, v, right_edge)
                {
                    let edge_weight = finite_weight(edge_weight);
                    if let Some(mut direct) = self.embedding_memo.get(child_state) {
                        direct.weight = finite_weight(direct.weight + edge_weight);
                        Self::keep_candidate(&mut continuation, direct);
                    }
                }
                if let Some(child) = continuation.filter(|child| child.weight > 0.0) {
                    matrix[i][j] = Some(child.weight);
                    child_results[i][j] = Some(child);
                }
            }
        }
        let matchings = max_weight_bipartite_matching_with_right_deletions(&matrix);
        let full = self.combine_rooted_matches(state, root_weight, &matchings.base, &child_results);
        self.embedding_memo.insert(state, Some(full));
        for (j, changed) in matchings.deletions.iter().enumerate() {
            let partial = State {
                view: self.right.excluded_views[v][j],
                ..state
            };
            let result = match changed {
                None => full,
                Some(matching) => {
                    self.combine_rooted_matches(partial, root_weight, matching, &child_results)
                }
            };
            self.embedding_memo.insert(partial, Some(result));
        }
    }

    fn store_skipped(&mut self, state: State, mut best: Option<SolverResult>) {
        if let Some(candidate) = &mut best {
            candidate.weight = finite_weight(candidate.weight - self.skip_vertex_penalty);
        }
        self.skipped_memo.insert(state, best);
    }

    fn compute_embeddings(&mut self, parents: &[Option<NodeId>], order: &[NodeId]) {
        let (right_parents, right_order, right_views) = fixed_orientation(self.right);
        let stride = self.embedding_memo.stride;
        for &u in order.iter().rev() {
            let left_children = Self::child_edges(self.left, u, parents[u]);
            for v in 0..self.right.len() {
                self.embedding_matching_family(
                    State {
                        u,
                        parent_u: parents[u],
                        view: v,
                    },
                    &left_children,
                );
            }
            // Maxima from skipping u to one left child, for every right view.
            let mut left_best = vec![None; stride];
            for child in &left_children {
                let base = child.to * stride;
                for (view, best) in left_best.iter_mut().enumerate() {
                    for candidate in [
                        self.embedding_memo.entries[base + view],
                        self.skipped_memo.entries[base + view],
                    ] {
                        if let Some(candidate) = candidate.expect("left child tables are complete")
                        {
                            Self::keep_candidate(best, candidate);
                        }
                    }
                }
            }
            // Downward right messages first, then a rerooting pass. At each
            // vertex, the best two incoming branches supply all exclusions.
            for &v in right_order.iter().rev() {
                let state = State {
                    u,
                    parent_u: parents[u],
                    view: right_views[v],
                };
                let mut best = left_best[state.view];
                for (edge, _, child_view) in self.right.neighbor_views(v) {
                    if Some(edge.to) != right_parents[v] {
                        if let Some(candidate) = self.continuation(State {
                            view: child_view,
                            ..state
                        }) {
                            Self::keep_candidate(&mut best, candidate);
                        }
                    }
                }
                self.store_skipped(state, best);
            }
            for &v in &right_order {
                let whole = State {
                    u,
                    parent_u: parents[u],
                    view: v,
                };
                let mut incoming = [None; 2];
                for (_, excluded, child_view) in self.right.neighbor_views(v) {
                    if let Some(candidate) = self.continuation(State {
                        view: child_view,
                        ..whole
                    }) {
                        keep_two(&mut incoming, excluded, candidate);
                    }
                }
                let mut best = left_best[v];
                if let Some((_, candidate)) = incoming[0] {
                    Self::keep_candidate(&mut best, candidate);
                }
                self.store_skipped(whole, best);
                for j in 0..self.right.excluded_views[v].len() {
                    let excluded = self.right.excluded_views[v][j];
                    let state = State {
                        view: excluded,
                        ..whole
                    };
                    let mut best = left_best[excluded];
                    let from_right = if incoming[0].is_some_and(|(chosen, _)| chosen == excluded) {
                        incoming[1]
                    } else {
                        incoming[0]
                    };
                    if let Some((_, candidate)) = from_right {
                        Self::keep_candidate(&mut best, candidate);
                    }
                    self.store_skipped(state, best);
                }
            }
        }
    }

    fn keep_candidate(best: &mut Option<SolverResult>, candidate: SolverResult) {
        match best {
            None => *best = Some(candidate),
            Some(current) => {
                // Iteration order is fixed. Keeping the first tie avoids
                // expanding or comparing complete intermediate witnesses.
                if candidate.weight > current.weight {
                    *current = candidate;
                }
            }
        }
    }
}

/// Compute a maximum-weight common connected subtree isomorphism between two
/// labeled trees.
///
/// This is the tree-level dynamic-programming core: choose a root pair, solve
/// child subproblems recursively, and combine child choices with a maximum-weight
/// bipartite matching. Unmatched children are allowed, so the result can be a
/// proper connected subtree of either input. The left tree is rooted once;
/// every connected selected subtree has a unique highest retained vertex in
/// this orientation. Enumerating that vertex and its arbitrary right image
/// covers all solutions without rerooting the left tree in every state.
pub fn maximum_common_subtree_isomorphism<S: Scoring>(
    left: &LabeledTree,
    right: &LabeledTree,
    scoring: &S,
) -> CommonSubtree {
    maximum_nonempty_common_subtree_isomorphism(left, right, scoring)
        .filter(|result| result.weight > 0.0)
        .unwrap_or_default()
}

/// Source-style nonempty optimum, retaining negative scores. `None` means no
/// compatible vertex mapping exists (including inputs with no vertices).
pub fn maximum_nonempty_common_subtree_isomorphism<S: Scoring>(
    left: &LabeledTree,
    right: &LabeledTree,
    scoring: &S,
) -> Option<CommonSubtree> {
    if left.is_empty() || right.is_empty() {
        return None;
    }

    let mut solver = RootedSolver::new(left, right, scoring);
    let (parents, _, _) = fixed_orientation(left);
    let mut best = None;
    for u in 0..left.len() {
        for v in 0..right.len() {
            let state = State {
                u,
                parent_u: parents[u],
                view: v,
            };
            if let Some(candidate) = solver.rooted_isomorphism(state) {
                RootedSolver::<S>::keep_candidate(&mut best, candidate);
            }
        }
    }
    best.map(|result| result.into_public(&solver.choices))
}

/// Distance-penalized common subtree embedding between two labeled
/// trees.
///
/// Implements the two state types of the 2018 paper's Lemma 5. A direct
/// edge pair contributes its edge weight only when neither path skips a vertex.
/// Otherwise the contribution is just the penalty for every skipped vertex.
/// The empty mapping is permitted with score zero. A fixed left orientation,
/// matching deletion families, rerooted skip messages and the skipped-highest
/// path case implement the paper's unrooted decomposition. Directed-edge IDs
/// locate views in constant time; no source-proved runtime claim is made.
///
/// # Panics
/// Panics if the penalty is negative or nonfinite.
pub fn largest_weight_common_subtree_embedding_with_distance_penalty<S: Scoring>(
    left: &LabeledTree,
    right: &LabeledTree,
    scoring: &S,
    skip_vertex_penalty: Weight,
) -> CommonSubtree {
    largest_weight_nonempty_common_subtree_embedding_with_distance_penalty(
        left,
        right,
        scoring,
        skip_vertex_penalty,
    )
    .filter(|result| result.weight > 0.0)
    .unwrap_or_default()
}

/// Nonempty form of the distance-penalized optimum, retaining negative scores.
/// Returns `None` when there is no compatible mapped vertex pair.
///
/// # Panics
/// Panics if the penalty is negative or nonfinite.
pub fn largest_weight_nonempty_common_subtree_embedding_with_distance_penalty<S: Scoring>(
    left: &LabeledTree,
    right: &LabeledTree,
    scoring: &S,
    skip_vertex_penalty: Weight,
) -> Option<CommonSubtree> {
    assert!(
        skip_vertex_penalty.is_finite() && skip_vertex_penalty >= 0.0,
        "skip vertex penalty must be finite and nonnegative"
    );
    if left.is_empty() || right.is_empty() {
        return None;
    }

    let (parents, order, _) = fixed_orientation(left);
    let mut solver = RootedSolver::with_skip_penalty(left, right, scoring, skip_vertex_penalty);
    solver.compute_embeddings(&parents, &order);
    let mut best = None;
    for u in 0..left.len() {
        for v in 0..right.len() {
            if let Some(candidate) = solver.embedding_memo.get(State {
                u,
                parent_u: parents[u],
                view: v,
            }) {
                RootedSolver::<S>::keep_candidate(&mut best, candidate);
            }
        }
    }
    // Lemma 10, M2: the highest left vertex is skipped inside one path.
    // Split that path across a right edge and two distinct left child branches.
    let mut joined = None;
    let mut best_weight = best.map(|candidate| candidate.weight);
    for u in 0..left.len() {
        let children = RootedSolver::<S>::child_edges(left, u, parents[u]);
        if children.len() < 2 {
            continue;
        }
        for v in 0..right.len() {
            for (_, excluded, opposite) in
                right.neighbor_views(v).filter(|(edge, _, _)| v < edge.to)
            {
                let mut first = [None; 2];
                let mut second = [None; 2];
                for child in &children {
                    let state = State {
                        u: child.to,
                        parent_u: Some(u),
                        view: excluded,
                    };
                    if let Some(candidate) = solver.continuation(state) {
                        keep_two(&mut first, child.to, candidate);
                    }
                    if let Some(candidate) = solver.continuation(State {
                        view: opposite,
                        ..state
                    }) {
                        keep_two(&mut second, child.to, candidate);
                    }
                }
                for (a, left_part) in first.into_iter().flatten() {
                    for (b, right_part) in second.into_iter().flatten() {
                        if a == b {
                            continue;
                        }
                        let weight = finite_weight(
                            finite_weight(left_part.weight + right_part.weight)
                                - skip_vertex_penalty,
                        );
                        if best_weight.is_none_or(|current| weight > current) {
                            best_weight = Some(weight);
                            joined = Some((weight, left_part.witness, right_part.witness));
                        }
                    }
                }
            }
        }
    }
    match joined {
        None => best.map(|result| result.into_public(&solver.choices)),
        Some((weight, left, right)) => Some(CommonSubtree {
            weight,
            node_pairs: reconstruct_mapping(&solver.choices, vec![left, right]),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_trees() {
        let err = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 0)]).unwrap_err();
        assert!(err.contains("must have"));
    }

    #[test]
    fn exact_common_subtree_finds_common_path() {
        let left = LabeledTree::new(vec![1, 2, 3, 9], &[(0, 1, 7), (1, 2, 7), (1, 3, 8)]).unwrap();
        let right = LabeledTree::new(vec![5, 1, 2, 3], &[(0, 1, 8), (1, 2, 7), (2, 3, 7)]).unwrap();
        let result =
            maximum_common_subtree_isomorphism(&left, &right, &ExactLabelScoring::default());
        assert_eq!(result.weight, 5.0);
        assert_eq!(result.node_pairs, vec![(0, 1), (1, 2), (2, 3)]);
    }
}
