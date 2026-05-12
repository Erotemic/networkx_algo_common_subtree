//! Labeled tree algorithms.
//!
//! This module implements graph-only tree recurrences for maximum common subtree
//! isomorphism, abbreviated **MCSI** in the 2016 paper context, and an
//! experimental reference version of the 2018 distance-penalized common subtree
//! embedding recurrence. The algorithms operate on ordinary labeled trees and
//! compose maximum-weight child matchings.

use std::collections::{HashMap, VecDeque};

use crate::matching::max_weight_bipartite_matching;
use crate::Weight;

const EPS: Weight = 1.0e-9;

/// Node index in a [`LabeledTree`].
pub type NodeId = usize;

/// Neighbor reference in an undirected labeled tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct EdgeRef {
    pub to: NodeId,
    pub label: i64,
}

/// A compact undirected labeled tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabeledTree {
    node_labels: Vec<i64>,
    adj: Vec<Vec<EdgeRef>>,
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
        for &(u, v, label) in edges {
            if u >= n || v >= n {
                return Err(format!("edge ({u}, {v}) is out of bounds for {n} nodes"));
            }
            if u == v {
                return Err(format!("self-loop at node {u} is not a tree edge"));
            }
            adj[u].push(EdgeRef { to: v, label });
            adj[v].push(EdgeRef { to: u, label });
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

        Ok(Self { node_labels, adj })
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

    /// Adjacent edges of a node.
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
}

/// Scoring / compatibility hook for labeled tree algorithms.
pub trait Scoring {
    /// Weight for mapping a node pair. `None` means incompatible.
    fn node_weight(&self, left: &LabeledTree, u: NodeId, right: &LabeledTree, v: NodeId)
        -> Option<Weight>;

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
}

/// Common subtree result.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CommonSubtree {
    /// Objective value.
    pub weight: Weight,
    /// Node mapping pairs `(left_node, right_node)`.
    pub node_pairs: Vec<(NodeId, NodeId)>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct State {
    u: NodeId,
    parent_u: Option<NodeId>,
    v: NodeId,
    parent_v: Option<NodeId>,
}

struct RootedSolver<'a, S: Scoring> {
    left: &'a LabeledTree,
    right: &'a LabeledTree,
    scoring: &'a S,
    iso_memo: HashMap<State, Option<CommonSubtree>>,
    embedding_memo: HashMap<State, Option<CommonSubtree>>,
    skip_vertex_penalty: Weight,
}

impl<'a, S: Scoring> RootedSolver<'a, S> {
    fn new(left: &'a LabeledTree, right: &'a LabeledTree, scoring: &'a S) -> Self {
        Self {
            left,
            right,
            scoring,
            iso_memo: HashMap::new(),
            embedding_memo: HashMap::new(),
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
            iso_memo: HashMap::new(),
            embedding_memo: HashMap::new(),
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

    fn rooted_isomorphism(&mut self, state: State) -> Option<CommonSubtree> {
        if let Some(found) = self.iso_memo.get(&state) {
            return found.clone();
        }

        let result = self.compute_rooted_isomorphism(state);
        self.iso_memo.insert(state, result.clone());
        result
    }

    fn compute_rooted_isomorphism(&mut self, state: State) -> Option<CommonSubtree> {
        let root_weight = self
            .scoring
            .node_weight(self.left, state.u, self.right, state.v)?;
        let left_children = Self::child_edges(self.left, state.u, state.parent_u);
        let right_children = Self::child_edges(self.right, state.v, state.parent_v);

        let mut matrix = vec![vec![None; right_children.len()]; left_children.len()];
        let mut child_results = vec![vec![None; right_children.len()]; left_children.len()];

        for (i, left_edge) in left_children.iter().enumerate() {
            for (j, right_edge) in right_children.iter().enumerate() {
                if let Some(edge_weight) = self.scoring.edge_weight(
                    self.left,
                    state.u,
                    left_edge.to,
                    self.right,
                    state.v,
                    right_edge.to,
                ) {
                    let child_state = State {
                        u: left_edge.to,
                        parent_u: Some(state.u),
                        v: right_edge.to,
                        parent_v: Some(state.v),
                    };
                    if let Some(child) = self.rooted_isomorphism(child_state) {
                        let value = edge_weight + child.weight;
                        if value > EPS {
                            matrix[i][j] = Some(value);
                            child_results[i][j] = Some(child);
                        }
                    }
                }
            }
        }

        let matching = max_weight_bipartite_matching(&matrix);
        let mut node_pairs = vec![(state.u, state.v)];
        for (i, j) in matching.pairs {
            if let Some(child) = child_results[i][j].take() {
                node_pairs.extend(child.node_pairs);
            }
        }
        node_pairs.sort_unstable();
        node_pairs.dedup();

        Some(CommonSubtree {
            weight: root_weight + matching.weight,
            node_pairs,
        })
    }

    fn rooted_embedding(&mut self, state: State) -> Option<CommonSubtree> {
        if let Some(found) = self.embedding_memo.get(&state) {
            return found.clone();
        }

        let mut best = self.compute_rooted_embedding_with_roots_mapped(state);

        for left_edge in Self::child_edges(self.left, state.u, state.parent_u) {
            let child_state = State {
                u: left_edge.to,
                parent_u: Some(state.u),
                v: state.v,
                parent_v: state.parent_v,
            };
            if let Some(mut candidate) = self.rooted_embedding(child_state) {
                candidate.weight -= self.skip_vertex_penalty;
                Self::keep_better(&mut best, candidate);
            }
        }

        for right_edge in Self::child_edges(self.right, state.v, state.parent_v) {
            let child_state = State {
                u: state.u,
                parent_u: state.parent_u,
                v: right_edge.to,
                parent_v: Some(state.v),
            };
            if let Some(mut candidate) = self.rooted_embedding(child_state) {
                candidate.weight -= self.skip_vertex_penalty;
                Self::keep_better(&mut best, candidate);
            }
        }

        if best.as_ref().map_or(false, |result| result.weight <= EPS) {
            best = None;
        }
        self.embedding_memo.insert(state, best.clone());
        best
    }

    fn compute_rooted_embedding_with_roots_mapped(&mut self, state: State) -> Option<CommonSubtree> {
        let root_weight = self
            .scoring
            .node_weight(self.left, state.u, self.right, state.v)?;
        let left_children = Self::child_edges(self.left, state.u, state.parent_u);
        let right_children = Self::child_edges(self.right, state.v, state.parent_v);

        let mut matrix = vec![vec![None; right_children.len()]; left_children.len()];
        let mut child_results = vec![vec![None; right_children.len()]; left_children.len()];

        for (i, left_edge) in left_children.iter().enumerate() {
            for (j, right_edge) in right_children.iter().enumerate() {
                if let Some(edge_weight) = self.scoring.edge_weight(
                    self.left,
                    state.u,
                    left_edge.to,
                    self.right,
                    state.v,
                    right_edge.to,
                ) {
                    let child_state = State {
                        u: left_edge.to,
                        parent_u: Some(state.u),
                        v: right_edge.to,
                        parent_v: Some(state.v),
                    };
                    if let Some(child) = self.rooted_embedding(child_state) {
                        let value = edge_weight + child.weight;
                        if value > EPS {
                            matrix[i][j] = Some(value);
                            child_results[i][j] = Some(child);
                        }
                    }
                }
            }
        }

        let matching = max_weight_bipartite_matching(&matrix);
        let mut node_pairs = vec![(state.u, state.v)];
        for (i, j) in matching.pairs {
            if let Some(child) = child_results[i][j].take() {
                node_pairs.extend(child.node_pairs);
            }
        }
        node_pairs.sort_unstable();
        node_pairs.dedup();

        Some(CommonSubtree {
            weight: root_weight + matching.weight,
            node_pairs,
        })
    }

    fn keep_better(best: &mut Option<CommonSubtree>, candidate: CommonSubtree) {
        if candidate.weight <= EPS {
            return;
        }
        match best {
            None => *best = Some(candidate),
            Some(current) => {
                if candidate.weight > current.weight + EPS
                    || ((candidate.weight - current.weight).abs() <= EPS
                        && candidate.node_pairs < current.node_pairs)
                {
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
/// proper connected subtree of either input.
pub fn maximum_common_subtree_isomorphism<S: Scoring>(
    left: &LabeledTree,
    right: &LabeledTree,
    scoring: &S,
) -> CommonSubtree {
    if left.is_empty() || right.is_empty() {
        return CommonSubtree::default();
    }

    let mut solver = RootedSolver::new(left, right, scoring);
    let mut best = None;
    for u in 0..left.len() {
        for v in 0..right.len() {
            let state = State {
                u,
                parent_u: None,
                v,
                parent_v: None,
            };
            if let Some(candidate) = solver.rooted_isomorphism(state) {
                RootedSolver::<S>::keep_better(&mut best, candidate);
            }
        }
    }
    best.unwrap_or_default()
}

/// Experimental distance-penalized common subtree embedding between two labeled
/// trees.
///
/// This prototype is intentionally conservative and test-driven. It uses the
/// same rooted child-matching core as [`maximum_common_subtree_isomorphism`], but
/// each rooted state may skip a vertex in either input at `skip_vertex_penalty`
/// cost before mapping another compatible root pair. This captures the core
/// distance-penalized tree-embedding recurrence described in the 2018 paper.
pub fn largest_weight_common_subtree_embedding_with_distance_penalty<S: Scoring>(
    left: &LabeledTree,
    right: &LabeledTree,
    scoring: &S,
    skip_vertex_penalty: Weight,
) -> CommonSubtree {
    if left.is_empty() || right.is_empty() {
        return CommonSubtree::default();
    }

    let mut solver = RootedSolver::with_skip_penalty(left, right, scoring, skip_vertex_penalty);
    let mut best = None;
    for u in 0..left.len() {
        for v in 0..right.len() {
            let state = State {
                u,
                parent_u: None,
                v,
                parent_v: None,
            };
            if let Some(candidate) = solver.rooted_embedding(state) {
                RootedSolver::<S>::keep_better(&mut best, candidate);
            }
        }
    }
    best.unwrap_or_default()
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
        let left = LabeledTree::new(vec![1, 2, 3, 9], &[(0, 1, 7), (1, 2, 7), (1, 3, 8)])
            .unwrap();
        let right = LabeledTree::new(vec![5, 1, 2, 3], &[(0, 1, 8), (1, 2, 7), (2, 3, 7)])
            .unwrap();
        let result = maximum_common_subtree_isomorphism(&left, &right, &ExactLabelScoring::default());
        assert_eq!(result.weight, 5.0);
        assert_eq!(result.node_pairs, vec![(0, 1), (1, 2), (2, 3)]);
    }
}
