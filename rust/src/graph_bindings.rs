//! Python boundaries for the existing graph algorithms and exact matching.
use common_subtree_algorithms::{self as algorithms, ExactLabelScoring, LabeledTree, Scoring};
use pyo3::exceptions::{PyOverflowError, PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use std::panic::{catch_unwind, AssertUnwindSafe};

type Matrix = Vec<Vec<Option<f64>>>;
type Edges = Vec<(usize, usize, i64)>;
type Paths = Vec<(Vec<usize>, Vec<usize>)>;
type GraphResult = (f64, Vec<(usize, usize)>, Paths);

struct TableScoring {
    nodes: Option<Matrix>,
    edges: Option<Matrix>,
    default: ExactLabelScoring,
}

impl Scoring for TableScoring {
    fn node_weight(
        &self,
        left: &LabeledTree,
        u: usize,
        right: &LabeledTree,
        v: usize,
    ) -> Option<f64> {
        match &self.nodes {
            Some(weights) => weights[u][v],
            None => self.default.node_weight(left, u, right, v),
        }
    }
    fn edge_weight(
        &self,
        left: &LabeledTree,
        u: usize,
        uc: usize,
        right: &LabeledTree,
        v: usize,
        vc: usize,
    ) -> Option<f64> {
        match &self.edges {
            Some(weights) => {
                let a = left.neighbors(u).iter().find(|edge| edge.to == uc)?;
                let b = right.neighbors(v).iter().find(|edge| edge.to == vc)?;
                weights[a.index][b.index]
            }
            None => self.default.edge_weight(left, u, uc, right, v, vc),
        }
    }

    fn branch_weight(
        &self,
        left: &LabeledTree,
        u: usize,
        left_edge: algorithms::EdgeRef,
        right: &LabeledTree,
        v: usize,
        right_edge: algorithms::EdgeRef,
    ) -> Option<f64> {
        match &self.edges {
            Some(weights) => weights[left_edge.index][right_edge.index],
            None => self
                .default
                .branch_weight(left, u, left_edge, right, v, right_edge),
        }
    }
}

fn finite(value: f64) -> PyResult<()> {
    if value.is_finite() {
        Ok(())
    } else {
        Err(PyValueError::new_err("weights must be finite"))
    }
}

fn validate_matrix(weights: &Matrix, rows: usize, columns: usize) -> PyResult<()> {
    if weights.len() != rows || weights.iter().any(|row| row.len() != columns) {
        return Err(PyValueError::new_err(
            "weight matrix shape does not match the input vertices or edges",
        ));
    }
    for value in weights.iter().flatten().flatten() {
        finite(*value)?;
    }
    Ok(())
}

fn checked_call<T>(call: impl FnOnce() -> T) -> PyResult<T> {
    catch_unwind(AssertUnwindSafe(call)).map_err(|payload| {
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or("Rust graph solver failed");
        if message.contains("finite") || message.contains("overflow") {
            PyValueError::new_err(message.to_string())
        } else {
            PyRuntimeError::new_err(message.to_string())
        }
    })
}

/// Compress the selected hull in linear time, retaining every skipped vertex.
fn skeleton_paths(
    tree: &LabeledTree,
    selected: &[bool],
) -> PyResult<FxHashMap<(usize, usize), Vec<usize>>> {
    let mut active = vec![true; tree.len()];
    let mut degrees: Vec<usize> = (0..tree.len()).map(|u| tree.neighbors(u).len()).collect();
    let mut queue: VecDeque<usize> = (0..tree.len())
        .filter(|&u| !selected[u] && degrees[u] <= 1)
        .collect();
    while let Some(u) = queue.pop_front() {
        if !active[u] {
            continue;
        }
        active[u] = false;
        for edge in tree.neighbors(u) {
            if active[edge.to] {
                degrees[edge.to] -= 1;
                if !selected[edge.to] && degrees[edge.to] <= 1 {
                    queue.push_back(edge.to);
                }
            }
        }
    }
    let mut paths = FxHashMap::default();
    for u in 0..tree.len() {
        if !selected[u] {
            continue;
        }
        for edge in tree.neighbors(u) {
            if !active[edge.to] {
                continue;
            }
            let mut path = vec![u, edge.to];
            let mut previous = u;
            let mut current = edge.to;
            while !selected[current] {
                if degrees[current] != 2 {
                    return Err(PyRuntimeError::new_err(
                        "solver witness omits a branch vertex",
                    ));
                }
                let next = tree
                    .neighbors(current)
                    .iter()
                    .find(|e| active[e.to] && e.to != previous)
                    .ok_or_else(|| PyRuntimeError::new_err("solver witness path is incomplete"))?
                    .to;
                previous = current;
                current = next;
                path.push(current);
            }
            if u < current {
                paths.insert((u, current), path);
            }
        }
    }
    Ok(paths)
}

fn witness_paths(
    left: &LabeledTree,
    right: &LabeledTree,
    pairs: &[(usize, usize)],
) -> PyResult<Paths> {
    if pairs.len() <= 1 {
        return Ok(Vec::new());
    }
    let mut left_selected = vec![false; left.len()];
    let mut right_selected = vec![false; right.len()];
    let mapping: FxHashMap<usize, usize> = pairs.iter().copied().collect();
    for &(u, v) in pairs {
        left_selected[u] = true;
        right_selected[v] = true;
    }
    let left_paths = skeleton_paths(left, &left_selected)?;
    let right_paths = skeleton_paths(right, &right_selected)?;
    if left_paths.len() + 1 != pairs.len() || right_paths.len() != left_paths.len() {
        return Err(PyRuntimeError::new_err(
            "solver witness is not a common tree skeleton",
        ));
    }
    let mut keys: Vec<_> = left_paths.keys().copied().collect();
    keys.sort_unstable();
    keys.into_iter()
        .map(|(u, v)| {
            let (ru, rv) = (mapping[&u], mapping[&v]);
            let key = (ru.min(rv), ru.max(rv));
            let mut right_path = right_paths
                .get(&key)
                .ok_or_else(|| PyRuntimeError::new_err("solver witness skeletons disagree"))?
                .clone();
            if ru > rv {
                right_path.reverse();
            }
            Ok((left_paths[&(u, v)].clone(), right_path))
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn solve_graph(
    py: Python<'_>,
    left_labels: Vec<i64>,
    left_edges: Edges,
    right_labels: Vec<i64>,
    right_edges: Edges,
    nodes: Option<Matrix>,
    edges: Option<Matrix>,
    node_match_weight: f64,
    edge_match_weight: f64,
    allow_empty: bool,
    penalty: Option<f64>,
) -> PyResult<Option<GraphResult>> {
    finite(node_match_weight)?;
    finite(edge_match_weight)?;
    if let Some(p) = penalty {
        if !p.is_finite() || p < 0.0 {
            return Err(PyValueError::new_err(
                "skip vertex penalty must be finite and nonnegative",
            ));
        }
    }
    let left = LabeledTree::new(left_labels, &left_edges).map_err(PyValueError::new_err)?;
    let right = LabeledTree::new(right_labels, &right_edges).map_err(PyValueError::new_err)?;
    if let Some(weights) = &nodes {
        validate_matrix(weights, left.len(), right.len())?;
    }
    if let Some(weights) = &edges {
        validate_matrix(weights, left_edges.len(), right_edges.len())?;
    }
    let scoring = TableScoring {
        nodes,
        edges,
        default: ExactLabelScoring {
            node_match_weight,
            edge_match_weight,
        },
    };
    py.allow_threads(|| {
        let result = checked_call(|| match (penalty, allow_empty) {
            (None, true) => Some(algorithms::maximum_common_subtree_isomorphism(
                &left, &right, &scoring,
            )),
            (None, false) => {
                algorithms::maximum_nonempty_common_subtree_isomorphism(&left, &right, &scoring)
            }
            (Some(p), true) => Some(
                algorithms::largest_weight_common_subtree_embedding_with_distance_penalty(
                    &left, &right, &scoring, p,
                ),
            ),
            (Some(p), false) => {
                algorithms::largest_weight_nonempty_common_subtree_embedding_with_distance_penalty(
                    &left, &right, &scoring, p,
                )
            }
        })?;
        result
            .map(|r| {
                let paths = witness_paths(&left, &right, &r.node_pairs)?;
                Ok((r.weight, r.node_pairs, paths))
            })
            .transpose()
    })
}

#[pyfunction(signature=(left_labels,left_edges,right_labels,right_edges,node_weights=None,edge_weights=None,node_match_weight=1.0,edge_match_weight=1.0,allow_empty=true))]
fn maximum_common_subtree_isomorphism(
    py: Python<'_>,
    left_labels: Vec<i64>,
    left_edges: Edges,
    right_labels: Vec<i64>,
    right_edges: Edges,
    node_weights: Option<Matrix>,
    edge_weights: Option<Matrix>,
    node_match_weight: f64,
    edge_match_weight: f64,
    allow_empty: bool,
) -> PyResult<Option<GraphResult>> {
    solve_graph(
        py,
        left_labels,
        left_edges,
        right_labels,
        right_edges,
        node_weights,
        edge_weights,
        node_match_weight,
        edge_match_weight,
        allow_empty,
        None,
    )
}

#[pyfunction(signature=(left_labels,left_edges,right_labels,right_edges,skip_vertex_penalty=0.0,node_weights=None,edge_weights=None,node_match_weight=1.0,edge_match_weight=1.0,allow_empty=true))]
fn largest_weight_common_subtree_embedding_with_distance_penalty(
    py: Python<'_>,
    left_labels: Vec<i64>,
    left_edges: Edges,
    right_labels: Vec<i64>,
    right_edges: Edges,
    skip_vertex_penalty: f64,
    node_weights: Option<Matrix>,
    edge_weights: Option<Matrix>,
    node_match_weight: f64,
    edge_match_weight: f64,
    allow_empty: bool,
) -> PyResult<Option<GraphResult>> {
    solve_graph(
        py,
        left_labels,
        left_edges,
        right_labels,
        right_edges,
        node_weights,
        edge_weights,
        node_match_weight,
        edge_match_weight,
        allow_empty,
        Some(skip_vertex_penalty),
    )
}

#[pyfunction]
fn min_cost_assignment(
    py: Python<'_>,
    cost: Vec<Vec<i64>>,
) -> PyResult<(Vec<usize>, i128, Vec<i128>, Vec<i128>)> {
    use verified_assignment_core::{min_cost_assignment, AssignmentError};
    match py.allow_threads(|| min_cost_assignment(&cost)) {
        Ok(result) => Ok((
            result.column_for_row,
            result.cost,
            result.row_potential,
            result.column_potential,
        )),
        Err(AssignmentError::NonSquare) => Err(PyValueError::new_err(
            "assignment cost matrix must be square",
        )),
        Err(AssignmentError::TooLarge) => Err(PyOverflowError::new_err(
            "assignment dimension exceeds u32 capacity",
        )),
        Err(AssignmentError::ArithmeticOverflow) => {
            Err(PyOverflowError::new_err("assignment arithmetic overflow"))
        }
        Err(AssignmentError::InvariantViolation) => {
            Err(PyRuntimeError::new_err("assignment invariant failed"))
        }
    }
}

#[pyfunction]
fn max_weight_partial_matching(
    py: Python<'_>,
    weights: Vec<Vec<Option<i64>>>,
) -> PyResult<(Vec<(usize, usize)>, i128)> {
    use verified_assignment_core::matching::{max_weight_partial_matching, MatchingError};
    match py.allow_threads(|| max_weight_partial_matching(&weights)) {
        Ok(result) => Ok((
            result
                .pairs
                .into_iter()
                .map(|p| (p.left, p.right))
                .collect(),
            result.weight,
        )),
        Err(MatchingError::NonRectangular) => Err(PyValueError::new_err(
            "matching weights must be rectangular",
        )),
        Err(MatchingError::TooLarge) => Err(PyOverflowError::new_err(
            "matching dimension exceeds u32 capacity",
        )),
        Err(MatchingError::ArithmeticOverflow) => {
            Err(PyOverflowError::new_err("matching arithmetic overflow"))
        }
        Err(MatchingError::AssignmentFailure) => {
            Err(PyRuntimeError::new_err("assignment solver failed"))
        }
    }
}

pub fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_function(wrap_pyfunction!(
        maximum_common_subtree_isomorphism,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        largest_weight_common_subtree_embedding_with_distance_penalty,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(min_cost_assignment, module)?)?;
    module.add_function(wrap_pyfunction!(max_weight_partial_matching, module)?)?;
    Ok(())
}
