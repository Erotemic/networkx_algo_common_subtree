use std::collections::{HashMap, HashSet, VecDeque};

use common_subtree_algorithms::{
    largest_weight_common_subtree_embedding_with_distance_penalty,
    maximum_common_subtree_isomorphism, ExactLabelScoring, LabeledTree,
};

const EPS: f64 = 1.0e-9;

fn assert_close(found: f64, expected: f64) {
    assert!(
        (found - expected).abs() <= EPS,
        "found {found}, expected {expected}"
    );
}

fn normalized_edge(u: usize, v: usize) -> (usize, usize) {
    if u < v { (u, v) } else { (v, u) }
}

fn path_between(tree: &LabeledTree, start: usize, stop: usize) -> Vec<usize> {
    if start == stop {
        return vec![start];
    }
    let mut parent = vec![None; tree.len()];
    let mut seen = vec![false; tree.len()];
    let mut queue = VecDeque::from([start]);
    seen[start] = true;
    while let Some(u) = queue.pop_front() {
        for edge in tree.neighbors(u) {
            if !seen[edge.to] {
                seen[edge.to] = true;
                parent[edge.to] = Some(u);
                if edge.to == stop {
                    queue.clear();
                    break;
                }
                queue.push_back(edge.to);
            }
        }
    }
    assert!(seen[stop], "tree constructor should ensure connectivity");
    let mut rev = vec![stop];
    while *rev.last().unwrap() != start {
        let current = *rev.last().unwrap();
        rev.push(parent[current].unwrap());
    }
    rev.reverse();
    rev
}

fn embedding_skeleton_edges(tree: &LabeledTree, selected_nodes: &[usize]) -> Vec<(usize, usize)> {
    let selected: HashSet<usize> = selected_nodes.iter().copied().collect();
    let mut out = Vec::new();
    for (i, &u) in selected_nodes.iter().enumerate() {
        for &v in &selected_nodes[(i + 1)..] {
            let path = path_between(tree, u, v);
            if path[1..path.len() - 1].iter().all(|node| !selected.contains(node)) {
                out.push(normalized_edge(u, v));
            }
        }
    }
    out.sort_unstable();
    assert_eq!(out.len(), selected_nodes.len().saturating_sub(1));
    out
}

fn score_embedding_witness(
    left: &LabeledTree,
    right: &LabeledTree,
    scoring: &ExactLabelScoring,
    node_pairs: &[(usize, usize)],
    skip_vertex_penalty: f64,
) -> f64 {
    if node_pairs.is_empty() {
        return 0.0;
    }
    let mut left_to_right = HashMap::new();
    let mut seen_right = HashSet::new();
    for &(u, v) in node_pairs {
        assert!(left_to_right.insert(u, v).is_none(), "left node {u} appears twice");
        assert!(seen_right.insert(v), "right node {v} appears twice");
        assert_eq!(left.node_label(u), right.node_label(v));
    }

    let mut left_nodes: Vec<usize> = left_to_right.keys().copied().collect();
    left_nodes.sort_unstable();
    let mut right_nodes: Vec<usize> = left_to_right.values().copied().collect();
    right_nodes.sort_unstable();

    let mut weight = node_pairs.len() as f64 * scoring.node_match_weight;
    let left_skeleton = embedding_skeleton_edges(left, &left_nodes);
    let right_skeleton: HashSet<(usize, usize)> = embedding_skeleton_edges(right, &right_nodes)
        .into_iter()
        .map(|(u, v)| normalized_edge(u, v))
        .collect();
    let mapped_skeleton: HashSet<(usize, usize)> = left_skeleton
        .iter()
        .map(|&(u, u2)| normalized_edge(left_to_right[&u], left_to_right[&u2]))
        .collect();
    assert_eq!(mapped_skeleton, right_skeleton, "witness does not preserve embedding skeletons");

    for &(u, u2) in &left_skeleton {
        let v = left_to_right[&u];
        let v2 = left_to_right[&u2];
        let left_path = path_between(left, u, u2);
        let right_path = path_between(right, v, v2);
        let left_next = left_path[1];
        let right_next = right_path[1];
        assert_eq!(left.edge_label(u, left_next), right.edge_label(v, right_next));
        let skipped = (left_path.len() - 2 + right_path.len() - 2) as f64;
        weight += scoring.edge_match_weight - skip_vertex_penalty * skipped;
    }
    weight
}

#[test]
fn embedding_matches_isomorphism_on_identical_inputs() {
    let tree = LabeledTree::new(
        vec![0, 1, 2, 3],
        &[(0, 1, 5), (1, 2, 6), (1, 3, 7)],
    )
    .unwrap();
    let scoring = ExactLabelScoring::default();
    let iso = maximum_common_subtree_isomorphism(&tree, &tree, &scoring);
    let emb = largest_weight_common_subtree_embedding_with_distance_penalty(&tree, &tree, &scoring, 0.5);
    assert_close(emb.weight, iso.weight);
    assert_eq!(emb.node_pairs, iso.node_pairs);
}

#[test]
fn embedding_can_skip_vertices_in_the_right_tree() {
    let left = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap();
    let right = LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let iso = maximum_common_subtree_isomorphism(&left, &right, &scoring);
    let emb = largest_weight_common_subtree_embedding_with_distance_penalty(&left, &right, &scoring, 0.25);
    assert_eq!(iso.weight, 3.0);
    assert_close(emb.weight, 4.75);
    assert_eq!(emb.node_pairs, vec![(0, 0), (1, 2), (2, 3)]);
}

#[test]
fn embedding_can_skip_vertices_in_the_left_tree() {
    let left = LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap();
    let right = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let emb = largest_weight_common_subtree_embedding_with_distance_penalty(&left, &right, &scoring, 0.25);
    assert_close(emb.weight, 4.75);
    assert_eq!(emb.node_pairs, vec![(0, 0), (2, 1), (3, 2)]);
}

#[test]
fn embedding_high_penalty_avoids_unnecessary_skips() {
    let left = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap();
    let right = LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let iso = maximum_common_subtree_isomorphism(&left, &right, &scoring);
    let emb = largest_weight_common_subtree_embedding_with_distance_penalty(&left, &right, &scoring, 10.0);
    assert_close(emb.weight, iso.weight);
    assert_eq!(emb.node_pairs, iso.node_pairs);
}

#[test]
fn embedding_zero_penalty_crosses_long_paths() {
    let left = LabeledTree::new(vec![1, 2], &[(0, 1, 4)]).unwrap();
    let right = LabeledTree::new(vec![1, 9, 8, 2], &[(0, 1, 4), (1, 2, 4), (2, 3, 4)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let iso = maximum_common_subtree_isomorphism(&left, &right, &scoring);
    let emb = largest_weight_common_subtree_embedding_with_distance_penalty(&left, &right, &scoring, 0.0);
    assert_eq!(iso.weight, 1.0);
    assert_eq!(emb.weight, 3.0);
    assert_eq!(emb.node_pairs, vec![(0, 0), (1, 3)]);
}

#[test]
fn embedding_weight_is_symmetric_under_input_order() {
    let left = LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap();
    let right = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let a = largest_weight_common_subtree_embedding_with_distance_penalty(&left, &right, &scoring, 0.25);
    let b = largest_weight_common_subtree_embedding_with_distance_penalty(&right, &left, &scoring, 0.25);
    assert_close(a.weight, b.weight);
}

#[test]
fn embedding_regression_witnesses_rescore_to_reported_weights() {
    let scoring = ExactLabelScoring::default();
    let cases = vec![
        (
            LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap(),
            LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap(),
            0.25,
        ),
        (
            LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap(),
            LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap(),
            0.25,
        ),
        (
            LabeledTree::new(vec![1, 2], &[(0, 1, 4)]).unwrap(),
            LabeledTree::new(vec![1, 9, 8, 2], &[(0, 1, 4), (1, 2, 4), (2, 3, 4)]).unwrap(),
            0.0,
        ),
    ];

    for (left, right, penalty) in cases {
        let result = largest_weight_common_subtree_embedding_with_distance_penalty(
            &left,
            &right,
            &scoring,
            penalty,
        );
        let witness_weight = score_embedding_witness(&left, &right, &scoring, &result.node_pairs, penalty);
        assert_close(witness_weight, result.weight);
    }
}

#[test]
fn embedding_score_is_monotone_in_skip_penalty() {
    let left = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap();
    let right = LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let mut previous = f64::INFINITY;
    for penalty in [0.0, 0.25, 1.0, 10.0] {
        let result = largest_weight_common_subtree_embedding_with_distance_penalty(
            &left,
            &right,
            &scoring,
            penalty,
        );
        assert!(result.weight <= previous + EPS);
        previous = result.weight;
    }
}
