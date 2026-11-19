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
    if u < v {
        (u, v)
    } else {
        (v, u)
    }
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

fn embedding_skeleton_edges(
    tree: &LabeledTree,
    selected_nodes: &[usize],
) -> Option<Vec<(usize, usize)>> {
    let selected: HashSet<usize> = selected_nodes.iter().copied().collect();
    let mut out = Vec::new();
    for (i, &u) in selected_nodes.iter().enumerate() {
        for &v in &selected_nodes[(i + 1)..] {
            let path = path_between(tree, u, v);
            if path[1..path.len() - 1]
                .iter()
                .all(|node| !selected.contains(node))
            {
                out.push(normalized_edge(u, v));
            }
        }
    }
    out.sort_unstable();
    if out.len() != selected_nodes.len().saturating_sub(1) {
        return None;
    }
    let mut used = HashSet::new();
    for &(u, v) in &out {
        let path = path_between(tree, u, v);
        for &node in &path[1..path.len() - 1] {
            if !used.insert(node) {
                return None;
            }
        }
    }
    Some(out)
}

fn score_embedding_witness(
    left: &LabeledTree,
    right: &LabeledTree,
    scoring: &ExactLabelScoring,
    node_pairs: &[(usize, usize)],
    skip_vertex_penalty: f64,
) -> Option<f64> {
    if node_pairs.is_empty() {
        return Some(0.0);
    }
    let mut left_to_right = HashMap::new();
    let mut seen_right = HashSet::new();
    for &(u, v) in node_pairs {
        if left_to_right.insert(u, v).is_some()
            || !seen_right.insert(v)
            || left.node_label(u) != right.node_label(v)
        {
            return None;
        }
    }

    let mut left_nodes: Vec<usize> = left_to_right.keys().copied().collect();
    left_nodes.sort_unstable();
    let mut right_nodes: Vec<usize> = left_to_right.values().copied().collect();
    right_nodes.sort_unstable();

    let mut weight = node_pairs.len() as f64 * scoring.node_match_weight;
    let left_skeleton = embedding_skeleton_edges(left, &left_nodes)?;
    let right_skeleton: HashSet<(usize, usize)> = embedding_skeleton_edges(right, &right_nodes)?
        .into_iter()
        .map(|(u, v)| normalized_edge(u, v))
        .collect();
    let mapped_skeleton: HashSet<(usize, usize)> = left_skeleton
        .iter()
        .map(|&(u, u2)| normalized_edge(left_to_right[&u], left_to_right[&u2]))
        .collect();
    if mapped_skeleton != right_skeleton {
        return None;
    }

    for &(u, u2) in &left_skeleton {
        let v = left_to_right[&u];
        let v2 = left_to_right[&u2];
        let left_path = path_between(left, u, u2);
        let right_path = path_between(right, v, v2);
        if left_path.len() == 2 && right_path.len() == 2 {
            if left.edge_label(u, u2) != right.edge_label(v, v2) {
                return None;
            }
            weight += scoring.edge_match_weight;
        } else {
            let skipped = (left_path.len() - 2 + right_path.len() - 2) as f64;
            weight -= skip_vertex_penalty * skipped;
        }
    }
    Some(weight)
}

#[test]
fn embedding_matches_isomorphism_on_identical_inputs() {
    let tree = LabeledTree::new(vec![0, 1, 2, 3], &[(0, 1, 5), (1, 2, 6), (1, 3, 7)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let iso = maximum_common_subtree_isomorphism(&tree, &tree, &scoring);
    let emb =
        largest_weight_common_subtree_embedding_with_distance_penalty(&tree, &tree, &scoring, 0.5);
    assert_close(emb.weight, iso.weight);
    assert_eq!(emb.node_pairs, iso.node_pairs);
}

#[test]
fn embedding_can_skip_vertices_in_the_right_tree() {
    let left = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap();
    let right = LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let iso = maximum_common_subtree_isomorphism(&left, &right, &scoring);
    let emb = largest_weight_common_subtree_embedding_with_distance_penalty(
        &left, &right, &scoring, 0.25,
    );
    assert_eq!(iso.weight, 3.0);
    assert_close(emb.weight, 3.75);
    assert_eq!(emb.node_pairs, vec![(0, 0), (1, 2), (2, 3)]);
}

#[test]
fn embedding_can_skip_vertices_in_the_left_tree() {
    let left = LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap();
    let right = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let emb = largest_weight_common_subtree_embedding_with_distance_penalty(
        &left, &right, &scoring, 0.25,
    );
    assert_close(emb.weight, 3.75);
    assert_eq!(emb.node_pairs, vec![(0, 0), (2, 1), (3, 2)]);
}

#[test]
fn embedding_high_penalty_avoids_unnecessary_skips() {
    let left = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap();
    let right = LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let iso = maximum_common_subtree_isomorphism(&left, &right, &scoring);
    let emb = largest_weight_common_subtree_embedding_with_distance_penalty(
        &left, &right, &scoring, 10.0,
    );
    assert_close(emb.weight, iso.weight);
    assert_eq!(emb.node_pairs, iso.node_pairs);
}

#[test]
fn embedding_zero_penalty_crosses_long_paths() {
    let left = LabeledTree::new(vec![1, 2], &[(0, 1, 4)]).unwrap();
    let right = LabeledTree::new(vec![1, 9, 8, 2], &[(0, 1, 4), (1, 2, 4), (2, 3, 4)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let iso = maximum_common_subtree_isomorphism(&left, &right, &scoring);
    let emb =
        largest_weight_common_subtree_embedding_with_distance_penalty(&left, &right, &scoring, 0.0);
    assert_eq!(iso.weight, 1.0);
    assert_eq!(emb.weight, 2.0);
    assert_eq!(emb.node_pairs, vec![(0, 0), (1, 3)]);
}

#[test]
fn embedding_weight_is_symmetric_under_input_order() {
    let left = LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap();
    let right = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let a = largest_weight_common_subtree_embedding_with_distance_penalty(
        &left, &right, &scoring, 0.25,
    );
    let b = largest_weight_common_subtree_embedding_with_distance_penalty(
        &right, &left, &scoring, 0.25,
    );
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
            &left, &right, &scoring, penalty,
        );
        let witness_weight =
            score_embedding_witness(&left, &right, &scoring, &result.node_pairs, penalty)
                .expect("invalid embedding");
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
            &left, &right, &scoring, penalty,
        );
        assert!(result.weight <= previous + EPS);
        previous = result.weight;
    }
}

// Enumerate partial injections directly, without a DP, matching algorithm, or
// production scorer. Each complete mapping is checked by paths in both trees.
fn brute_force_weight(
    left: &LabeledTree,
    right: &LabeledTree,
    scoring: &ExactLabelScoring,
    penalty: f64,
) -> f64 {
    fn visit(
        left: &LabeledTree,
        right: &LabeledTree,
        scoring: &ExactLabelScoring,
        penalty: f64,
        u: usize,
        pairs: &mut Vec<(usize, usize)>,
        best: &mut f64,
    ) {
        if u == left.len() {
            if let Some(w) = score_embedding_witness(left, right, scoring, pairs, penalty) {
                *best = best.max(w);
            }
            return;
        }
        visit(left, right, scoring, penalty, u + 1, pairs, best);
        for v in 0..right.len() {
            if pairs.iter().any(|&(_, used)| used == v) {
                continue;
            }
            pairs.push((u, v));
            visit(left, right, scoring, penalty, u + 1, pairs, best);
            pairs.pop();
        }
    }
    let mut best = 0.0;
    visit(left, right, scoring, penalty, 0, &mut Vec::new(), &mut best);
    best
}

#[test]
fn skipped_paths_ignore_all_edge_labels_and_rewards() {
    for label in [5, 9] {
        let left = LabeledTree::new(vec![1, 2], &[(0, 1, 5)]).unwrap();
        let right = LabeledTree::new(vec![1, 99, 2], &[(0, 1, label), (1, 2, label)]).unwrap();
        let scoring = ExactLabelScoring {
            node_match_weight: 1.0,
            edge_match_weight: 100.0,
        };
        let result = largest_weight_common_subtree_embedding_with_distance_penalty(
            &left, &right, &scoring, 0.25,
        );
        assert_close(result.weight, 1.75);
        assert_close(
            score_embedding_witness(&left, &right, &scoring, &result.node_pairs, 0.25).unwrap(),
            1.75,
        );
    }
}

#[test]
fn embedding_matches_exhaustive_partial_injections() {
    let mut trees = vec![LabeledTree::new(vec![], &[]).unwrap()];
    // Every recursive labeled tree through four nodes, including stars and
    // paths. All binary vertex labelings, with alternating edge labels.
    for n in 1..=4usize {
        let count: usize = (1..n).product();
        for code in 0..count {
            let mut value = code;
            let mut edges = Vec::new();
            for child in 1..n {
                let parent = value % child;
                value /= child;
                edges.push((parent, child, (child % 2) as i64));
            }
            for labels in 0..(1usize << n) {
                trees.push(
                    LabeledTree::new((0..n).map(|i| ((labels >> i) & 1) as i64).collect(), &edges)
                        .unwrap(),
                );
            }
        }
    }
    for (i, left) in trees.iter().enumerate() {
        // Keep the full set of right shapes with fixed labels, plus a
        // deterministic sample of other labels, to bound CI runtime.
        for (j, right) in trees.iter().enumerate().filter(|(j, _)| j % 7 == 0) {
            for (node, edge, penalty) in [(1.0, 1.0, 0.25), (-1.0, 3.0, 0.0), (1.0, -2.0, 0.5)] {
                let scoring = ExactLabelScoring {
                    node_match_weight: node,
                    edge_match_weight: edge,
                };
                let result = largest_weight_common_subtree_embedding_with_distance_penalty(
                    left, right, &scoring, penalty,
                );
                let expected = brute_force_weight(left, right, &scoring, penalty);
                assert!(
                    (result.weight - expected).abs() < EPS,
                    "case {i}, {j}, {node}, {edge}, {penalty}: {} != {expected}",
                    result.weight
                );
                assert_close(
                    score_embedding_witness(left, right, &scoring, &result.node_pairs, penalty)
                        .unwrap(),
                    result.weight,
                );
            }
        }
    }
}
