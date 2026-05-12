use std::collections::{HashMap, HashSet, VecDeque};

use common_subtree_algorithms::{
    maximum_common_subtree_isomorphism, ExactLabelScoring, LabeledTree, Scoring,
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

fn subset_nodes(mask: usize, n: usize) -> Vec<usize> {
    (0..n).filter(|&node| ((mask >> node) & 1) == 1).collect()
}

fn connected_subsets(tree: &LabeledTree) -> Vec<Vec<usize>> {
    let n = tree.len();
    let mut out = Vec::new();
    for mask in 1usize..(1usize << n) {
        let nodes = subset_nodes(mask, n);
        if is_connected_subset(tree, &nodes) {
            out.push(nodes);
        }
    }
    out
}

fn is_connected_subset(tree: &LabeledTree, nodes: &[usize]) -> bool {
    let wanted: HashSet<usize> = nodes.iter().copied().collect();
    let mut seen = HashSet::from([nodes[0]]);
    let mut queue = VecDeque::from([nodes[0]]);
    while let Some(u) = queue.pop_front() {
        for edge in tree.neighbors(u) {
            if wanted.contains(&edge.to) && seen.insert(edge.to) {
                queue.push_back(edge.to);
            }
        }
    }
    seen.len() == wanted.len()
}

fn induced_edges(tree: &LabeledTree, nodes: &[usize]) -> Vec<(usize, usize)> {
    let wanted: HashSet<usize> = nodes.iter().copied().collect();
    let mut out = Vec::new();
    for &u in nodes {
        for edge in tree.neighbors(u) {
            if u < edge.to && wanted.contains(&edge.to) {
                out.push((u, edge.to));
            }
        }
    }
    out.sort_unstable();
    out
}

fn permutations(items: &[usize]) -> Vec<Vec<usize>> {
    fn rec(start: usize, data: &mut [usize], out: &mut Vec<Vec<usize>>) {
        if start == data.len() {
            out.push(data.to_vec());
            return;
        }
        for idx in start..data.len() {
            data.swap(start, idx);
            rec(start + 1, data, out);
            data.swap(start, idx);
        }
    }
    let mut data = items.to_vec();
    let mut out = Vec::new();
    rec(0, &mut data, &mut out);
    out
}

fn brute_force_exact_weight<S: Scoring>(left: &LabeledTree, right: &LabeledTree, scoring: &S) -> f64 {
    if left.is_empty() || right.is_empty() {
        return 0.0;
    }
    let left_subsets = connected_subsets(left);
    let right_subsets = connected_subsets(right);
    let mut best = 0.0;
    for left_nodes in &left_subsets {
        let left_edges = induced_edges(left, left_nodes);
        for right_nodes in &right_subsets {
            if left_nodes.len() != right_nodes.len() {
                continue;
            }
            let right_edge_set: HashSet<(usize, usize)> = induced_edges(right, right_nodes)
                .into_iter()
                .map(|(u, v)| normalized_edge(u, v))
                .collect();
            for right_perm in permutations(right_nodes) {
                let node_map: HashMap<usize, usize> = left_nodes
                    .iter()
                    .copied()
                    .zip(right_perm.into_iter())
                    .collect();
                let mut weight = 0.0;
                let mut ok = true;
                for &u in left_nodes {
                    match scoring.node_weight(left, u, right, node_map[&u]) {
                        Some(w) => weight += w,
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if !ok {
                    continue;
                }
                for &(u, u_child) in &left_edges {
                    let v = node_map[&u];
                    let v_child = node_map[&u_child];
                    if !right_edge_set.contains(&normalized_edge(v, v_child)) {
                        ok = false;
                        break;
                    }
                    match scoring.edge_weight(left, u, u_child, right, v, v_child) {
                        Some(w) => weight += w,
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok && weight > best {
                    best = weight;
                }
            }
        }
    }
    best
}

fn score_isomorphism_witness<S: Scoring>(
    left: &LabeledTree,
    right: &LabeledTree,
    scoring: &S,
    node_pairs: &[(usize, usize)],
) -> f64 {
    if node_pairs.is_empty() {
        return 0.0;
    }

    let mut left_to_right = HashMap::new();
    let mut seen_right = HashSet::new();
    for &(u, v) in node_pairs {
        assert!(u < left.len(), "left witness node {u} is out of bounds");
        assert!(v < right.len(), "right witness node {v} is out of bounds");
        assert!(left_to_right.insert(u, v).is_none(), "left node {u} appears twice");
        assert!(seen_right.insert(v), "right node {v} appears twice");
    }

    let mut left_nodes: Vec<usize> = left_to_right.keys().copied().collect();
    left_nodes.sort_unstable();
    let mut right_nodes: Vec<usize> = left_to_right.values().copied().collect();
    right_nodes.sort_unstable();
    assert!(is_connected_subset(left, &left_nodes));
    assert!(is_connected_subset(right, &right_nodes));

    let mut weight = 0.0;
    for (&u, &v) in &left_to_right {
        weight += scoring
            .node_weight(left, u, right, v)
            .expect("witness contains an incompatible node pair");
    }

    let left_edges = induced_edges(left, &left_nodes);
    let right_edges: HashSet<(usize, usize)> = induced_edges(right, &right_nodes)
        .into_iter()
        .map(|(u, v)| normalized_edge(u, v))
        .collect();
    let mapped_edges: HashSet<(usize, usize)> = left_edges
        .iter()
        .map(|&(u, u_child)| normalized_edge(left_to_right[&u], left_to_right[&u_child]))
        .collect();
    assert_eq!(mapped_edges, right_edges, "witness does not preserve induced edges");

    for &(u, u_child) in &left_edges {
        let v = left_to_right[&u];
        let v_child = left_to_right[&u_child];
        weight += scoring
            .edge_weight(left, u, u_child, right, v, v_child)
            .expect("witness contains an incompatible edge pair");
    }
    weight
}

fn check_against_bruteforce(left: &LabeledTree, right: &LabeledTree) {
    let scoring = ExactLabelScoring::default();
    let expected = brute_force_exact_weight(left, right, &scoring);
    let result = maximum_common_subtree_isomorphism(left, right, &scoring);
    assert_close(result.weight, expected);
    let witness_weight = score_isomorphism_witness(left, right, &scoring, &result.node_pairs);
    assert_close(witness_weight, result.weight);
}

#[test]
fn mcsi_matches_bruteforce_on_handwritten_tree_pairs() {
    let cases = vec![
        LabeledTree::new(vec![1], &[]).unwrap(),
        LabeledTree::new(vec![1, 2], &[(0, 1, 5)]).unwrap(),
        LabeledTree::new(vec![1, 2], &[(0, 1, 6)]).unwrap(),
        LabeledTree::new(vec![1, 2, 3], &[(0, 1, 7), (1, 2, 7)]).unwrap(),
        LabeledTree::new(vec![3, 2, 1], &[(0, 1, 7), (1, 2, 7)]).unwrap(),
        LabeledTree::new(vec![0, 1, 2, 3], &[(0, 1, 9), (0, 2, 9), (0, 3, 9)]).unwrap(),
        LabeledTree::new(vec![0, 3, 2, 1], &[(0, 1, 9), (0, 2, 9), (0, 3, 9)]).unwrap(),
        LabeledTree::new(vec![1, 9, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]).unwrap(),
    ];

    for left in &cases {
        for right in &cases {
            check_against_bruteforce(left, right);
        }
    }
}

#[test]
fn mcsi_respects_edge_label_incompatibility() {
    let left = LabeledTree::new(vec![1, 2], &[(0, 1, 5)]).unwrap();
    let right = LabeledTree::new(vec![1, 2], &[(0, 1, 6)]).unwrap();
    let result = maximum_common_subtree_isomorphism(&left, &right, &ExactLabelScoring::default());
    assert_eq!(result.weight, 1.0);
    assert_eq!(result.node_pairs.len(), 1);
}

#[test]
fn mcsi_is_unordered_for_star_children() {
    let left = LabeledTree::new(vec![0, 1, 2, 3], &[(0, 1, 7), (0, 2, 7), (0, 3, 7)]).unwrap();
    let right = LabeledTree::new(vec![0, 3, 2, 1], &[(0, 1, 7), (0, 2, 7), (0, 3, 7)]).unwrap();
    let result = maximum_common_subtree_isomorphism(&left, &right, &ExactLabelScoring::default());
    assert_eq!(result.weight, 7.0);
    assert_eq!(result.node_pairs, vec![(0, 0), (1, 3), (2, 2), (3, 1)]);
}

#[test]
fn mcsi_weight_is_symmetric_under_input_order() {
    let left = LabeledTree::new(vec![1, 2, 3, 9], &[(0, 1, 5), (1, 2, 5), (0, 3, 0)]).unwrap();
    let right = LabeledTree::new(vec![4, 1, 2, 3], &[(0, 1, 0), (1, 2, 5), (2, 3, 5)]).unwrap();
    let scoring = ExactLabelScoring::default();
    let a = maximum_common_subtree_isomorphism(&left, &right, &scoring);
    let b = maximum_common_subtree_isomorphism(&right, &left, &scoring);
    assert_close(a.weight, b.weight);
}

fn prufer_edges(code: &[usize]) -> Vec<(usize, usize, i64)> {
    let n = code.len() + 2;
    let mut degree = vec![1usize; n];
    for &node in code {
        degree[node] += 1;
    }

    let mut edges = Vec::new();
    for &node in code {
        let leaf = (0..n).find(|&idx| degree[idx] == 1).unwrap();
        edges.push((leaf.min(node), leaf.max(node), 1));
        degree[leaf] -= 1;
        degree[node] -= 1;
    }
    let remaining: Vec<usize> = (0..n).filter(|&idx| degree[idx] == 1).collect();
    edges.push((remaining[0].min(remaining[1]), remaining[0].max(remaining[1]), 1));
    edges.sort_unstable();
    edges
}

fn all_labeled_tree_shapes(n: usize) -> Vec<Vec<(usize, usize, i64)>> {
    if n == 1 {
        return vec![Vec::new()];
    }

    fn rec(
        pos: usize,
        len: usize,
        n: usize,
        code: &mut Vec<usize>,
        seen: &mut HashSet<Vec<(usize, usize, i64)>>,
        out: &mut Vec<Vec<(usize, usize, i64)>>,
    ) {
        if pos == len {
            let edges = prufer_edges(code);
            if seen.insert(edges.clone()) {
                out.push(edges);
            }
            return;
        }
        for node in 0..n {
            code.push(node);
            rec(pos + 1, len, n, code, seen, out);
            code.pop();
        }
    }

    let mut seen = HashSet::new();
    let mut out = Vec::new();
    rec(0, n - 2, n, &mut Vec::new(), &mut seen, &mut out);
    out
}

fn binary_labels(n: usize, offset: usize) -> Vec<i64> {
    (0..n).map(|idx| ((idx + offset) % 2) as i64).collect()
}

#[test]
fn mcsi_matches_bruteforce_for_all_prufer_trees_up_to_four_nodes() {
    let mut cases = Vec::new();
    for n in 1..=4 {
        for edges in all_labeled_tree_shapes(n) {
            cases.push(LabeledTree::new(binary_labels(n, 0), &edges).unwrap());
            cases.push(LabeledTree::new(binary_labels(n, 1), &edges).unwrap());
        }
    }

    for left in &cases {
        for right in &cases {
            check_against_bruteforce(left, right);
        }
    }
}

#[test]
fn mcsi_identity_scores_full_tree_for_all_small_shapes() {
    let scoring = ExactLabelScoring::default();
    for n in 1..=5 {
        for edges in all_labeled_tree_shapes(n) {
            let tree = LabeledTree::new(binary_labels(n, 0), &edges).unwrap();
            let result = maximum_common_subtree_isomorphism(&tree, &tree, &scoring);
            assert_close(result.weight, (2 * n - 1) as f64);
            let witness_weight = score_isomorphism_witness(&tree, &tree, &scoring, &result.node_pairs);
            assert_close(witness_weight, result.weight);
        }
    }
}
