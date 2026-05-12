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
