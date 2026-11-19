use common_subtree_algorithms::{
    largest_weight_common_subtree_embedding_with_distance_penalty,
    max_weight_bipartite_matching, maximum_common_subtree_isomorphism, ExactLabelScoring,
    LabeledTree,
};

#[test]
fn bipartite_matching_smoke_test() {
    let weights = vec![
        vec![Some(3.0), Some(10.0), None],
        vec![Some(8.0), Some(4.0), Some(1.0)],
        vec![None, Some(9.0), Some(7.0)],
    ];
    let result = max_weight_bipartite_matching(&weights);
    assert_eq!(result.pairs, vec![(0, 1), (1, 0), (2, 2)]);
    assert_eq!(result.weight, 25.0);
}

#[test]
fn common_subtree_isomorphism_smoke_test() {
    // left:      1
    //          / \
    //         2   9
    //        /
    //       3
    // right: 4 - 1 - 2 - 3
    let left = LabeledTree::new(vec![1, 2, 3, 9], &[(0, 1, 5), (1, 2, 5), (0, 3, 0)])
        .unwrap();
    let right = LabeledTree::new(vec![4, 1, 2, 3], &[(0, 1, 0), (1, 2, 5), (2, 3, 5)])
        .unwrap();

    let result = maximum_common_subtree_isomorphism(&left, &right, &ExactLabelScoring::default());
    assert_eq!(result.weight, 5.0);
    assert_eq!(result.node_pairs, vec![(0, 1), (1, 2), (2, 3)]);
}

#[test]
fn distance_penalized_embedding_can_skip_inserted_vertex() {
    // left:  A - B - C
    // right: A - X - B - C
    let left = LabeledTree::new(vec![1, 2, 3], &[(0, 1, 1), (1, 2, 1)]).unwrap();
    let right = LabeledTree::new(vec![1, 99, 2, 3], &[(0, 1, 1), (1, 2, 1), (2, 3, 1)])
        .unwrap();

    let iso = maximum_common_subtree_isomorphism(&left, &right, &ExactLabelScoring::default());
    let emb = largest_weight_common_subtree_embedding_with_distance_penalty(
        &left,
        &right,
        &ExactLabelScoring::default(),
        0.25,
    );

    assert_eq!(iso.weight, 3.0); // best direct isomorphism is B-C: two nodes + one edge
    assert!(emb.weight > iso.weight);
    assert_eq!(emb.node_pairs, vec![(0, 0), (1, 2), (2, 3)]);
}
