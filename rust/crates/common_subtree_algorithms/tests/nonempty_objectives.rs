use common_subtree_algorithms::{
    largest_weight_common_subtree_embedding_with_distance_penalty,
    largest_weight_nonempty_common_subtree_embedding_with_distance_penalty,
    maximum_common_subtree_isomorphism, maximum_nonempty_common_subtree_isomorphism,
    ExactLabelScoring, LabeledTree,
};

#[test]
fn nonempty_objectives_retain_negative_and_zero_optima() {
    let tree = LabeledTree::new(vec![1, 1], &[(0, 1, 0)]).unwrap();
    for node_weight in [-2.0, 0.0] {
        let scoring = ExactLabelScoring {
            node_match_weight: node_weight,
            edge_match_weight: -1.0,
        };
        let iso = maximum_nonempty_common_subtree_isomorphism(&tree, &tree, &scoring).unwrap();
        let emb = largest_weight_nonempty_common_subtree_embedding_with_distance_penalty(
            &tree, &tree, &scoring, 0.25,
        )
        .unwrap();
        assert_eq!(iso.weight, node_weight);
        assert_eq!(emb.weight, node_weight);
        assert_eq!(iso.node_pairs.len(), 1);
        assert_eq!(emb.node_pairs.len(), 1);
        assert!(maximum_common_subtree_isomorphism(&tree, &tree, &scoring)
            .node_pairs
            .is_empty());
        assert!(
            largest_weight_common_subtree_embedding_with_distance_penalty(
                &tree, &tree, &scoring, 0.25
            )
            .node_pairs
            .is_empty()
        );
    }
}

#[test]
fn positive_edge_rewards_can_offset_negative_vertices() {
    let tree = LabeledTree::new(vec![1, 1], &[(0, 1, 0)]).unwrap();
    let scoring = ExactLabelScoring {
        node_match_weight: -5.0,
        edge_match_weight: 11.0,
    };
    assert_eq!(
        maximum_nonempty_common_subtree_isomorphism(&tree, &tree, &scoring)
            .unwrap()
            .weight,
        1.0
    );
    assert_eq!(
        largest_weight_nonempty_common_subtree_embedding_with_distance_penalty(
            &tree, &tree, &scoring, 0.25
        )
        .unwrap()
        .weight,
        1.0
    );
}

#[test]
fn no_compatible_mapping_is_distinct_from_empty_and_negative() {
    let left = LabeledTree::new(vec![1], &[]).unwrap();
    let right = LabeledTree::new(vec![2], &[]).unwrap();
    let empty = LabeledTree::new(vec![], &[]).unwrap();
    let scoring = ExactLabelScoring::default();
    for other in [&right, &empty] {
        assert!(maximum_nonempty_common_subtree_isomorphism(&left, other, &scoring).is_none());
        assert!(
            largest_weight_nonempty_common_subtree_embedding_with_distance_penalty(
                &left, other, &scoring, 0.25
            )
            .is_none()
        );
    }
}

#[test]
fn positive_gains_below_old_threshold_are_retained() {
    let tiny = 5.0e-12;
    for tree in [
        LabeledTree::new(vec![1], &[]).unwrap(),
        LabeledTree::new(vec![1, 1], &[(0, 1, 0)]).unwrap(),
    ] {
        let scoring = ExactLabelScoring {
            node_match_weight: tiny,
            edge_match_weight: 0.0,
        };
        let expected = tiny * tree.len() as f64;
        let iso = maximum_common_subtree_isomorphism(&tree, &tree, &scoring);
        let emb = largest_weight_common_subtree_embedding_with_distance_penalty(
            &tree, &tree, &scoring, 0.25,
        );
        assert_eq!(iso.weight, expected);
        assert_eq!(emb.weight, expected);
        assert_eq!(iso.node_pairs.len(), tree.len());
        assert_eq!(emb.node_pairs.len(), tree.len());
    }
}

#[test]
fn close_scores_are_not_treated_as_equal() {
    use common_subtree_algorithms::Scoring;
    struct CloseScores;
    impl Scoring for CloseScores {
        fn node_weight(&self, _: &LabeledTree, _: usize, _: &LabeledTree, v: usize) -> Option<f64> {
            Some(1.0 + v as f64 * 5.0e-10)
        }
        fn edge_weight(
            &self,
            _: &LabeledTree,
            _: usize,
            _: usize,
            _: &LabeledTree,
            _: usize,
            _: usize,
        ) -> Option<f64> {
            None
        }
    }
    let left = LabeledTree::new(vec![1], &[]).unwrap();
    let right = LabeledTree::new(vec![1, 1], &[(0, 1, 0)]).unwrap();
    let iso = maximum_common_subtree_isomorphism(&left, &right, &CloseScores);
    let emb = largest_weight_common_subtree_embedding_with_distance_penalty(
        &left,
        &right,
        &CloseScores,
        0.25,
    );
    assert_eq!(iso.node_pairs, vec![(0, 1)]);
    assert_eq!(emb.node_pairs, vec![(0, 1)]);
    assert_eq!(iso.weight, 1.0 + 5.0e-10);
    assert_eq!(emb.weight, 1.0 + 5.0e-10);
}

#[test]
fn graph_solvers_reject_nonfinite_scoring_values() {
    for node_weight in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        let tree = LabeledTree::new(vec![1], &[]).unwrap();
        let scoring = ExactLabelScoring {
            node_match_weight: node_weight,
            edge_match_weight: 0.0,
        };
        assert!(
            std::panic::catch_unwind(|| maximum_common_subtree_isomorphism(&tree, &tree, &scoring))
                .is_err()
        );
        assert!(std::panic::catch_unwind(|| {
            largest_weight_common_subtree_embedding_with_distance_penalty(
                &tree, &tree, &scoring, 0.25,
            )
        })
        .is_err());
    }
    for edge_weight in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        let tree = LabeledTree::new(vec![1, 1], &[(0, 1, 0)]).unwrap();
        let scoring = ExactLabelScoring {
            node_match_weight: 1.0,
            edge_match_weight: edge_weight,
        };
        assert!(
            std::panic::catch_unwind(|| maximum_common_subtree_isomorphism(&tree, &tree, &scoring))
                .is_err()
        );
        assert!(std::panic::catch_unwind(|| {
            largest_weight_common_subtree_embedding_with_distance_penalty(
                &tree, &tree, &scoring, 0.25,
            )
        })
        .is_err());
    }
}

#[test]
fn graph_solvers_reject_accumulation_overflow() {
    let tree = LabeledTree::new(vec![1, 1], &[(0, 1, 0)]).unwrap();
    let scoring = ExactLabelScoring {
        node_match_weight: f64::MAX,
        edge_match_weight: 0.0,
    };
    assert!(
        std::panic::catch_unwind(|| maximum_common_subtree_isomorphism(&tree, &tree, &scoring))
            .is_err()
    );
    assert!(std::panic::catch_unwind(|| {
        largest_weight_common_subtree_embedding_with_distance_penalty(&tree, &tree, &scoring, 0.25)
    })
    .is_err());
}
