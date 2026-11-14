use common_subtree_algorithms::{
    largest_weight_nonempty_common_subtree_embedding_with_roots,
    maximum_nonempty_common_subtree_isomorphism_with_roots, ExactLabelScoring, LabeledTree,
    RootConstraint,
};

#[test]
fn ambient_orientations_and_forced_roots_have_distinct_optima() {
    let tree = LabeledTree::new(vec![0, 1, 2], &[(0, 1, 0), (1, 2, 0)]).unwrap();
    let scoring = ExactLabelScoring::default();
    for (constraint, expected) in [
        (RootConstraint::Unrooted, Some(5.0)),
        (
            RootConstraint::Rooted {
                left: 0,
                right: 2,
                root_to_root: false,
            },
            Some(1.0),
        ),
        (
            RootConstraint::Rooted {
                left: 0,
                right: 2,
                root_to_root: true,
            },
            None,
        ),
        (
            RootConstraint::Rooted {
                left: 1,
                right: 0,
                root_to_root: false,
            },
            Some(3.0),
        ),
        (
            RootConstraint::Rooted {
                left: 1,
                right: 1,
                root_to_root: true,
            },
            Some(5.0),
        ),
    ] {
        let iso = maximum_nonempty_common_subtree_isomorphism_with_roots(
            &tree, &tree, &scoring, constraint,
        );
        let embedding = largest_weight_nonempty_common_subtree_embedding_with_roots(
            &tree, &tree, &scoring, 0.25, constraint,
        );
        assert_eq!(iso.map(|r| r.weight), expected);
        assert_eq!(embedding.map(|r| r.weight), expected);
    }
}

#[test]
fn rooted_embeddings_do_not_join_across_a_skipped_highest_vertex() {
    let left = LabeledTree::new(vec![99, 1, 2], &[(0, 1, 0), (0, 2, 0)]).unwrap();
    let right = LabeledTree::new(vec![1, 2], &[(0, 1, 0)]).unwrap();
    let scoring = ExactLabelScoring {
        node_match_weight: 1.0,
        edge_match_weight: 100.0,
    };
    for (constraint, expected) in [
        (RootConstraint::Unrooted, Some(1.75)),
        (
            RootConstraint::Rooted {
                left: 0,
                right: 0,
                root_to_root: false,
            },
            Some(1.0),
        ),
        (
            RootConstraint::Rooted {
                left: 0,
                right: 0,
                root_to_root: true,
            },
            None,
        ),
        (
            RootConstraint::Rooted {
                left: 1,
                right: 0,
                root_to_root: true,
            },
            Some(1.75),
        ),
    ] {
        let result = largest_weight_nonempty_common_subtree_embedding_with_roots(
            &left, &right, &scoring, 0.25, constraint,
        );
        assert_eq!(result.map(|r| r.weight), expected);
    }
}

#[test]
#[should_panic(expected = "tree roots must be input vertices")]
fn invalid_native_root_is_rejected() {
    let tree = LabeledTree::new(vec![0], &[]).unwrap();
    maximum_nonempty_common_subtree_isomorphism_with_roots(
        &tree,
        &tree,
        &ExactLabelScoring::default(),
        RootConstraint::Rooted {
            left: 1,
            right: 0,
            root_to_root: false,
        },
    );
}
