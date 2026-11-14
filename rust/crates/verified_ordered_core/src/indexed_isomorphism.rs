//! Original-pair reconstruction around the source-proved structural solvers.
//!
//! Whole child subtrees may be removed; grandchildren are never promoted.
//! These reconstruction functions are tested/extracted, not yet source proved.
//! The structural optimum still comes from the existing proved reference core.

use crate::{
    indexed::{number_word, IndexedCommonEmbedding, IndexedWord},
    isomorphism::{largest_common_isomorphism, rooted_common_isomorphism},
    BalancedWord,
};

/// Retain an ordered subsequence of children of the same original parent.
/// Matching a pair recurses into its children; skipping it drops the whole
/// subtree. In particular, an interior match cannot replace a sibling.
pub fn reconstruct_rooted_isomorphism(
    pattern: &BalancedWord,
    input: &IndexedWord,
) -> Option<IndexedWord> {
    match (pattern, input) {
        (BalancedWord::Empty, _) => Some(IndexedWord::Empty),
        (_, IndexedWord::Empty) => None,
        (BalancedWord::Pair(ph, pt), IndexedWord::Pair(index, head, tail)) => {
            match reconstruct_rooted_isomorphism(ph, head) {
                Some(inside) => match reconstruct_rooted_isomorphism(pt, tail) {
                    Some(outside) => {
                        return Some(IndexedWord::Pair(
                            *index,
                            Box::new(inside),
                            Box::new(outside),
                        ))
                    }
                    None => {}
                },
                None => {}
            }
            reconstruct_rooted_isomorphism(pattern, tail)
        }
    }
}

/// The implicit parent may move to any original vertex; once chosen, all
/// retained component roots are children of that same parent.
pub fn reconstruct_any_isomorphism(
    pattern: &BalancedWord,
    input: &IndexedWord,
) -> Option<IndexedWord> {
    match reconstruct_rooted_isomorphism(pattern, input) {
        Some(value) => Some(value),
        None => match input {
            IndexedWord::Empty => None,
            IndexedWord::Pair(_, head, tail) => match reconstruct_any_isomorphism(pattern, head) {
                Some(value) => Some(value),
                None => reconstruct_any_isomorphism(pattern, tail),
            },
        },
    }
}

/// Unweighted reference isomorphism with original preorder pair identities.
/// `rooted` retains both implicit parents. The existing structural solvers
/// supply the optimum; indexed reconstruction remains a separate proof gap.
/// This is an exponential reference, with no production runtime claim.
pub fn maximum_common_isomorphism_indexed(
    left: &BalancedWord,
    right: &BalancedWord,
    rooted: bool,
) -> Option<IndexedCommonEmbedding> {
    let shape = match if rooted {
        rooted_common_isomorphism(left, right)
    } else {
        largest_common_isomorphism(left, right)
    } {
        Some(value) => value,
        None => return None,
    };
    let left_input = match number_word(left, 0) {
        Some(value) => value,
        None => return None,
    };
    let right_input = match number_word(right, 0) {
        Some(value) => value,
        None => return None,
    };
    let left = match if rooted {
        reconstruct_rooted_isomorphism(&shape.word, &left_input.word)
    } else {
        reconstruct_any_isomorphism(&shape.word, &left_input.word)
    } {
        Some(value) => value,
        None => return None,
    };
    let right = match if rooted {
        reconstruct_rooted_isomorphism(&shape.word, &right_input.word)
    } else {
        reconstruct_any_isomorphism(&shape.word, &right_input.word)
    } {
        Some(value) => value,
        None => return None,
    };
    Some(IndexedCommonEmbedding {
        left,
        right,
        edges: shape.edges,
    })
}
