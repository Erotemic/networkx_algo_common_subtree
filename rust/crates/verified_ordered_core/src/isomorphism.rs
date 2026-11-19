//! Ordered adjacency-preserving subtree selection, distinct from contraction.
//!
//! A structural word describes the children of an implicit, actual tree root.
//! The level state preserves that root; the general state may choose any input
//! descendant as its root. Skipping a child removes its whole subtree and never
//! promotes grandchildren. Both functions are reference recursions, without a
//! memoization or paper running-time claim.

use crate::{choose_longer, BalancedWord, CommonEmbedding};

/// Maximum common subtree with both roots fixed. The historical result payload
/// `CommonEmbedding` stores only a structural word and its exact edge count;
/// this function's contract is adjacency-preserving subtree isomorphism.
pub fn rooted_common_isomorphism(
    left: &BalancedWord,
    right: &BalancedWord,
) -> Option<CommonEmbedding> {
    match (left, right) {
        (BalancedWord::Empty, _) | (_, BalancedWord::Empty) => Some(CommonEmbedding {
            word: BalancedWord::Empty,
            edges: 0,
        }),
        (BalancedWord::Pair(lh, lt), BalancedWord::Pair(rh, rt)) => {
            let heads = match rooted_common_isomorphism(lh, rh) {
                Some(value) => value,
                None => return None,
            };
            let tails = match rooted_common_isomorphism(lt, rt) {
                Some(value) => value,
                None => return None,
            };
            let subtotal = match heads.edges.checked_add(tails.edges) {
                Some(value) => value,
                None => return None,
            };
            let edges = match subtotal.checked_add(1) {
                Some(value) => value,
                None => return None,
            };
            let matched = CommonEmbedding {
                word: BalancedWord::Pair(Box::new(heads.word), Box::new(tails.word)),
                edges,
            };
            let drop_left = match rooted_common_isomorphism(lt, right) {
                Some(value) => value,
                None => return None,
            };
            let drop_right = match rooted_common_isomorphism(left, rt) {
                Some(value) => value,
                None => return None,
            };
            Some(choose_longer(choose_longer(matched, drop_left), drop_right))
        }
    }
}

/// Maximum common connected ordered subtree, allowing both roots to move.
/// Every admitted input has fewer than 2^32 edges per tree. Checked candidate
/// score arithmetic reports `None` if it cannot be represented. Ties prefer the
/// current-root witness, then left head/tail, then right head/tail.
pub fn largest_common_isomorphism(
    left: &BalancedWord,
    right: &BalancedWord,
) -> Option<CommonEmbedding> {
    match (left, right) {
        (BalancedWord::Empty, _) | (_, BalancedWord::Empty) => Some(CommonEmbedding {
            word: BalancedWord::Empty,
            edges: 0,
        }),
        (BalancedWord::Pair(lh, lt), BalancedWord::Pair(rh, rt)) => {
            let rooted = match rooted_common_isomorphism(left, right) {
                Some(value) => value,
                None => return None,
            };
            let left_head = match largest_common_isomorphism(lh, right) {
                Some(value) => value,
                None => return None,
            };
            let left_tail = match largest_common_isomorphism(lt, right) {
                Some(value) => value,
                None => return None,
            };
            let right_head = match largest_common_isomorphism(left, rh) {
                Some(value) => value,
                None => return None,
            };
            let right_tail = match largest_common_isomorphism(left, rt) {
                Some(value) => value,
                None => return None,
            };
            Some(choose_longer(
                rooted,
                choose_longer(
                    choose_longer(left_head, left_tail),
                    choose_longer(right_head, right_tail),
                ),
            ))
        }
    }
}
