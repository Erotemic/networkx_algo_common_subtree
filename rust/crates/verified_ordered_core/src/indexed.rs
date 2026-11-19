//! Original opening-pair indices for independently maximum contractions.
//!
//! Shape memoization remains independent of occurrence identities. Number each
//! original input in preorder, then reconstruct that optimal shape by actual
//! indexed pair deletions. Different equal-shaped input occurrences retain
//! their own indices. Reconstruction is a reference backtracking algorithm.

use crate::{maximum_common_embedding, BalancedWord};

/// A balanced pair with its zero-based original opening/preorder pair index.
pub enum IndexedWord {
    Empty,
    Pair(u32, Box<IndexedWord>, Box<IndexedWord>),
}

pub struct NumberedWord {
    pub word: IndexedWord,
    pub next: u32,
}

/// Both words have the same shape. Their corresponding pair indices identify
/// the actual retained input edges. The implicit root has no incoming pair.
pub struct IndexedCommonEmbedding {
    pub left: IndexedWord,
    pub right: IndexedWord,
    pub edges: u32,
}

pub fn copy_indexed(word: &IndexedWord) -> IndexedWord {
    match word {
        IndexedWord::Empty => IndexedWord::Empty,
        IndexedWord::Pair(index, head, tail) => IndexedWord::Pair(
            *index,
            Box::new(copy_indexed(head)),
            Box::new(copy_indexed(tail)),
        ),
    }
}

pub fn append_indexed(left: &IndexedWord, right: &IndexedWord) -> IndexedWord {
    match left {
        IndexedWord::Empty => copy_indexed(right),
        IndexedWord::Pair(index, head, tail) => IndexedWord::Pair(
            *index,
            Box::new(copy_indexed(head)),
            Box::new(append_indexed(tail, right)),
        ),
    }
}

/// Canonical pair numbering starts at `next` and returns the first unused
/// index. A final counter outside u32 is reported explicitly as `None`.
pub fn number_word(word: &BalancedWord, next: u32) -> Option<NumberedWord> {
    match word {
        BalancedWord::Empty => Some(NumberedWord {
            word: IndexedWord::Empty,
            next,
        }),
        BalancedWord::Pair(head, tail) => {
            let following = match next.checked_add(1) {
                Some(value) => value,
                None => return None,
            };
            let head = match number_word(head, following) {
                Some(value) => value,
                None => return None,
            };
            let tail = match number_word(tail, head.next) {
                Some(value) => value,
                None => return None,
            };
            Some(NumberedWord {
                word: IndexedWord::Pair(next, Box::new(head.word), Box::new(tail.word)),
                next: tail.next,
            })
        }
    }
}

/// Find an actual indexed contraction with precisely the requested shape.
/// Try retaining the first pair, then delete that pair and splice its contents.
/// Returns `None` precisely when the shape is not obtainable by contractions.
pub fn reconstruct_embedding(pattern: &BalancedWord, input: &IndexedWord) -> Option<IndexedWord> {
    match (pattern, input) {
        (BalancedWord::Empty, _) => Some(IndexedWord::Empty),
        (_, IndexedWord::Empty) => None,
        (BalancedWord::Pair(ph, pt), IndexedWord::Pair(index, head, tail)) => {
            match reconstruct_embedding(ph, head) {
                Some(inside) => match reconstruct_embedding(pt, tail) {
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
            let contracted = append_indexed(head, tail);
            reconstruct_embedding(pattern, &contracted)
        }
    }
}

/// Independently maximum common contracted tree with original pair indices.
///
/// For inputs with fewer than 2^32 pairs, all checked arithmetic succeeds and
/// the optimal shape can be reconstructed in both originals. The returned
/// indexed trees identify corresponding retained edges in preorder. These are
/// edge/pair indices, distinct from a vertex-pair Python sequence conversion.
pub fn maximum_common_embedding_indexed(
    left: &BalancedWord,
    right: &BalancedWord,
) -> Option<IndexedCommonEmbedding> {
    let shape = match maximum_common_embedding(left, right) {
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
    let left = match reconstruct_embedding(&shape.word, &left_input.word) {
        Some(value) => value,
        None => return None,
    };
    let right = match reconstruct_embedding(&shape.word, &right_input.word) {
        Some(value) => value,
        None => return None,
    };
    Some(IndexedCommonEmbedding {
        left,
        right,
        edges: shape.edges,
    })
}
