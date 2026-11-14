//! Safe, extraction-friendly operations for the ordered contraction solver.
//!
//! The first operation connects a contraction's edge budget to the independent
//! mathematical edge count. The solver and its refinement are developed next.

/// Remaining edge budget after exactly one contraction. A singleton tree has
/// no edge to contract, so an empty budget returns `None`.
pub fn remaining_edges_after_contraction(edges: u32) -> Option<u32> {
    if edges == 0 {
        None
    } else {
        Some(edges - 1)
    }
}

/// A balanced word in its first-pair/interior/suffix representation. Every
/// value is balanced by construction; `Empty` represents a singleton tree.
pub enum BalancedWord {
    Empty,
    Pair(Box<BalancedWord>, Box<BalancedWord>),
}

/// Own a structural copy without depending on a derived cloning implementation.
pub fn copy_word(word: &BalancedWord) -> BalancedWord {
    match word {
        BalancedWord::Empty => BalancedWord::Empty,
        BalancedWord::Pair(head, tail) => {
            BalancedWord::Pair(Box::new(copy_word(head)), Box::new(copy_word(tail)))
        }
    }
}

/// Concatenate two balanced words, preserving every pair's nesting.
pub fn concatenate(left: &BalancedWord, right: &BalancedWord) -> BalancedWord {
    match left {
        BalancedWord::Empty => copy_word(right),
        BalancedWord::Pair(head, tail) => BalancedWord::Pair(
            Box::new(copy_word(head)),
            Box::new(concatenate(tail, right)),
        ),
    }
}

/// An explicit balanced-word witness and its edge score.
pub struct CommonEmbedding {
    pub word: BalancedWord,
    pub edges: u32,
}

/// Retain the first witness on equal scores.
pub fn choose_longer(first: CommonEmbedding, second: CommonEmbedding) -> CommonEmbedding {
    if first.edges < second.edges {
        second
    } else {
        first
    }
}

/// Construct a maximum common embedded tree using the three branches of the
/// ordered balanced-word recurrence. The slow reference recursion intentionally
/// precedes memoization. Returns `None` if a candidate score overflows `u32`.
/// Ties retain the matched-root candidate, then the left-deletion candidate.
pub fn largest_common_embedding(
    left: &BalancedWord,
    right: &BalancedWord,
) -> Option<CommonEmbedding> {
    match (left, right) {
        (BalancedWord::Empty, _) | (_, BalancedWord::Empty) => Some(CommonEmbedding {
            word: BalancedWord::Empty,
            edges: 0,
        }),
        (BalancedWord::Pair(lh, lt), BalancedWord::Pair(rh, rt)) => {
            let heads = match largest_common_embedding(lh, rh) {
                Some(value) => value,
                None => return None,
            };
            let tails = match largest_common_embedding(lt, rt) {
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
            let contracted_left = concatenate(lh, lt);
            let drop_left = match largest_common_embedding(&contracted_left, right) {
                Some(value) => value,
                None => return None,
            };
            let contracted_right = concatenate(rh, rt);
            let drop_right = match largest_common_embedding(left, &contracted_right) {
                Some(value) => value,
                None => return None,
            };
            Some(choose_longer(choose_longer(matched, drop_left), drop_right))
        }
    }
}
