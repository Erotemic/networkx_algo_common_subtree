//! Indexed reconstruction guided by shared memoized containment checks.

use crate::{
    indexed::{append_indexed, number_word, IndexedCommonEmbedding, IndexedWord},
    memoized_common_embedding, words_equal, BalancedWord, MemoTable,
};

/// Erase original pair identities while retaining the entire balanced shape.
pub fn erase_indexed(word: &IndexedWord) -> BalancedWord {
    match word {
        IndexedWord::Empty => BalancedWord::Empty,
        IndexedWord::Pair(_, head, tail) => {
            BalancedWord::Pair(Box::new(erase_indexed(head)), Box::new(erase_indexed(tail)))
        }
    }
}

/// A maximum common word equals the complete pattern exactly when it embeds.
pub fn embedding_possible(
    pattern: &BalancedWord,
    input: &IndexedWord,
    table: MemoTable,
) -> (Option<bool>, MemoTable) {
    let shape = erase_indexed(input);
    let (matching, table) = memoized_common_embedding(pattern, &shape, table);
    match matching {
        Some(matching) => (Some(words_equal(&matching.word, pattern)), table),
        None => (None, table),
    }
}

/// Test the two independent pieces of a retained first pair, threading one memo.
pub fn keep_first_pair(
    pattern_head: &BalancedWord,
    pattern_tail: &BalancedWord,
    input_head: &IndexedWord,
    input_tail: &IndexedWord,
    table: MemoTable,
) -> (Option<bool>, MemoTable) {
    let (head_possible, table) = embedding_possible(pattern_head, input_head, table);
    match head_possible {
        None => (None, table),
        Some(false) => (Some(false), table),
        Some(true) => embedding_possible(pattern_tail, input_tail, table),
    }
}

/// The concrete recursive-call count distinguishes reconstruction work from
/// the separately memoized feasibility computations and structural copying.
pub struct GuidedReconstruction {
    pub word: Option<IndexedWord>,
    pub table: MemoTable,
    pub calls: u64,
}

/// Choose whether to keep the first pair before recursively reconstructing it.
/// A rejected keep branch performs no recursive witness construction.
pub fn reconstruct_guided(
    pattern: &BalancedWord,
    input: &IndexedWord,
    table: MemoTable,
) -> Option<GuidedReconstruction> {
    match pattern {
        BalancedWord::Empty => Some(GuidedReconstruction {
            word: Some(IndexedWord::Empty),
            table,
            calls: 1,
        }),
        BalancedWord::Pair(ph, pt) => match input {
            IndexedWord::Empty => Some(GuidedReconstruction {
                word: None,
                table,
                calls: 1,
            }),
            IndexedWord::Pair(index, head, tail) => {
                let (keep, table) = keep_first_pair(ph, pt, head, tail, table);
                let keep = match keep {
                    Some(value) => value,
                    None => return None,
                };
                if keep {
                    let inside = match reconstruct_guided(ph, head, table) {
                        Some(value) => value,
                        None => return None,
                    };
                    let inside_word = match inside.word {
                        Some(value) => value,
                        None => return None,
                    };
                    let outside = match reconstruct_guided(pt, tail, inside.table) {
                        Some(value) => value,
                        None => return None,
                    };
                    let outside_word = match outside.word {
                        Some(value) => value,
                        None => return None,
                    };
                    let subtotal = match inside.calls.checked_add(outside.calls) {
                        Some(value) => value,
                        None => return None,
                    };
                    let calls = match subtotal.checked_add(1) {
                        Some(value) => value,
                        None => return None,
                    };
                    Some(GuidedReconstruction {
                        word: Some(IndexedWord::Pair(
                            *index,
                            Box::new(inside_word),
                            Box::new(outside_word),
                        )),
                        table: outside.table,
                        calls,
                    })
                } else {
                    let contracted = append_indexed(head, tail);
                    let result = match reconstruct_guided(pattern, &contracted, table) {
                        Some(value) => value,
                        None => return None,
                    };
                    let calls = match result.calls.checked_add(1) {
                        Some(value) => value,
                        None => return None,
                    };
                    Some(GuidedReconstruction {
                        word: result.word,
                        table: result.table,
                        calls,
                    })
                }
            }
        },
    }
}

/// Maximum common indexed contraction using shared memoized feasibility and
/// guided reconstruction. The older reference entry point remains available.
pub fn maximum_common_embedding_indexed_guided(
    left: &BalancedWord,
    right: &BalancedWord,
) -> Option<IndexedCommonEmbedding> {
    let (matching, table) = memoized_common_embedding(left, right, MemoTable::Empty);
    let matching = match matching {
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
    let left_result = match reconstruct_guided(&matching.word, &left_input.word, table) {
        Some(value) => value,
        None => return None,
    };
    let left_word = match left_result.word {
        Some(value) => value,
        None => return None,
    };
    let right_result =
        match reconstruct_guided(&matching.word, &right_input.word, left_result.table) {
            Some(value) => value,
            None => return None,
        };
    let right_word = match right_result.word {
        Some(value) => value,
        None => return None,
    };
    Some(IndexedCommonEmbedding {
        left: left_word,
        right: right_word,
        edges: matching.edges,
    })
}
