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

/// Structural equality, kept explicit for translation and key refinement.
pub fn words_equal(first: &BalancedWord, second: &BalancedWord) -> bool {
    match (first, second) {
        (BalancedWord::Empty, BalancedWord::Empty) => true,
        (BalancedWord::Pair(fh, ft), BalancedWord::Pair(sh, st)) => {
            words_equal(fh, sh) && words_equal(ft, st)
        }
        _ => false,
    }
}

pub fn copy_result(result: &CommonEmbedding) -> CommonEmbedding {
    CommonEmbedding {
        word: copy_word(&result.word),
        edges: result.edges,
    }
}

pub struct MemoEntry {
    pub left: BalancedWord,
    pub right: BalancedWord,
    pub result: CommonEmbedding,
}

/// Extraction-friendly owned association list. Its linear lookup cost is
/// explicit; the independently verified Lean memo model uses the same order.
pub enum MemoTable {
    Empty,
    Entry(Box<MemoEntry>, Box<MemoTable>),
}

pub fn memo_lookup(
    table: &MemoTable,
    left: &BalancedWord,
    right: &BalancedWord,
) -> Option<CommonEmbedding> {
    match table {
        MemoTable::Empty => None,
        MemoTable::Entry(entry, rest) => {
            if words_equal(left, &entry.left) && words_equal(right, &entry.right) {
                Some(copy_result(&entry.result))
            } else {
                memo_lookup(rest, left, right)
            }
        }
    }
}

pub fn memo_insert(
    table: MemoTable,
    left: &BalancedWord,
    right: &BalancedWord,
    result: &CommonEmbedding,
) -> MemoTable {
    MemoTable::Entry(
        Box::new(MemoEntry {
            left: copy_word(left),
            right: copy_word(right),
            result: copy_result(result),
        }),
        Box::new(table),
    )
}

/// Threaded memoized solver. Returning the owned table makes every state update
/// explicit without relying on a model of a third-party hash table.
pub fn memoized_common_embedding(
    left: &BalancedWord,
    right: &BalancedWord,
    table: MemoTable,
) -> (Option<CommonEmbedding>, MemoTable) {
    if let Some(result) = memo_lookup(&table, left, right) {
        return (Some(result), table);
    }
    match (left, right) {
        (BalancedWord::Empty, _) | (_, BalancedWord::Empty) => {
            let result = CommonEmbedding {
                word: BalancedWord::Empty,
                edges: 0,
            };
            let table = memo_insert(table, left, right, &result);
            (Some(result), table)
        }
        (BalancedWord::Pair(lh, lt), BalancedWord::Pair(rh, rt)) => {
            let (heads, table) = memoized_common_embedding(lh, rh, table);
            let heads = match heads {
                Some(value) => value,
                None => return (None, table),
            };
            let (tails, table) = memoized_common_embedding(lt, rt, table);
            let tails = match tails {
                Some(value) => value,
                None => return (None, table),
            };
            let subtotal = match heads.edges.checked_add(tails.edges) {
                Some(value) => value,
                None => return (None, table),
            };
            let edges = match subtotal.checked_add(1) {
                Some(value) => value,
                None => return (None, table),
            };
            let matched = CommonEmbedding {
                word: BalancedWord::Pair(Box::new(heads.word), Box::new(tails.word)),
                edges,
            };
            let contracted_left = concatenate(lh, lt);
            let (drop_left, table) = memoized_common_embedding(&contracted_left, right, table);
            let drop_left = match drop_left {
                Some(value) => value,
                None => return (None, table),
            };
            let contracted_right = concatenate(rh, rt);
            let (drop_right, table) = memoized_common_embedding(left, &contracted_right, table);
            let drop_right = match drop_right {
                Some(value) => value,
                None => return (None, table),
            };
            let result = choose_longer(choose_longer(matched, drop_left), drop_right);
            let table = memo_insert(table, left, right, &result);
            (Some(result), table)
        }
    }
}

/// Memoized entry point with an initially empty table.
pub fn maximum_common_embedding(
    left: &BalancedWord,
    right: &BalancedWord,
) -> Option<CommonEmbedding> {
    memoized_common_embedding(left, right, MemoTable::Empty).0
}

pub mod isomorphism;

pub mod indexed;

pub mod tokens;

pub mod token_matching;

pub mod guided;
