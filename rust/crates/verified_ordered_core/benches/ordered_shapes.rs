use std::time::Instant;
use verified_ordered_core::{copy_word, memoized_common_embedding, BalancedWord, MemoTable};

fn chain(edges: usize) -> BalancedWord {
    if edges == 0 {
        BalancedWord::Empty
    } else {
        BalancedWord::Pair(Box::new(chain(edges - 1)), Box::new(BalancedWord::Empty))
    }
}

fn star(edges: usize) -> BalancedWord {
    if edges == 0 {
        BalancedWord::Empty
    } else {
        BalancedWord::Pair(Box::new(BalancedWord::Empty), Box::new(star(edges - 1)))
    }
}

fn balanced(levels: usize) -> BalancedWord {
    if levels == 0 {
        return BalancedWord::Empty;
    }
    let subtree = balanced(levels - 1);
    BalancedWord::Pair(
        Box::new(copy_word(&subtree)),
        Box::new(BalancedWord::Pair(
            Box::new(subtree),
            Box::new(BalancedWord::Empty),
        )),
    )
}

fn edge_count(word: &BalancedWord) -> usize {
    match word {
        BalancedWord::Empty => 0,
        BalancedWord::Pair(h, t) => 1 + edge_count(h) + edge_count(t),
    }
}

fn table_size(table: &MemoTable) -> usize {
    let mut current = table;
    let mut count = 0;
    while let MemoTable::Entry(_, rest) = current {
        count += 1;
        current = rest;
    }
    count
}

fn main() {
    let cases = vec![
        ("chain12", chain(12), chain(12)),
        ("chain24", chain(24), chain(24)),
        ("star24", star(24), star(24)),
        ("chain_star24", chain(24), star(24)),
        ("balanced_height4", balanced(4), balanced(4)),
        ("balanced_height5", balanced(5), balanced(5)),
    ];
    println!("case,left_edges,right_edges,seconds,score,cache_entries");
    for (name, left, right) in cases {
        let start = Instant::now();
        let (result, table) = memoized_common_embedding(&left, &right, MemoTable::Empty);
        let elapsed = start.elapsed().as_secs_f64();
        let result = result.expect("benchmark scores fit u32");
        println!(
            "{name},{},{},{elapsed:.9},{},{}",
            edge_count(&left),
            edge_count(&right),
            result.edges,
            table_size(&table)
        );
    }
}
