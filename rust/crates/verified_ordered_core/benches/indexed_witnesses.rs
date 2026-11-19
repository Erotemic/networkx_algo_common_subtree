use std::time::Instant;
use verified_ordered_core::{
    copy_word,
    guided::{maximum_common_embedding_indexed_guided, reconstruct_guided},
    indexed::{maximum_common_embedding_indexed, number_word},
    memoized_common_embedding, BalancedWord, MemoTable,
};

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
        BalancedWord::Empty
    } else {
        let first = balanced(levels - 1);
        BalancedWord::Pair(
            Box::new(copy_word(&first)),
            Box::new(BalancedWord::Pair(
                Box::new(first),
                Box::new(BalancedWord::Empty),
            )),
        )
    }
}

fn broom(handle: usize, leaves: usize) -> BalancedWord {
    if handle == 0 {
        star(leaves)
    } else {
        BalancedWord::Pair(
            Box::new(broom(handle - 1, leaves)),
            Box::new(BalancedWord::Empty),
        )
    }
}

fn caterpillar(levels: usize) -> BalancedWord {
    if levels == 0 {
        BalancedWord::Empty
    } else {
        BalancedWord::Pair(Box::new(caterpillar(levels - 1)), Box::new(star(1)))
    }
}

fn edges(word: &BalancedWord) -> usize {
    match word {
        BalancedWord::Empty => 0,
        BalancedWord::Pair(head, tail) => 1 + edges(head) + edges(tail),
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

fn inputs(name: &str) -> (BalancedWord, BalancedWord) {
    match name {
        "chain12" => (chain(12), chain(12)),
        "chain24" => (chain(24), chain(24)),
        "chain48" => (chain(48), chain(48)),
        "star24" => (star(24), star(24)),
        "chain_star24" => (chain(24), star(24)),
        "binary4" => (balanced(4), balanced(4)),
        "binary5" => (balanced(5), balanced(5)),
        "broom24" => (broom(12, 12), broom(12, 12)),
        "caterpillar24" => (caterpillar(12), caterpillar(12)),
        "unequal_chain_star" => (chain(12), star(24)),
        _ => panic!("unknown case"),
    }
}

fn sample(name: &str, mode: &str, measured: bool) {
    let (left, right) = inputs(name);
    let left_edges = edges(&left);
    let right_edges = edges(&right);
    let (seconds, score, calls, initial_states, final_states) = match mode {
        "reference" | "guided" => {
            let start = Instant::now();
            let result = if mode == "reference" {
                maximum_common_embedding_indexed(&left, &right)
            } else {
                maximum_common_embedding_indexed_guided(&left, &right)
            }
            .expect("benchmark score fits");
            let elapsed = start.elapsed().as_secs_f64();
            std::hint::black_box(&result);
            (elapsed, result.edges, None, None, None)
        }
        "witness" => {
            let (matching, table) = memoized_common_embedding(&left, &right, MemoTable::Empty);
            let matching = matching.expect("benchmark score fits");
            let left_input = number_word(&left, 0).expect("benchmark numbering fits");
            let right_input = number_word(&right, 0).expect("benchmark numbering fits");
            let initial_states = table_size(&table);
            let start = Instant::now();
            let left_result = reconstruct_guided(&matching.word, &left_input.word, table)
                .expect("benchmark reconstruction fits");
            let right_result =
                reconstruct_guided(&matching.word, &right_input.word, left_result.table)
                    .expect("benchmark reconstruction fits");
            let elapsed = start.elapsed().as_secs_f64();
            assert!(left_result.word.is_some() && right_result.word.is_some());
            std::hint::black_box((&left_result.word, &right_result.word));
            (
                elapsed,
                matching.edges,
                Some(left_result.calls + right_result.calls),
                Some(initial_states),
                Some(table_size(&right_result.table)),
            )
        }
        _ => panic!("unknown mode"),
    };
    if measured {
        println!(
            "{name},{mode},{left_edges},{right_edges},{seconds:.9},{score},{},{},{}",
            calls.map(|v| v.to_string()).unwrap_or_default(),
            initial_states.map(|v| v.to_string()).unwrap_or_default(),
            final_states.map(|v| v.to_string()).unwrap_or_default()
        );
    }
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let name = args.get(1).expect("case argument");
    let mode = args.get(2).expect("mode argument");
    sample(name, mode, false);
    println!(
        "case,mode,left_edges,right_edges,seconds,score,witness_calls,initial_states,final_states"
    );
    for _ in 0..5 {
        sample(name, mode, true);
    }
}
