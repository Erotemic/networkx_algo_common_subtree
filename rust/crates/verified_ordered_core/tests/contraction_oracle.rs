use std::collections::BTreeSet;
use verified_ordered_core::{largest_common_embedding, maximum_common_embedding, BalancedWord};

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
struct Tree(Vec<Tree>);

fn trees(edges: usize) -> Vec<Tree> {
    forests(edges).into_iter().map(Tree).collect()
}

fn forests(edges: usize) -> Vec<Vec<Tree>> {
    if edges == 0 {
        return vec![vec![]];
    }
    let mut out = Vec::new();
    for first in 0..edges {
        for tree in trees(first) {
            for rest in forests(edges - first - 1) {
                let mut children = vec![tree.clone()];
                children.extend(rest);
                out.push(children);
            }
        }
    }
    out
}

// Enumerate parent-child contractions directly in ordered trees. This code
// knows nothing about balanced first-return recurrence branches.
fn contract_once(tree: &Tree) -> Vec<Tree> {
    let mut out = Vec::new();
    for (index, child) in tree.0.iter().enumerate() {
        let mut spliced = tree.0[..index].to_vec();
        spliced.extend(child.0.clone());
        spliced.extend_from_slice(&tree.0[index + 1..]);
        out.push(Tree(spliced));
        for smaller in contract_once(child) {
            let mut changed = tree.0.clone();
            changed[index] = smaller;
            out.push(Tree(changed));
        }
    }
    out
}

fn closure(tree: &Tree) -> BTreeSet<Vec<u8>> {
    let mut seen = BTreeSet::from([tree.clone()]);
    let mut pending = vec![tree.clone()];
    while let Some(current) = pending.pop() {
        for smaller in contract_once(&current) {
            if seen.insert(smaller.clone()) {
                pending.push(smaller);
            }
        }
    }
    seen.iter().map(tree_encoding).collect()
}

fn tree_encoding(tree: &Tree) -> Vec<u8> {
    let mut out = Vec::new();
    for child in &tree.0 {
        out.push(0);
        out.extend(tree_encoding(child));
        out.push(1);
    }
    out
}

fn as_word(forest: &[Tree]) -> BalancedWord {
    match forest.split_first() {
        None => BalancedWord::Empty,
        Some((head, tail)) => {
            BalancedWord::Pair(Box::new(as_word(&head.0)), Box::new(as_word(tail)))
        }
    }
}

fn word_encoding(word: &BalancedWord) -> Vec<u8> {
    match word {
        BalancedWord::Empty => vec![],
        BalancedWord::Pair(head, tail) => {
            let mut out = vec![0];
            out.extend(word_encoding(head));
            out.push(1);
            out.extend(word_encoding(tail));
            out
        }
    }
}

#[test]
fn solver_matches_independent_tree_contractions_through_six_edges() {
    let inputs: Vec<_> = (0..=6).flat_map(trees).collect();
    assert_eq!(inputs.len(), 197);
    let candidates: Vec<_> = inputs.iter().map(closure).collect();
    for (i, left) in inputs.iter().enumerate() {
        for (j, right) in inputs.iter().enumerate() {
            let expected = candidates[i]
                .intersection(&candidates[j])
                .map(|word| word.len() / 2)
                .max()
                .unwrap();
            let result = largest_common_embedding(&as_word(&left.0), &as_word(&right.0))
                .expect("tiny scores fit u32");
            let memoized = maximum_common_embedding(&as_word(&left.0), &as_word(&right.0))
                .expect("tiny memoized scores fit u32");
            assert_eq!(memoized.edges, result.edges);
            assert_eq!(word_encoding(&memoized.word), word_encoding(&result.word));
            let witness = word_encoding(&result.word);
            assert_eq!(result.edges as usize, expected, "pair {i}, {j}");
            assert_eq!(witness.len() / 2, expected);
            assert!(candidates[i].contains(&witness));
            assert!(candidates[j].contains(&witness));
        }
    }
}
