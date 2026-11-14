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

// Enumerate ordered adjacency-preserving selections in actual trees. A skipped
// child contributes nothing; its descendants are never promoted into siblings.
fn rooted_prunings(tree: &Tree) -> BTreeSet<Vec<u8>> {
    fn select_children(children: &[Tree]) -> Vec<Vec<Tree>> {
        match children.split_first() {
            None => vec![vec![]],
            Some((first, tail)) => {
                let suffixes = select_children(tail);
                let mut out = suffixes.clone();
                for child in select_children(&first.0) {
                    for suffix in &suffixes {
                        let mut kept = vec![Tree(child.clone())];
                        kept.extend_from_slice(suffix);
                        out.push(kept);
                    }
                }
                out
            }
        }
    }
    select_children(&tree.0)
        .into_iter()
        .map(|children| tree_encoding(&Tree(children)))
        .collect()
}

fn subtree_prunings(tree: &Tree) -> BTreeSet<Vec<u8>> {
    let mut out = rooted_prunings(tree);
    for child in &tree.0 {
        out.extend(subtree_prunings(child));
    }
    out
}

#[test]
fn isomorphism_matches_independent_tree_selections_through_six_edges() {
    use verified_ordered_core::isomorphism::{
        largest_common_isomorphism, rooted_common_isomorphism,
    };
    let inputs: Vec<_> = (0..=6).flat_map(trees).collect();
    assert_eq!(inputs.len(), 197);
    let rooted: Vec<_> = inputs.iter().map(rooted_prunings).collect();
    let anywhere: Vec<_> = inputs.iter().map(subtree_prunings).collect();
    for (i, left) in inputs.iter().enumerate() {
        for (j, right) in inputs.iter().enumerate() {
            for (candidates, solve) in [
                (
                    &rooted,
                    rooted_common_isomorphism
                        as fn(
                            &BalancedWord,
                            &BalancedWord,
                        )
                            -> Option<verified_ordered_core::CommonEmbedding>,
                ),
                (
                    &anywhere,
                    largest_common_isomorphism
                        as fn(
                            &BalancedWord,
                            &BalancedWord,
                        )
                            -> Option<verified_ordered_core::CommonEmbedding>,
                ),
            ] {
                let expected = candidates[i]
                    .intersection(&candidates[j])
                    .map(|word| word.len() / 2)
                    .max()
                    .unwrap();
                let result: verified_ordered_core::CommonEmbedding =
                    solve(&as_word(&left.0), &as_word(&right.0)).expect("tiny scores fit u32");
                let witness = word_encoding(&result.word);
                assert_eq!(result.edges as usize, expected, "pair {i}, {j}");
                assert_eq!(witness.len() / 2, expected);
                assert!(candidates[i].contains(&witness));
                assert!(candidates[j].contains(&witness));
            }
        }
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
struct TaggedEdge {
    original: u32,
    children: Vec<TaggedEdge>,
}

fn tag_original(forest: &[Tree], next: &mut u32) -> Vec<TaggedEdge> {
    forest
        .iter()
        .map(|child| {
            let original = *next;
            *next += 1;
            TaggedEdge {
                original,
                children: tag_original(&child.0, next),
            }
        })
        .collect()
}

fn tagged_output(word: &verified_ordered_core::indexed::IndexedWord) -> Vec<TaggedEdge> {
    use verified_ordered_core::indexed::IndexedWord;
    match word {
        IndexedWord::Empty => vec![],
        IndexedWord::Pair(index, head, tail) => {
            let mut result = vec![TaggedEdge {
                original: *index,
                children: tagged_output(head),
            }];
            result.extend(tagged_output(tail));
            result
        }
    }
}

fn strip_tags(forest: &[TaggedEdge]) -> Tree {
    Tree(
        forest
            .iter()
            .map(|child| strip_tags(&child.children))
            .collect(),
    )
}

// Independently contract every possible actual parent-child edge, preserving
// each remaining edge's original identity. No first-return search is used.
fn contract_tagged_once(forest: &[TaggedEdge]) -> Vec<Vec<TaggedEdge>> {
    let mut result = Vec::new();
    for (index, child) in forest.iter().enumerate() {
        let mut spliced = forest[..index].to_vec();
        spliced.extend_from_slice(&child.children);
        spliced.extend_from_slice(&forest[index + 1..]);
        result.push(spliced);
        for smaller in contract_tagged_once(&child.children) {
            let mut changed = forest.to_vec();
            changed[index].children = smaller;
            result.push(changed);
        }
    }
    result
}

fn tagged_closure(original: &[TaggedEdge]) -> BTreeSet<Vec<TaggedEdge>> {
    let mut result = BTreeSet::from([original.to_vec()]);
    let mut pending = vec![original.to_vec()];
    while let Some(current) = pending.pop() {
        for smaller in contract_tagged_once(&current) {
            if result.insert(smaller.clone()) {
                pending.push(smaller);
            }
        }
    }
    result
}

#[test]
fn indexed_witnesses_match_independent_labeled_contractions_through_six_edges() {
    use verified_ordered_core::indexed::{
        maximum_common_embedding_indexed, number_word, reconstruct_embedding,
    };
    let inputs: Vec<_> = (0..=6).flat_map(trees).collect();
    let numbered: Vec<_> = inputs
        .iter()
        .map(|tree| tag_original(&tree.0, &mut 0))
        .collect();
    let candidates: Vec<_> = numbered
        .iter()
        .map(|forest| tagged_closure(forest))
        .collect();
    let shapes: Vec<BTreeSet<Vec<u8>>> = candidates
        .iter()
        .map(|choices| {
            choices
                .iter()
                .map(|forest| tree_encoding(&strip_tags(forest)))
                .collect()
        })
        .collect();
    for (i, input) in inputs.iter().enumerate() {
        let word = as_word(&input.0);
        let indexed = number_word(&word, 0).expect("tiny input numbering fits");
        assert!(tagged_output(&indexed.word) == numbered[i]);
        assert_eq!(indexed.next as usize, tree_encoding(input).len() / 2);
        for (j, other) in inputs.iter().enumerate() {
            let pattern = as_word(&other.0);
            let witness = reconstruct_embedding(&pattern, &indexed.word);
            let guided = verified_ordered_core::guided::reconstruct_guided(
                &pattern,
                &indexed.word,
                verified_ordered_core::MemoTable::Empty,
            )
            .expect("tiny guided reconstruction fits");
            assert!(guided.calls <= 2 * indexed.next as u64 + 1);
            assert!(guided.word.as_ref().map(tagged_output) == witness.as_ref().map(tagged_output));
            assert_eq!(
                witness.is_some(),
                shapes[i].contains(&tree_encoding(other)),
                "pattern {j}, input {i}"
            );
            if let Some(witness) = witness {
                let kept = tagged_output(&witness);
                assert!(candidates[i].contains(&kept));
                assert!(strip_tags(&kept) == *other);
            }
            let common =
                maximum_common_embedding_indexed(&word, &pattern).expect("tiny indexed scores fit");
            let guided_common =
                verified_ordered_core::guided::maximum_common_embedding_indexed_guided(
                    &word, &pattern,
                )
                .expect("tiny guided indexed scores fit");
            assert_eq!(guided_common.edges, common.edges);
            assert!(tagged_output(&guided_common.left) == tagged_output(&common.left));
            assert!(tagged_output(&guided_common.right) == tagged_output(&common.right));
            let left = tagged_output(&common.left);
            let right = tagged_output(&common.right);
            assert!(candidates[i].contains(&left));
            assert!(candidates[j].contains(&right));
            assert!(strip_tags(&left) == strip_tags(&right));
            let expected = shapes[i]
                .intersection(&shapes[j])
                .map(|shape| shape.len() / 2)
                .max()
                .unwrap();
            assert_eq!(common.edges as usize, expected);
            assert_eq!(tree_encoding(&strip_tags(&left)).len() / 2, expected);
        }
    }
}

#[test]
fn indexed_numbering_checks_offset_overflow() {
    use verified_ordered_core::indexed::number_word;
    let one = BalancedWord::Pair(Box::new(BalancedWord::Empty), Box::new(BalancedWord::Empty));
    assert!(number_word(&one, u32::MAX).is_none());
    let result = number_word(&one, u32::MAX - 1).unwrap();
    assert_eq!(result.next, u32::MAX);
    assert_eq!(tagged_output(&result.word)[0].original, u32::MAX - 1);
    assert_eq!(
        number_word(&BalancedWord::Empty, u32::MAX).unwrap().next,
        u32::MAX
    );
}

#[test]
fn flat_token_adapter_matches_independent_tree_contractions_through_six_edges() {
    use verified_ordered_core::token_matching::maximum_common_token_embedding;
    let inputs: Vec<_> = (0..=6).flat_map(trees).collect();
    let words: Vec<Vec<bool>> = inputs
        .iter()
        .map(|tree| {
            tree_encoding(tree)
                .into_iter()
                .map(|token| token != 0)
                .collect()
        })
        .collect();
    let candidates: Vec<_> = inputs.iter().map(closure).collect();
    for i in 0..inputs.len() {
        for j in 0..inputs.len() {
            let result = match maximum_common_token_embedding(&words[i], &words[j]) {
                Ok(value) => value,
                Err(_) => panic!("tiny valid input rejected: {i}, {j}"),
            };
            assert!(result.left.windows(2).all(|pair| pair[0] < pair[1]));
            assert!(result.right.windows(2).all(|pair| pair[0] < pair[1]));
            let left: Vec<_> = result
                .left
                .iter()
                .map(|index| words[i][*index] as u8)
                .collect();
            let right: Vec<_> = result
                .right
                .iter()
                .map(|index| words[j][*index] as u8)
                .collect();
            assert_eq!(left, right);
            assert!(candidates[i].contains(&left));
            assert!(candidates[j].contains(&right));
            let expected = candidates[i]
                .intersection(&candidates[j])
                .map(|word| word.len() / 2)
                .max()
                .unwrap();
            assert_eq!(result.edges as usize, expected);
            assert_eq!(result.left.len(), 2 * expected);
            assert_eq!(result.right.len(), 2 * expected);
        }
    }
}
