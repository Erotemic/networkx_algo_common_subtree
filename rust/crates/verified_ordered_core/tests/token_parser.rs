use verified_ordered_core::{
    tokens::{parse_balanced_tokens, TokenError},
    BalancedWord,
};

// Independent stack oracle records both positions while checking every prefix.
fn stack_pairs(tokens: &[bool]) -> Option<Vec<(usize, usize)>> {
    let mut stack: Vec<usize> = Vec::new();
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    for (index, closed) in tokens.iter().enumerate() {
        if *closed {
            let pair = stack.pop()?;
            pairs[pair] = (pairs[pair].0, index);
        } else {
            stack.push(pairs.len());
            pairs.push((index, index));
        }
    }
    if stack.is_empty() {
        Some(pairs)
    } else {
        None
    }
}

fn encoded(word: &BalancedWord) -> Vec<bool> {
    match word {
        BalancedWord::Empty => vec![],
        BalancedWord::Pair(head, tail) => {
            let mut result = vec![false];
            result.extend(encoded(head));
            result.push(true);
            result.extend(encoded(tail));
            result
        }
    }
}

#[test]
fn parser_matches_independent_stack_on_every_word_through_fourteen_tokens() {
    for size in 0..=14 {
        for code in 0..(1usize << size) {
            let tokens: Vec<bool> = (0..size).map(|bit| code & (1 << bit) != 0).collect();
            let expected = stack_pairs(&tokens);
            let result = parse_balanced_tokens(&tokens);
            match (expected, result) {
                (None, Err(_)) => {}
                (Some(expected), Ok(result)) => {
                    assert_eq!(result.next, tokens.len());
                    assert_eq!(encoded(&result.word), tokens);
                    let actual: Vec<_> = result
                        .positions
                        .iter()
                        .map(|pair| (pair.open, pair.close))
                        .collect();
                    assert_eq!(actual, expected);
                }
                _ => panic!("balance mismatch for {tokens:?}"),
            }
        }
    }
}

#[test]
fn explicit_unmatched_token_errors() {
    assert!(matches!(
        parse_balanced_tokens(&[true]),
        Err(TokenError::UnexpectedClose)
    ));
    assert!(matches!(
        parse_balanced_tokens(&[false]),
        Err(TokenError::MissingClose)
    ));
    assert!(matches!(
        parse_balanced_tokens(&[false, true, true]),
        Err(TokenError::UnexpectedClose)
    ));
    assert!(matches!(
        parse_balanced_tokens(&[false, false, true]),
        Err(TokenError::MissingClose)
    ));
}

#[test]
fn flat_token_adapter_preserves_input_error_side_and_precedence() {
    use verified_ordered_core::token_matching::{
        maximum_common_token_embedding, TokenMatchingError,
    };
    assert!(matches!(
        maximum_common_token_embedding(&[true], &[false]),
        Err(TokenMatchingError::LeftInput(TokenError::UnexpectedClose))
    ));
    assert!(matches!(
        maximum_common_token_embedding(&[false, true], &[false]),
        Err(TokenMatchingError::RightInput(TokenError::MissingClose))
    ));
    assert!(
        matches!(maximum_common_token_embedding(&[], &[]), Ok(result) if result.left.is_empty() && result.right.is_empty() && result.edges == 0)
    );
}

#[test]
fn isomorphism_indices_preserve_parents_and_original_occurrences() {
    use verified_ordered_core::token_matching::maximum_common_token_isomorphism;
    let left = [false, false, true, false, true, true];
    let right = [false, true, false, true];
    let general = maximum_common_token_isomorphism(&left, &right, false)
        .ok()
        .unwrap();
    assert_eq!(general.left, vec![1, 2, 3, 4]);
    assert_eq!(general.right, vec![0, 1, 2, 3]);
    assert_eq!(general.edges, 2);
    let rooted = maximum_common_token_isomorphism(&left, &right, true)
        .ok()
        .unwrap();
    assert_eq!(rooted.left, vec![0, 5]);
    assert_eq!(rooted.edges, 1);
    let repeated =
        maximum_common_token_isomorphism(&[false, false, true, true, false, true], &right, true)
            .ok()
            .unwrap();
    assert_eq!(repeated.left, vec![0, 3, 4, 5]);
    assert_eq!(repeated.edges, 2);
}

#[test]
fn isomorphism_token_errors_preserve_sides_even_for_empty_inputs() {
    use verified_ordered_core::token_matching::{
        maximum_common_token_isomorphism, TokenMatchingError,
    };
    for rooted in [false, true] {
        assert!(matches!(
            maximum_common_token_isomorphism(&[true], &[], rooted),
            Err(TokenMatchingError::LeftInput(TokenError::UnexpectedClose))
        ));
        assert!(matches!(
            maximum_common_token_isomorphism(&[], &[false], rooted),
            Err(TokenMatchingError::RightInput(TokenError::MissingClose))
        ));
        assert!(matches!(maximum_common_token_isomorphism(&[], &[], rooted),
                         Ok(r) if r.edges == 0 && r.left.is_empty() && r.right.is_empty()));
    }
}
