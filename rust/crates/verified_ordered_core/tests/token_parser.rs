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
