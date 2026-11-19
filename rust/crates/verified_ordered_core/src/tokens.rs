//! Checked flat balanced-token input with exact original pair coordinates.
//!
//! `false` opens a pair and `true` closes it. Token kinds and external labels
//! are resolved by the caller; this core handles the unlabeled balanced grammar.

use crate::BalancedWord;

pub struct PairPositions {
    pub open: usize,
    pub close: usize,
}

pub struct ParsedForest {
    pub word: BalancedWord,
    pub next: usize,
    /// Original token coordinates in opening/preorder pair order.
    pub positions: Vec<PairPositions>,
}

pub enum TokenError {
    UnexpectedClose,
    MissingClose,
    TooLarge,
}

fn parse_forest(
    input: &[bool],
    start: usize,
    mut positions: Vec<PairPositions>,
) -> Result<ParsedForest, TokenError> {
    if start == input.len() {
        return Ok(ParsedForest {
            word: BalancedWord::Empty,
            next: start,
            positions,
        });
    }
    if input[start] {
        return Ok(ParsedForest {
            word: BalancedWord::Empty,
            next: start,
            positions,
        });
    }
    let pair_index = positions.len();
    if pair_index == u32::MAX as usize {
        return Err(TokenError::TooLarge);
    }
    positions.push(PairPositions {
        open: start,
        close: start,
    });
    let mut head = match parse_forest(input, start + 1, positions) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if head.next == input.len() {
        return Err(TokenError::MissingClose);
    }
    if !input[head.next] {
        return Err(TokenError::MissingClose);
    }
    head.positions[pair_index].close = head.next;
    let tail = match parse_forest(input, head.next + 1, head.positions) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(ParsedForest {
        word: BalancedWord::Pair(Box::new(head.word), Box::new(tail.word)),
        next: tail.next,
        positions: tail.positions,
    })
}

/// Parse a complete flat balanced word, retaining both original token
/// coordinates for every pair. Empty input is supported. Unmatched opening
/// and closing tokens, and an excluded u32 pair count, have explicit errors.
pub fn parse_balanced_tokens(input: &[bool]) -> Result<ParsedForest, TokenError> {
    let parsed = match parse_forest(input, 0, Vec::new()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if parsed.next != input.len() {
        return Err(TokenError::UnexpectedClose);
    }
    Ok(parsed)
}
