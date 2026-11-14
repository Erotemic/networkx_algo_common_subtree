//! Flat-token reference adapter for the verified indexed contraction solver.

use crate::{
    indexed::{maximum_common_embedding_indexed, IndexedWord},
    tokens::{parse_balanced_tokens, PairPositions, TokenError},
};

pub enum TokenMatchingError {
    LeftInput(TokenError),
    RightInput(TokenError),
    SolverFailure,
    InvalidIndex,
}

pub struct TokenCommonEmbedding {
    pub left: Vec<usize>,
    pub right: Vec<usize>,
    pub edges: u32,
}

fn emit_tokens(
    word: &IndexedWord,
    coordinates: &[PairPositions],
    mut output: Vec<usize>,
) -> Result<Vec<usize>, TokenMatchingError> {
    match word {
        IndexedWord::Empty => Ok(output),
        IndexedWord::Pair(index, head, tail) => {
            let pair = *index as usize;
            if pair >= coordinates.len() {
                return Err(TokenMatchingError::InvalidIndex);
            }
            let opening = coordinates[pair].open;
            let closing = coordinates[pair].close;
            output.push(opening);
            let mut output = match emit_tokens(head, coordinates, output) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            output.push(closing);
            emit_tokens(tail, coordinates, output)
        }
    }
}

/// Maximum common balanced contraction with exact original token positions.
///
/// The typed alphabet uses false for opening and true for closing. Returns
/// both original token-index lists and the exact pair/edge score. The matching
/// is unweighted, with explicit malformed/oversized input errors. This remains
/// a reference adapter with backtracking reconstruction, without a paper cost
/// claim. External token kinds and labels are handled by a separate caller.
pub fn maximum_common_token_embedding(
    left: &[bool],
    right: &[bool],
) -> Result<TokenCommonEmbedding, TokenMatchingError> {
    let left_input = match parse_balanced_tokens(left) {
        Ok(value) => value,
        Err(error) => return Err(TokenMatchingError::LeftInput(error)),
    };
    let right_input = match parse_balanced_tokens(right) {
        Ok(value) => value,
        Err(error) => return Err(TokenMatchingError::RightInput(error)),
    };
    let matching = match maximum_common_embedding_indexed(&left_input.word, &right_input.word) {
        Some(value) => value,
        None => return Err(TokenMatchingError::SolverFailure),
    };
    let left_tokens = match emit_tokens(&matching.left, &left_input.positions, Vec::new()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let right_tokens = match emit_tokens(&matching.right, &right_input.positions, Vec::new()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(TokenCommonEmbedding {
        left: left_tokens,
        right: right_tokens,
        edges: matching.edges,
    })
}
