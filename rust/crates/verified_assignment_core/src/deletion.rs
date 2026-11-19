//! Reference family of right-vertex-deleted exact matching instances.
//!
//! Surviving vertices retain their original matrix indices. Unmatched right
//! vertices reuse the original result. Matched deletions call the verified
//! reference solver again; this is not the paper's one-augmentation repair.

use crate::matching::{max_weight_partial_matching, MatchedPair, MatchingError, PartialMatching};

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
pub struct DeletionFamily {
    pub original: PartialMatching,
    /// Entry j solves the instance with all edges incident to right j forbidden.
    pub without_right: Vec<PartialMatching>,
}

fn uses_right(pairs: &[MatchedPair], right: usize) -> bool {
    let mut index = 0;
    while index < pairs.len() {
        if pairs[index].right == right {
            return true;
        }
        index += 1;
    }
    false
}

fn copy_matching(original: &PartialMatching) -> PartialMatching {
    let mut pairs = Vec::new();
    let mut index = 0;
    while index < original.pairs.len() {
        let pair = &original.pairs[index];
        pairs.push(MatchedPair {
            left: pair.left,
            right: pair.right,
        });
        index += 1;
    }
    PartialMatching {
        pairs,
        weight: original.weight,
    }
}

fn mask_row(row: &[Option<i64>], removed: usize) -> Vec<Option<i64>> {
    let mut result = Vec::new();
    let mut column = 0;
    while column < row.len() {
        if column == removed {
            result.push(None);
        } else {
            result.push(row[column]);
        }
        column += 1;
    }
    result
}

fn mask_right(weights: &[Vec<Option<i64>>], removed: usize) -> Vec<Vec<Option<i64>>> {
    let mut result = Vec::new();
    let mut row = 0;
    while row < weights.len() {
        result.push(mask_row(&weights[row], removed));
        row += 1;
    }
    result
}

/// Solve the original and every right-vertex-deleted instance exactly.
///
/// Empty sides, forbidden/signed weights, shape and size handling follow the
/// single-instance API. Output indices always refer to the original matrix.
/// This reference family reuses solutions for unmatched deletions and fully
/// recomputes each matched deletion. It makes no optimized runtime claim.
pub fn max_weight_matching_deletions(
    weights: &[Vec<Option<i64>>],
) -> Result<DeletionFamily, MatchingError> {
    let original = match max_weight_partial_matching(weights) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let right = if weights.len() == 0 {
        0
    } else {
        weights[0].len()
    };
    let mut without_right = Vec::new();
    let mut removed = 0;
    while removed < right {
        let result = if uses_right(&original.pairs, removed) {
            let masked = mask_right(weights, removed);
            match max_weight_partial_matching(&masked) {
                Ok(value) => value,
                Err(error) => return Err(error),
            }
        } else {
            copy_matching(&original)
        };
        without_right.push(result);
        removed += 1;
    }
    Ok(DeletionFamily {
        original,
        without_right,
    })
}

#[cfg(test)]
mod tests;
