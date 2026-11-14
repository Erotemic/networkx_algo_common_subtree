//! Exact signed partial matching through the verified square assignment core.

use crate::min_cost_assignment;

#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub struct MatchedPair {
    pub left: usize,
    pub right: usize,
}

#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub struct PartialMatching {
    pub pairs: Vec<MatchedPair>,
    pub weight: i128,
}

#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub enum MatchingError {
    NonRectangular,
    TooLarge,
    AssignmentFailure,
    ArithmeticOverflow,
}

fn is_rectangular(weights: &[Vec<Option<i64>>], right: usize) -> bool {
    let mut row = 0;
    while row < weights.len() {
        if weights[row].len() != right {
            return false;
        }
        row += 1;
    }
    true
}

fn negative_profit(weight: Option<i64>) -> i64 {
    match weight {
        Some(value) => {
            if value > 0 {
                -value
            } else {
                0
            }
        }
        None => 0,
    }
}

fn cost_cell(weights: &[Vec<Option<i64>>], left: usize, row: usize, column: usize) -> i64 {
    if row < left && column >= left {
        negative_profit(weights[row][column - left])
    } else {
        0
    }
}

// Indices are Fin(left) + Fin(right): real left rows precede dummy rows,
// and real right columns follow the reserved left-column block.
fn cost_row(weights: &[Vec<Option<i64>>], left: usize, dimension: usize, row: usize) -> Vec<i64> {
    let mut result = Vec::new();
    let mut column = 0;
    while column < dimension {
        result.push(cost_cell(weights, left, row, column));
        column += 1;
    }
    result
}

fn cost_matrix(weights: &[Vec<Option<i64>>], left: usize, dimension: usize) -> Vec<Vec<i64>> {
    let mut result = Vec::new();
    let mut row = 0;
    while row < dimension {
        result.push(cost_row(weights, left, dimension, row));
        row += 1;
    }
    result
}

fn decode_pairs(
    weights: &[Vec<Option<i64>>],
    left: usize,
    right: usize,
    columns: &[usize],
) -> Vec<MatchedPair> {
    let mut pairs = Vec::new();
    let mut row = 0;
    while row < left {
        let column = columns[row];
        if column >= left {
            let target = column - left;
            if target < right {
                match weights[row][target] {
                    Some(weight) => {
                        if weight > 0 {
                            pairs.push(MatchedPair {
                                left: row,
                                right: target,
                            });
                        }
                    }
                    None => {}
                }
            }
        }
        row += 1;
    }
    pairs
}

fn solve_built_matrix(
    weights: &[Vec<Option<i64>>],
    left: usize,
    right: usize,
    cost: &[Vec<i64>],
) -> Result<PartialMatching, MatchingError> {
    match min_cost_assignment(cost) {
        Err(_) => Err(MatchingError::AssignmentFailure),
        Ok(assignment) => {
            let pairs = decode_pairs(weights, left, right, &assignment.column_for_row);
            match 0i128.checked_sub(assignment.cost) {
                Some(weight) => Ok(PartialMatching { pairs, weight }),
                None => Err(MatchingError::ArithmeticOverflow),
            }
        }
    }
}

/// Globally maximum-weight compatible partial matching of a rectangular matrix.
///
/// `None` forbids an edge. Zero and negative edges may be left unmatched; the
/// returned witness contains only positive edges. Empty sides are supported.
/// Shape and combined-dimension errors are explicit. The square reduction uses
/// one dummy row/column per original vertex and makes no optimized-cost claim.
pub fn max_weight_partial_matching(
    weights: &[Vec<Option<i64>>],
) -> Result<PartialMatching, MatchingError> {
    let left = weights.len();
    let right = if left == 0 { 0 } else { weights[0].len() };
    if !is_rectangular(weights, right) {
        return Err(MatchingError::NonRectangular);
    }
    let dimension = match left.checked_add(right) {
        Some(value) => value,
        None => return Err(MatchingError::TooLarge),
    };
    if dimension > u32::MAX as usize || dimension == usize::MAX {
        return Err(MatchingError::TooLarge);
    }
    let cost = cost_matrix(weights, left, dimension);
    solve_built_matrix(weights, left, right, &cost)
}

#[cfg(test)]
mod tests;
