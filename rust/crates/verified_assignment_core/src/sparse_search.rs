//! Reference alternating search using actual optional-edge cut steps.
//!
//! The cut/update primitive has a maintained source proof. Refinement of this
//! complete search and its subsequent path flip is developed separately. Each
//! cut is scanned from the matrix; this is not the paper's priority-queue cost.

use crate::{sparse::advance_sparse_cut, unused_columns, zeros_usize, AssignmentError};

pub struct SparseSearch {
    pub rows: Vec<i128>,
    pub columns: Vec<i128>,
    pub predecessor_row: Vec<usize>,
    /// Positive discovery order of each reached column; zero means unreached.
    pub discovery: Vec<usize>,
    pub target: usize,
    pub steps: usize,
}

/// Validate and invert a completed permutation, including the temporary edge.
fn inverse_completed(completed: &[usize]) -> Result<Vec<usize>, AssignmentError> {
    let n = completed.len();
    let mut inverse = zeros_usize(n);
    let mut seen = unused_columns(n);
    let mut failure = None;
    let mut row = 0;
    while row < n && failure.is_none() {
        let column = completed[row];
        if column >= n {
            failure = Some(AssignmentError::InvariantViolation);
        } else if seen[column] {
            failure = Some(AssignmentError::InvariantViolation);
        } else {
            seen[column] = true;
            inverse[column] = row;
        }
        row += 1;
    }
    match failure {
        Some(error) => Err(error),
        None => Ok(inverse),
    }
}

/// Find a tight augmenting path for a single missing assignment edge.
///
/// `completed` is a permutation whose root edge is temporary; all other edges
/// describe the actual partial assignment. Its free target is completed[root].
/// A valid seed has feasible duals and tight allowed edges at every other row.
/// The search preserves that matching and returns the path through predecessor
/// rows in original coordinates. Invalid dimensions, permutations, arithmetic
/// and exhausted/empty cuts produce explicit errors.
pub fn find_sparse_augmenting_path(
    cost: &[Vec<Option<i64>>],
    mut rows: Vec<i128>,
    mut columns: Vec<i128>,
    completed: &[usize],
    root: usize,
) -> Result<SparseSearch, AssignmentError> {
    let n = cost.len();
    if rows.len() != n || columns.len() != n || completed.len() != n {
        return Err(AssignmentError::NonSquare);
    }
    if n > u32::MAX as usize {
        return Err(AssignmentError::TooLarge);
    }
    if root >= n {
        return Err(AssignmentError::InvariantViolation);
    }
    let inverse = match inverse_completed(completed) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let target = completed[root];
    let mut selected_rows = unused_columns(n);
    let mut selected_columns = unused_columns(n);
    let mut predecessor_row = zeros_usize(n);
    let mut discovery = zeros_usize(n);
    selected_rows[root] = true;
    let mut steps = 0;
    let mut searching = true;
    let mut failure = None;
    while searching && failure.is_none() {
        if steps >= n {
            failure = Some(AssignmentError::InvariantViolation);
        }
        if failure.is_none() {
            steps += 1;
            match advance_sparse_cut(cost, &rows, &columns, &selected_rows, &selected_columns) {
                Err(error) => failure = Some(error),
                Ok(None) => failure = Some(AssignmentError::InvariantViolation),
                Ok(Some(step)) => {
                    let row = step.cut.row;
                    let column = step.cut.column;
                    predecessor_row[column] = row;
                    discovery[column] = steps;
                    rows = step.rows;
                    columns = step.columns;
                    if column == target {
                        searching = false;
                    } else {
                        selected_columns[column] = true;
                        selected_rows[inverse[column]] = true;
                    }
                }
            }
        }
    }
    match failure {
        Some(error) => Err(error),
        None => Ok(SparseSearch { rows, columns, predecessor_row, discovery, target, steps }),
    }
}
