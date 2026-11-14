//! Reference alternating search using actual optional-edge cut steps.
//!
//! The complete search, path flip and one-path augmentation have maintained
//! source proofs. Each
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

pub struct SparseAugmentation {
    pub column_for_row: Vec<usize>,
    pub search: SparseSearch,
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

fn copy_indices(values: &[usize]) -> Vec<usize> {
    let mut result = Vec::new();
    let mut index = 0;
    while index < values.len() {
        result.push(values[index]);
        index += 1;
    }
    result
}

/// Flip a ranked predecessor path, retaining all original coordinates.
///
/// The completed input is a permutation with a temporary root-to-target edge.
/// Every nonroot predecessor follows its old assignment column with a strictly
/// smaller positive discovery rank. Other rows retain their old assignment.
/// Shape, root/target, predecessor, parent and rank checks reject malformed
/// paths. The sparse search supplies the allowed/tight-edge certificate.
pub fn flip_sparse_path(
    completed: &[usize],
    predecessor_row: &[usize],
    discovery: &[usize],
    root: usize,
    target: usize,
) -> Result<Vec<usize>, AssignmentError> {
    let n = completed.len();
    if predecessor_row.len() != n || discovery.len() != n {
        return Err(AssignmentError::NonSquare);
    }
    if n > u32::MAX as usize {
        return Err(AssignmentError::TooLarge);
    }
    if root >= n || target >= n {
        return Err(AssignmentError::InvariantViolation);
    }
    if completed[root] != target {
        return Err(AssignmentError::InvariantViolation);
    }
    let mut assignment = copy_indices(completed);
    let mut column = target;
    let mut path_length = 0;
    let mut finished = false;
    let mut failure = None;
    while !finished && failure.is_none() {
        if path_length >= n {
            failure = Some(AssignmentError::InvariantViolation);
        }
        if failure.is_none() {
            path_length += 1;
            let row = predecessor_row[column];
            if row >= n || discovery[column] == 0 {
                failure = Some(AssignmentError::InvariantViolation);
            } else {
                assignment[row] = column;
                if row == root {
                    finished = true;
                } else {
                    let parent = completed[row];
                    if parent >= n {
                        failure = Some(AssignmentError::InvariantViolation);
                    } else if discovery[parent] == 0 || discovery[parent] >= discovery[column] {
                        failure = Some(AssignmentError::InvariantViolation);
                    } else {
                        column = parent;
                    }
                }
            }
        }
    }
    match failure {
        Some(error) => Err(error),
        None => Ok(assignment),
    }
}

/// Reference one-path augmentation of a feasible tight single-deficit seed.
/// Maintained source proofs cover search, path flipping, original indices and
/// independent optimality. Full-matrix cut scans have no optimized cost claim.
pub fn augment_sparse_permutation(
    cost: &[Vec<Option<i64>>],
    rows: Vec<i128>,
    columns: Vec<i128>,
    completed: &[usize],
    root: usize,
) -> Result<SparseAugmentation, AssignmentError> {
    let search = match find_sparse_augmenting_path(cost, rows, columns, completed, root) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let column_for_row = match flip_sparse_path(completed, &search.predecessor_row, &search.discovery, root, search.target) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(SparseAugmentation { column_for_row, search })
}
