//! One-path repair after deleting the same original row and column.
//!
//! The Lean source proof covers projection, warm starts, one augmentation and
//! original-index readback under a feasible/tight numeric input invariant.

use crate::{sparse::square_shape, sparse_search::{augment_sparse_permutation, inverse_completed}, AssignmentError};

pub struct SparseDeletedAssignment {
    /// Surviving original row/column coordinates, in increasing order.
    pub vertices: Vec<usize>,
    /// Original column indices, one for each surviving original row in vertices.
    pub column_for_row: Vec<usize>,
    pub rows: Vec<i128>,
    pub columns: Vec<i128>,
    /// False for a fixed deleted vertex; true when one augmentation ran.
    pub repaired: bool,
}

fn compact_index(vertex: usize, removed: usize) -> Result<usize, AssignmentError> {
    if vertex == removed {
        Err(AssignmentError::InvariantViolation)
    } else if vertex < removed {
        Ok(vertex)
    } else {
        Ok(vertex - 1)
    }
}

fn surviving_vertices(n: usize, removed: usize) -> Vec<usize> {
    let mut vertices = Vec::new();
    let mut vertex = 0;
    while vertex < n {
        if vertex != removed {
            vertices.push(vertex);
        }
        vertex += 1;
    }
    vertices
}

fn project_row(values: &[Option<i64>], vertices: &[usize]) -> Vec<Option<i64>> {
    let mut result = Vec::new();
    let mut column = 0;
    while column < vertices.len() {
        result.push(values[vertices[column]]);
        column += 1;
    }
    result
}

fn project_cost(cost: &[Vec<Option<i64>>], vertices: &[usize]) -> Vec<Vec<Option<i64>>> {
    let mut result = Vec::new();
    let mut row = 0;
    while row < vertices.len() {
        result.push(project_row(&cost[vertices[row]], vertices));
        row += 1;
    }
    result
}

fn project_potentials(values: &[i128], vertices: &[usize]) -> Vec<i128> {
    let mut result = Vec::new();
    let mut vertex = 0;
    while vertex < vertices.len() {
        result.push(values[vertices[vertex]]);
        vertex += 1;
    }
    result
}

fn complete_surviving(
    completed: &[usize], vertices: &[usize], removed: usize, free_row: usize, free_column: usize,
) -> Result<Vec<usize>, AssignmentError> {
    let mut result = Vec::new();
    let mut index = 0;
    let mut failure = None;
    while index < vertices.len() && failure.is_none() {
        let row = vertices[index];
        let old_column = if row == free_row { free_column } else { completed[row] };
        match compact_index(old_column, removed) {
            Ok(column) => result.push(column),
            Err(error) => failure = Some(error),
        }
        index += 1;
    }
    match failure {
        Some(error) => Err(error),
        None => Ok(result),
    }
}

fn original_columns(columns: &[usize], vertices: &[usize]) -> Result<Vec<usize>, AssignmentError> {
    let mut result = Vec::new();
    let mut index = 0;
    let mut failure = None;
    while index < columns.len() && failure.is_none() {
        let column = columns[index];
        if column >= vertices.len() {
            failure = Some(AssignmentError::InvariantViolation);
        } else {
            result.push(vertices[column]);
        }
        index += 1;
    }
    match failure {
        Some(error) => Err(error),
        None => Ok(result),
    }
}

/// Restrict an old feasible/tight perfect assignment after deleting a vertex.
///
/// Fixed deletions reuse every surviving edge and potential. Otherwise the
/// unique old free row/column form a temporary completion, and exactly one
/// sparse path augmentation repairs it. The surviving graph must admit a
/// perfect assignment; copied graphs supply their zero identity edges. Output
/// row and column labels refer to the original matrix. This reference caller
/// does not implement the paper's optimized priority-queue schedule.
pub fn repair_deleted_sparse_vertex(
    cost: &[Vec<Option<i64>>], rows: &[i128], columns: &[i128], completed: &[usize], removed: usize,
) -> Result<SparseDeletedAssignment, AssignmentError> {
    let n = cost.len();
    if rows.len() != n || columns.len() != n || completed.len() != n || !square_shape(cost) {
        return Err(AssignmentError::NonSquare);
    }
    if n > u32::MAX as usize {
        return Err(AssignmentError::TooLarge);
    }
    if removed >= n {
        return Err(AssignmentError::InvariantViolation);
    }
    let inverse = match inverse_completed(completed) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let free_row = inverse[removed];
    let free_column = completed[removed];
    let vertices = surviving_vertices(n, removed);
    let projected_cost = project_cost(cost, &vertices);
    let projected_rows = project_potentials(rows, &vertices);
    let projected_columns = project_potentials(columns, &vertices);
    let seed = match complete_surviving(completed, &vertices, removed, free_row, free_column) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let repaired = free_column != removed;
    let (assignment, updated_rows, updated_columns) = if repaired {
        let root = match compact_index(free_row, removed) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        let augmented = match augment_sparse_permutation(&projected_cost, projected_rows, projected_columns, &seed, root) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        (augmented.column_for_row, augmented.search.rows, augmented.search.columns)
    } else {
        (seed, projected_rows, projected_columns)
    };
    let exported = match original_columns(&assignment, &vertices) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(SparseDeletedAssignment { vertices, column_for_row: exported, rows: updated_rows, columns: updated_columns, repaired })
}
