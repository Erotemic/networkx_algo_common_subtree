//! Exact allowed-edge cut primitives for the sparse assignment repair.

use crate::AssignmentError;

pub struct SparseCut {
    pub row: usize,
    pub column: usize,
    pub delta: i128,
}

/// Retain the first edge on equal slack, with no sentinel for absence.
fn select_cut(previous: Option<SparseCut>, candidate: SparseCut) -> SparseCut {
    match previous {
        None => candidate,
        Some(old) => {
            if candidate.delta < old.delta {
                candidate
            } else {
                old
            }
        }
    }
}

fn square_shape(cost: &[Vec<Option<i64>>]) -> bool {
    let mut row = 0;
    while row < cost.len() {
        if cost[row].len() != cost.len() {
            return false;
        }
        row += 1;
    }
    true
}

fn minimum_sparse_row(
    cost: &[Option<i64>],
    row_potential: i128,
    columns: &[i128],
    selected_columns: &[bool],
    row: usize,
    mut best: Option<SparseCut>,
) -> Result<Option<SparseCut>, AssignmentError> {
    let mut column = 0;
    while column < cost.len() {
        if !selected_columns[column] {
            let edge = cost[column];
            match edge {
                None => {}
                Some(value) => {
                    let partial = match (value as i128).checked_sub(row_potential) {
                        Some(value) => value,
                        None => return Err(AssignmentError::ArithmeticOverflow),
                    };
                    let delta = match partial.checked_sub(columns[column]) {
                        Some(value) => value,
                        None => return Err(AssignmentError::ArithmeticOverflow),
                    };
                    best = Some(select_cut(best, SparseCut { row, column, delta }));
                }
            }
        }
        column += 1;
    }
    Ok(best)
}

/// Minimum reduced cost across the selected-row/unselected-column cut.
///
/// Only actual optional edges are considered. None means no allowed crossing
/// edge. The optional matrix and all state vectors must have the same square
/// extent; malformed dimensions, oversized extent and checked arithmetic failure
/// are explicit errors. This is a cut primitive, not yet a sparse solver.
pub fn minimum_sparse_cut(
    cost: &[Vec<Option<i64>>],
    rows: &[i128],
    columns: &[i128],
    selected_rows: &[bool],
    selected_columns: &[bool],
) -> Result<Option<SparseCut>, AssignmentError> {
    let n = cost.len();
    if rows.len() != n
        || columns.len() != n
        || selected_rows.len() != n
        || selected_columns.len() != n
    {
        return Err(AssignmentError::NonSquare);
    }
    if !square_shape(cost) {
        return Err(AssignmentError::NonSquare);
    }
    if n > u32::MAX as usize {
        return Err(AssignmentError::TooLarge);
    }
    let mut best = None;
    let mut row = 0;
    while row < n {
        if selected_rows[row] {
            best = match minimum_sparse_row(
                &cost[row],
                rows[row],
                columns,
                selected_columns,
                row,
                best,
            ) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
        }
        row += 1;
    }
    Ok(best)
}

fn increase_selected(value: i128, selected: bool, delta: i128) -> Result<i128, AssignmentError> {
    if selected {
        match value.checked_add(delta) {
            Some(value) => Ok(value),
            None => Err(AssignmentError::ArithmeticOverflow),
        }
    } else {
        Ok(value)
    }
}

fn decrease_selected(value: i128, selected: bool, delta: i128) -> Result<i128, AssignmentError> {
    if selected {
        match value.checked_sub(delta) {
            Some(value) => Ok(value),
            None => Err(AssignmentError::ArithmeticOverflow),
        }
    } else {
        Ok(value)
    }
}

fn adjust_selected(
    values: &[i128],
    selected: &[bool],
    delta: i128,
    increasing: bool,
) -> Result<Vec<i128>, AssignmentError> {
    let mut updated = Vec::new();
    let mut index = 0;
    while index < values.len() {
        let value = if increasing {
            increase_selected(values[index], selected[index], delta)
        } else {
            decrease_selected(values[index], selected[index], delta)
        };
        let value = match value {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        updated.push(value);
        index += 1;
    }
    Ok(updated)
}

/// Apply a nonnegative cut adjustment to zero-based sparse potential vectors.
///
/// The selected row potentials increase and selected column potentials decrease
/// by exactly delta. Input slices are preserved, and partial output is discarded
/// on checked arithmetic failure. This uses the same coordinates as the sparse
/// cut primitive, with no reserved dense-Hungarian accumulator slot.
pub fn adjust_sparse_cut(
    rows: &[i128],
    columns: &[i128],
    selected_rows: &[bool],
    selected_columns: &[bool],
    delta: i128,
) -> Result<(Vec<i128>, Vec<i128>), AssignmentError> {
    let n = rows.len();
    if columns.len() != n || selected_rows.len() != n || selected_columns.len() != n {
        return Err(AssignmentError::NonSquare);
    }
    if n > u32::MAX as usize {
        return Err(AssignmentError::TooLarge);
    }
    if delta < 0 {
        return Err(AssignmentError::InvariantViolation);
    }
    let updated_rows = match adjust_selected(rows, selected_rows, delta, true) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let updated_columns = match adjust_selected(columns, selected_columns, delta, false) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok((updated_rows, updated_columns))
}
