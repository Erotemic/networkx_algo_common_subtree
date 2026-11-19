//! Exact integer assignment core for the common-subtree verification program.
//!
//! Costs are signed i64 values. Potentials and totals use checked i128
//! arithmetic. Returned potentials expose the primal/dual optimality criterion.
//! The complete dense Hungarian API has a maintained Lean total-correctness
//! proof; sparse repair primitives are developed separately.

#[cfg_attr(test, derive(Clone, Debug, PartialEq, Eq))]
pub struct Assignment {
    pub column_for_row: Vec<usize>,
    pub row_potential: Vec<i128>,
    pub column_potential: Vec<i128>,
    pub cost: i128,
}

#[cfg_attr(test, derive(Clone, Copy, Debug, PartialEq, Eq))]
pub enum AssignmentError {
    NonSquare,
    TooLarge,
    ArithmeticOverflow,
    InvariantViolation,
}

pub mod matching;

fn zeros_i128(len: usize) -> Vec<i128> {
    let mut result = Vec::new();
    let mut index = 0;
    while index < len {
        result.push(0);
        index += 1;
    }
    result
}

fn zeros_usize(len: usize) -> Vec<usize> {
    let mut result = Vec::new();
    let mut index = 0;
    while index < len {
        result.push(0);
        index += 1;
    }
    result
}

fn absent_costs(len: usize) -> Vec<Option<i128>> {
    let mut result = Vec::new();
    let mut index = 0;
    while index < len {
        result.push(None);
        index += 1;
    }
    result
}

fn unused_columns(len: usize) -> Vec<bool> {
    let mut result = Vec::new();
    let mut index = 0;
    while index < len {
        result.push(false);
        index += 1;
    }
    result
}

fn minimum_row(row: &[i64]) -> Option<i64> {
    let mut minimum = None;
    let mut column = 0;
    while column < row.len() {
        let value = row[column];
        let improve = match minimum {
            None => true,
            Some(old) => value < old,
        };
        if improve {
            minimum = Some(value);
        }
        column += 1;
    }
    minimum
}

/// Row minima with zero column potentials give a feasible initial dual state.
fn initial_potentials(cost: &[Vec<i64>], extent: usize) -> Result<Vec<i128>, AssignmentError> {
    let mut result = zeros_i128(extent);
    let mut row = 0;
    let mut failure = None;
    while row < cost.len() && failure.is_none() {
        match minimum_row(&cost[row]) {
            Some(value) => result[row + 1] = value as i128,
            None => failure = Some(AssignmentError::InvariantViolation),
        }
        row += 1;
    }
    match failure {
        Some(error) => Err(error),
        None => Ok(result),
    }
}

/// Relax one slack and update its predecessor only on a strict improvement.
fn relax_column(
    slack: &mut Vec<Option<i128>>,
    predecessor: &mut Vec<usize>,
    candidate: usize,
    column: usize,
    reduced: i128,
) -> i128 {
    match slack[candidate] {
        None => {
            slack[candidate] = Some(reduced);
            predecessor[candidate] = column;
            reduced
        }
        Some(old) => {
            if reduced < old {
                slack[candidate] = Some(reduced);
                predecessor[candidate] = column;
                reduced
            } else {
                old
            }
        }
    }
}

/// Keep an attaining column, retaining the earlier one when costs tie.
fn select_delta(
    delta: Option<i128>,
    next_column: usize,
    best: i128,
    candidate: usize,
) -> (Option<i128>, usize) {
    match delta {
        None => (Some(best), candidate),
        Some(old) => {
            if best < old {
                (Some(best), candidate)
            } else {
                (delta, next_column)
            }
        }
    }
}

/// Scan the unused columns and update the exact minimum slacks.
fn scan_columns(
    cost: &[Vec<i64>],
    u: &[i128],
    v: &[i128],
    used: &[bool],
    slack: &mut Vec<Option<i128>>,
    predecessor: &mut Vec<usize>,
    column: usize,
    active_row: usize,
    n: usize,
) -> Result<(i128, usize), AssignmentError> {
    let mut delta = None;
    let mut next_column = 0;
    let mut candidate = 1;
    while candidate <= n {
        if !used[candidate] {
            let first =
                match (cost[active_row - 1][candidate - 1] as i128).checked_sub(u[active_row]) {
                    Some(value) => value,
                    None => return Err(AssignmentError::ArithmeticOverflow),
                };
            let reduced = match first.checked_sub(v[candidate]) {
                Some(value) => value,
                None => return Err(AssignmentError::ArithmeticOverflow),
            };
            let best = relax_column(slack, predecessor, candidate, column, reduced);
            let (new_delta, new_column) = select_delta(delta, next_column, best, candidate);
            delta = new_delta;
            next_column = new_column;
        }
        candidate += 1;
    }
    match delta {
        Some(value) => Ok((value, next_column)),
        None => Err(AssignmentError::InvariantViolation),
    }
}

fn adjust_potentials(
    u: &mut Vec<i128>,
    v: &mut Vec<i128>,
    matched_row: &[usize],
    used: &[bool],
    slack: &mut Vec<Option<i128>>,
    amount: i128,
    n: usize,
) -> Result<(), AssignmentError> {
    let mut index = 0;
    while index <= n {
        if used[index] {
            let assigned = matched_row[index];
            u[assigned] = match u[assigned].checked_add(amount) {
                Some(value) => value,
                None => return Err(AssignmentError::ArithmeticOverflow),
            };
            v[index] = match v[index].checked_sub(amount) {
                Some(value) => value,
                None => return Err(AssignmentError::ArithmeticOverflow),
            };
        } else if let Some(value) = slack[index] {
            slack[index] = match value.checked_sub(amount) {
                Some(updated) => Some(updated),
                None => return Err(AssignmentError::ArithmeticOverflow),
            };
        }
        index += 1;
    }
    Ok(())
}

fn find_augmenting_column(
    cost: &[Vec<i64>],
    u: &mut Vec<i128>,
    v: &mut Vec<i128>,
    matched_row: &[usize],
    predecessor: &mut Vec<usize>,
    n: usize,
    extent: usize,
) -> Result<usize, AssignmentError> {
    let mut column = 0;
    let mut slack = absent_costs(extent);
    let mut used = unused_columns(extent);
    let mut visited = 0;
    let mut searching = true;
    let mut failure = None;
    while searching && failure.is_none() {
        if visited >= n || used[column] {
            failure = Some(AssignmentError::InvariantViolation);
        }
        visited += 1;
        used[column] = true;
        let active_row = matched_row[column];
        if active_row == 0 || active_row > n {
            failure = Some(AssignmentError::InvariantViolation);
        }
        if failure.is_none() {
            match scan_columns(
                cost,
                u,
                v,
                &used,
                &mut slack,
                predecessor,
                column,
                active_row,
                n,
            ) {
                Err(error) => failure = Some(error),
                Ok((amount, next_column)) => {
                    match adjust_potentials(u, v, matched_row, &used, &mut slack, amount, n) {
                        Err(error) => failure = Some(error),
                        Ok(()) => {
                            column = next_column;
                            searching = matched_row[column] != 0;
                        }
                    }
                }
            }
        }
    }
    match failure {
        Some(error) => Err(error),
        None => Ok(column),
    }
}

fn augment_matching(
    matched_row: &mut Vec<usize>,
    predecessor: &[usize],
    mut column: usize,
    n: usize,
) -> Result<(), AssignmentError> {
    let mut path_length = 0;
    while column != 0 {
        if path_length >= n {
            return Err(AssignmentError::InvariantViolation);
        }
        path_length += 1;
        let previous = predecessor[column];
        matched_row[column] = matched_row[previous];
        column = previous;
    }
    Ok(())
}

fn reconstruct_assignment(
    cost: &[Vec<i64>],
    u: &[i128],
    v: &[i128],
    matched_row: &[usize],
    n: usize,
) -> Result<Assignment, AssignmentError> {
    let mut failure = None;
    let mut column_for_row = zeros_usize(n);
    let mut column = 1;
    while column <= n && failure.is_none() {
        let assigned = matched_row[column];
        if assigned == 0 || assigned > n {
            failure = Some(AssignmentError::InvariantViolation);
        } else {
            column_for_row[assigned - 1] = column - 1;
        }
        column += 1;
    }
    let mut total = 0i128;
    let mut row_potential = Vec::new();
    let mut column_potential = Vec::new();
    let mut index = 0;
    while index < n && failure.is_none() {
        match total.checked_add(cost[index][column_for_row[index]] as i128) {
            Some(value) => total = value,
            None => failure = Some(AssignmentError::ArithmeticOverflow),
        }
        row_potential.push(u[index + 1]);
        column_potential.push(v[index + 1]);
        index += 1;
    }
    match failure {
        Some(error) => Err(error),
        None => Ok(Assignment {
            column_for_row,
            row_potential,
            column_potential,
            cost: total,
        }),
    }
}

fn finish_assignment(
    cost: &[Vec<i64>],
    n: usize,
    extent: usize,
    mut u: Vec<i128>,
) -> Result<Assignment, AssignmentError> {
    let mut v = zeros_i128(extent);
    let mut matched_row = zeros_usize(extent);
    let mut predecessor = zeros_usize(extent);
    let mut next_row = 1;
    let mut failure = None;
    while next_row <= n && failure.is_none() {
        matched_row[0] = next_row;
        match find_augmenting_column(
            cost,
            &mut u,
            &mut v,
            &matched_row,
            &mut predecessor,
            n,
            extent,
        ) {
            Err(error) => failure = Some(error),
            Ok(column) => match augment_matching(&mut matched_row, &predecessor, column, n) {
                Err(error) => failure = Some(error),
                Ok(()) => {}
            },
        }
        next_row += 1;
    }
    match failure {
        Some(error) => Err(error),
        None => reconstruct_assignment(cost, &u, &v, &matched_row, n),
    }
}

fn is_square(cost: &[Vec<i64>]) -> bool {
    let n = cost.len();
    let mut row = 0;
    while row < n {
        if cost[row].len() != n {
            return false;
        }
        row += 1;
    }
    true
}

/// Minimum-cost perfect assignment of a square signed-integer matrix.
///
/// Empty input has the empty assignment and cost zero. Malformed inputs and
/// checked-arithmetic failures are explicit errors. Finite costs are never
/// replaced by a sentinel, and zero is a valid reduced cost.
///
/// Row minima and zero column potentials initialize a feasible dual state.
/// A reserved column zero supports augmentation; exported indices are zero based.
pub fn min_cost_assignment(cost: &[Vec<i64>]) -> Result<Assignment, AssignmentError> {
    let n = cost.len();
    if n > u32::MAX as usize {
        return Err(AssignmentError::TooLarge);
    }
    let extent = match n.checked_add(1) {
        Some(value) => value,
        None => return Err(AssignmentError::TooLarge),
    };
    if !is_square(cost) {
        return Err(AssignmentError::NonSquare);
    }
    match initial_potentials(cost, extent) {
        Ok(value) => finish_assignment(cost, n, extent, value),
        Err(error) => Err(error),
    }
}

#[cfg(test)]
mod tests;

pub mod deletion;

pub mod sparse;

pub mod sparse_search;

pub mod sparse_deletion;

/// Original-index construction for complete uniform matching families.
pub mod uniform_pairs;
