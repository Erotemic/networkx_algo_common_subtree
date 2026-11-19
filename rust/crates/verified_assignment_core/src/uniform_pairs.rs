/// Select one original pair in a uniform complete matching.
#[inline]
fn uniform_row(
    left: usize,
    right: usize,
    deleted: Option<usize>,
    row: usize,
) -> Option<(usize, usize)> {
    match deleted {
        None => Some((row, row)),
        Some(removed) => {
            if right > left {
                Some((row, if row == removed { left } else { row }))
            } else if row == removed {
                None
            } else {
                Some((row, row))
            }
        }
    }
}

/// Original pair indices for a complete uniform matching. An optional original
/// right vertex is deleted; an index outside the right side has no effect.
/// Scoring remains outside this integer-only construction.
#[inline]
pub fn uniform_pair_indices(
    left: usize,
    right: usize,
    deleted: Option<usize>,
) -> Vec<(usize, usize)> {
    let size = if left < right { left } else { right };
    let mut pairs = Vec::with_capacity(size);
    let mut row = 0;
    while row < size {
        match uniform_row(left, right, deleted, row) {
            Some(pair) => pairs.push(pair),
            None => {}
        }
        row += 1;
    }
    pairs
}
