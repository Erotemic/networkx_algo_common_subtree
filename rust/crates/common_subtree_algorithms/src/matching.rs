//! Weighted bipartite matching primitives.
//!
//! The two supported paper-level recurrences reduce each rooted
//! child-combination subproblem to a maximum-weight bipartite matching instance:
//! maximum common subtree isomorphism and largest-weight common subtree
//! embeddings with distance penalties. This module keeps the reference
//! implementation small and self-contained: optional matrix entries are
//! incompatible, real vertices may remain unmatched at zero profit, and the
//! returned matching only contains positive real-real assignments.

use crate::Weight;

/// Result of a maximum-weight bipartite matching.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct WeightedMatching {
    /// Chosen pairs as `(left_index, right_index)`.
    pub pairs: Vec<(usize, usize)>,
    /// Sum of chosen edge weights.
    pub weight: Weight,
}

/// One optimum and optima after deleting each original right vertex.
/// Unmatched deletions share `base`; repaired witnesses retain original indices.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct WeightedMatchingFamily {
    pub base: WeightedMatching,
    pub(crate) deletions: Vec<Option<WeightedMatching>>,
}

impl WeightedMatchingFamily {
    pub fn right_size(&self) -> usize {
        self.deletions.len()
    }

    /// Return the optimum excluding `deleted`, or `None` for an invalid index.
    pub fn without_right(&self, deleted: usize) -> Option<&WeightedMatching> {
        self.deletions
            .get(deleted)
            .map(|changed| changed.as_ref().unwrap_or(&self.base))
    }
}

fn matching_from_pairs(
    weights: &[Vec<Option<Weight>>],
    pairs: impl Iterator<Item = (usize, usize)>,
) -> WeightedMatching {
    let mut pairs: Vec<_> = pairs
        .filter(|&(u, v)| weights[u][v].is_some_and(|w| w > 0.0))
        .collect();
    pairs.sort_unstable();
    let mut weight = 0.0;
    for &(u, v) in &pairs {
        weight += weights[u][v].unwrap();
        assert!(weight.is_finite(), "matching total weight overflow");
    }
    WeightedMatching { pairs, weight }
}

/// Compute a related family without independently solving each deleted matrix.
///
/// The smaller side is covered using zero-profit dummy columns. Unmatched
/// right vertices reuse the optimum; each matched deletion uses one Hungarian
/// augmentation. Larger-side deletions remove a column. Smaller-side deletions
/// replace the deleted row by a zero-cost dummy on the old occupied columns:
/// an optimum of the surviving rows exists within those columns (alternating
/// components starting at old unoccupied columns cannot improve an old optimum).
///
/// For nonempty sides k=min(left,right), l=max(left,right), dense arithmetic is
/// O(k^2*l), including all deletions. Only k deletions can require repair.
/// Scratch space is linear; returned repaired pairs occupy at most O(k^2)
/// space plus the right-index table. This f64 implementation is tested, not
/// covered by the separate exact-integer source proof. Panics follow the
/// finite/shape/overflow contract of `max_weight_bipartite_matching`.
pub fn max_weight_bipartite_matching_with_right_deletions(
    weights: &[Vec<Option<Weight>>],
) -> WeightedMatchingFamily {
    let (left, right) = validate_weights(weights);
    if left == 0 || right == 0 {
        return WeightedMatchingFamily::default();
    }
    if !weights.iter().flatten().flatten().any(|&w| w > 0.0) {
        return WeightedMatchingFamily {
            base: WeightedMatching::default(),
            deletions: vec![None; right],
        };
    }
    let transposed = left > right;
    let rows = left.min(right);
    let real_columns = left.max(right);
    let columns = left
        .checked_add(right)
        .expect("matching dimension overflow");
    let cost = |i: usize, j: usize| {
        if j >= real_columns {
            0.0
        } else {
            let value = if transposed {
                weights[j][i]
            } else {
                weights[i][j]
            };
            -value.unwrap_or(0.0).max(0.0)
        }
    };
    let state = AssignmentState::solve(rows, columns, &cost);
    let occupied = state.columns();
    let base = matching_from_pairs(
        weights,
        occupied
            .iter()
            .enumerate()
            .filter(|&(_, &j)| j < real_columns)
            .map(|(i, &j)| if transposed { (j, i) } else { (i, j) }),
    );
    let mut matched_right = vec![false; right];
    for &(_, j) in &base.pairs {
        matched_right[j] = true;
    }
    let mut deletions = Vec::with_capacity(right);
    let mut repair = AssignmentState::new(rows, if transposed { rows } else { columns - 1 });
    for deleted in 0..right {
        if !matched_right[deleted] {
            deletions.push(None);
            continue;
        }
        repair.u.clone_from(&state.u);
        if !transposed {
            let original = |j: usize| if j < deleted { j } else { j + 1 };
            for j in 0..columns - 1 {
                repair.p[j + 1] = state.p[original(j) + 1];
                repair.v[j + 1] = state.v[original(j) + 1];
            }
            let free_row = state.p[deleted + 1] - 1;
            repair.augment_row(free_row, &|i, j| cost(i, original(j)));
            let result = matching_from_pairs(
                weights,
                (1..repair.p.len())
                    .filter(|&j| repair.p[j] != 0 && original(j - 1) < right)
                    .map(|j| (repair.p[j] - 1, original(j - 1))),
            );
            deletions.push(Some(result));
        } else {
            // Occupied columns are in original row order, so the old matching
            // is diagonal in these compact coordinates. Leave the new dummy
            // row free and choose a feasible potential for its zero costs.
            for j in 0..rows {
                repair.p[j + 1] = if j == deleted { 0 } else { j + 1 };
                repair.v[j + 1] = state.v[occupied[j] + 1];
            }
            repair.u[deleted + 1] = repair.v[1..]
                .iter()
                .map(|v| -v)
                .fold(f64::INFINITY, f64::min);
            repair.augment_row(deleted, &|i, j| {
                if i == deleted {
                    0.0
                } else {
                    cost(i, occupied[j])
                }
            });
            let result = matching_from_pairs(
                weights,
                (1..repair.p.len())
                    .filter(|&j| {
                        repair.p[j] != 0 && repair.p[j] - 1 != deleted && occupied[j - 1] < left
                    })
                    .map(|j| (occupied[j - 1], repair.p[j] - 1)),
            );
            deletions.push(Some(result));
        }
    }
    WeightedMatchingFamily { base, deletions }
}

/// Solve a maximum-weight bipartite matching problem.
///
/// `weights[i][j] == None` means left vertex `i` cannot be matched to right
/// vertex `j`. Vertices are allowed to remain unmatched with contribution `0`.
/// Nonpositive compatible edges are omitted. Every strictly positive chosen
/// weight is retained, without a fixed absolute threshold.
///
/// # Panics
///
/// Panics for ragged matrices, nonfinite weights, or nonfinite intermediate
/// arithmetic. Floating-point rounding remains part of this reference API;
/// it is not an exact-real solver.
///
/// The implementation assigns the smaller side into the larger side, replacing
/// forbidden/nonpositive profits by zero and discarding zero assignments.
/// Every partial matching extends to such an injection without decreasing its
/// profit, and every injection decodes to a feasible partial matching. Thus
/// the optima agree without dummy rows/columns. The rectangular Hungarian
/// algorithm uses O(min(left,right)^2 * max(left,right)) arithmetic operations
/// and linear auxiliary space, excluding the input and returned pairs.
/// This bound does not establish the faster paper-level tree algorithms.
pub fn max_weight_bipartite_matching(weights: &[Vec<Option<Weight>>]) -> WeightedMatching {
    let (left, right) = validate_weights(weights);
    if left == 0 || right == 0 {
        return WeightedMatching::default();
    }
    if !weights.iter().flatten().flatten().any(|&w| w > 0.0) {
        return WeightedMatching::default();
    }

    // Common leaf/chain subproblems need only a scan, not augmentation.
    if left == 1 || right == 1 {
        let mut best = 0.0;
        let mut pair = None;
        for (i, row) in weights.iter().enumerate() {
            for (j, value) in row.iter().enumerate() {
                if let Some(w) = value {
                    if *w > best {
                        best = *w;
                        pair = Some((i, j));
                    }
                }
            }
        }
        return WeightedMatching {
            pairs: pair.into_iter().collect(),
            weight: best,
        };
    }

    let transposed = left > right;
    let (rows, columns) = (left.min(right), left.max(right));
    let assignment = min_cost_assignment_rectangular(rows, columns, |i, j| {
        let value = if transposed {
            weights[j][i]
        } else {
            weights[i][j]
        };
        // Negate directly: a max-profit shift can erase tiny positive weights
        // when another entry is much larger. No cost/profit matrices are built.
        -value.unwrap_or(0.0).max(0.0)
    });
    let mut pairs = Vec::with_capacity(rows);
    for (i, j) in assignment.into_iter().enumerate() {
        let pair = if transposed { (j, i) } else { (i, j) };
        if weights[pair.0][pair.1].is_some_and(|w| w > 0.0) {
            pairs.push(pair);
        }
    }
    pairs.sort_unstable();
    let mut weight = 0.0;
    for &(i, j) in &pairs {
        weight += weights[i][j].unwrap();
        assert!(weight.is_finite(), "matching total weight overflow");
    }
    WeightedMatching { pairs, weight }
}

/// Rectangular Hungarian state; column/row zero are path sentinels.
/// Keeping the duals and assignment permits a single warm augmentation.
struct AssignmentState {
    u: Vec<Weight>,
    v: Vec<Weight>,
    p: Vec<usize>,
    way: Vec<usize>,
    minv: Vec<Weight>,
    used: Vec<bool>,
}

impl AssignmentState {
    fn new(rows: usize, columns: usize) -> Self {
        let row_extent = rows.checked_add(1).expect("matching dimension overflow");
        let column_extent = columns.checked_add(1).expect("matching dimension overflow");
        Self {
            u: vec![0.0; row_extent],
            v: vec![0.0; column_extent],
            p: vec![0; column_extent],
            way: vec![0; column_extent],
            minv: vec![f64::INFINITY; column_extent],
            used: vec![false; column_extent],
        }
    }

    fn solve(rows: usize, columns: usize, cost: &impl Fn(usize, usize) -> Weight) -> Self {
        let mut state = Self::new(rows, columns);
        for row in 0..rows {
            state.augment_row(row, cost);
        }
        state
    }

    /// All other rows are matched tightly under a feasible dual. This fills
    /// the unique free row, using the existing free columns and potentials.
    fn augment_row(&mut self, row: usize, cost: &impl Fn(usize, usize) -> Weight) {
        let columns = self.p.len() - 1;
        self.p[0] = row + 1;
        let mut j0 = 0usize;
        self.minv.fill(f64::INFINITY);
        self.used.fill(false);
        self.way.fill(0);
        loop {
            self.used[j0] = true;
            let i0 = self.p[j0];
            let mut delta = f64::INFINITY;
            let mut j1 = 0usize;
            for j in 1..=columns {
                if !self.used[j] {
                    let cur = cost(i0 - 1, j - 1) - self.u[i0] - self.v[j];
                    assert!(cur.is_finite(), "matching reduced-cost arithmetic overflow");
                    if cur < self.minv[j] {
                        self.minv[j] = cur;
                        self.way[j] = j0;
                    }
                    if self.minv[j] < delta {
                        delta = self.minv[j];
                        j1 = j;
                    }
                }
            }
            assert!(
                delta.is_finite(),
                "matching augmentation requires a finite cost"
            );
            for j in 0..=columns {
                if self.used[j] {
                    self.u[self.p[j]] += delta;
                    // Column zero is only a path sentinel. Its unused dual
                    // objective can overflow even if every real potential is
                    // finite; the actual selected total is checked separately.
                    if j != 0 {
                        self.v[j] -= delta;
                    }
                    assert!(
                        self.u[self.p[j]].is_finite() && self.v[j].is_finite(),
                        "matching potential arithmetic overflow"
                    );
                } else {
                    self.minv[j] -= delta;
                }
            }
            j0 = j1;
            if self.p[j0] == 0 {
                break;
            }
        }
        loop {
            let j1 = self.way[j0];
            self.p[j0] = self.p[j1];
            j0 = j1;
            if j0 == 0 {
                break;
            }
        }
    }

    fn columns(&self) -> Vec<usize> {
        let mut assignment = vec![0usize; self.u.len() - 1];
        for j in 1..self.p.len() {
            if self.p[j] != 0 {
                assignment[self.p[j] - 1] = j - 1;
            }
        }
        assignment
    }
}

fn min_cost_assignment_rectangular(
    rows: usize,
    columns: usize,
    cost: impl Fn(usize, usize) -> Weight,
) -> Vec<usize> {
    AssignmentState::solve(rows, columns, &cost).columns()
}

fn validate_weights(weights: &[Vec<Option<Weight>>]) -> (usize, usize) {
    let left = weights.len();
    let right = weights.first().map_or(0, Vec::len);
    for row in weights {
        assert_eq!(
            row.len(),
            right,
            "all rows in a matching weight matrix must have the same length"
        );
        for w in row.iter().flatten() {
            assert!(w.is_finite(), "matching weights must be finite");
        }
    }
    (left, right)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matching_handles_rectangular_inputs_and_unmatched_vertices() {
        let weights = vec![
            vec![Some(8.0), Some(1.0), None],
            vec![Some(7.0), Some(6.0), Some(-5.0)],
        ];
        let result = max_weight_bipartite_matching(&weights);
        assert_eq!(result.pairs, vec![(0, 0), (1, 1)]);
        assert_eq!(result.weight, 14.0);
    }

    #[test]
    fn matching_prefers_unmatched_to_negative_edges() {
        let weights = vec![vec![Some(-1.0)]];
        let result = max_weight_bipartite_matching(&weights);
        assert_eq!(result.pairs, Vec::<(usize, usize)>::new());
        assert_eq!(result.weight, 0.0);
    }
}
