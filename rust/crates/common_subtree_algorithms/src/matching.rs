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
    if left == 0 || right == 0 {
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

/// Rectangular Hungarian assignment: rows <= columns, row -> column.
/// Costs are read on demand; scratch buffers are reused between augmentations.
fn min_cost_assignment_rectangular(
    rows: usize,
    columns: usize,
    cost: impl Fn(usize, usize) -> Weight,
) -> Vec<usize> {
    let row_extent = rows.checked_add(1).expect("matching dimension overflow");
    let column_extent = columns.checked_add(1).expect("matching dimension overflow");
    let mut u = vec![0.0; row_extent];
    let mut v = vec![0.0; column_extent];
    let mut p = vec![0usize; column_extent];
    let mut way = vec![0usize; column_extent];
    let mut minv = vec![f64::INFINITY; column_extent];
    let mut used = vec![false; column_extent];

    for i in 1..=rows {
        p[0] = i;
        let mut j0 = 0usize;
        minv.fill(f64::INFINITY);
        used.fill(false);
        way.fill(0);
        loop {
            used[j0] = true;
            let i0 = p[j0];
            let mut delta = f64::INFINITY;
            let mut j1 = 0usize;
            for j in 1..=columns {
                if !used[j] {
                    let cur = cost(i0 - 1, j - 1) - u[i0] - v[j];
                    assert!(cur.is_finite(), "matching reduced-cost arithmetic overflow");
                    if cur < minv[j] {
                        minv[j] = cur;
                        way[j] = j0;
                    }
                    if minv[j] < delta {
                        delta = minv[j];
                        j1 = j;
                    }
                }
            }
            assert!(
                delta.is_finite(),
                "matching augmentation requires a finite cost"
            );
            for j in 0..=columns {
                if used[j] {
                    u[p[j]] += delta;
                    // Column zero is only a path sentinel. Its unused dual
                    // objective can overflow even if every real potential is
                    // finite; the actual selected total is checked separately.
                    if j != 0 {
                        v[j] -= delta;
                    }
                    assert!(
                        u[p[j]].is_finite() && v[j].is_finite(),
                        "matching potential arithmetic overflow"
                    );
                } else {
                    minv[j] -= delta;
                }
            }
            j0 = j1;
            if p[j0] == 0 {
                break;
            }
        }
        loop {
            let j1 = way[j0];
            p[j0] = p[j1];
            j0 = j1;
            if j0 == 0 {
                break;
            }
        }
    }
    let mut assignment = vec![0usize; rows];
    for j in 1..=columns {
        if p[j] != 0 {
            assignment[p[j] - 1] = j - 1;
        }
    }
    assignment
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
