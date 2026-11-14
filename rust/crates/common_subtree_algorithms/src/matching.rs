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
/// The implementation builds a square assignment instance with dummy rows and
/// columns and solves it with the Hungarian algorithm for minimum cost. The
/// dummy assignments are what make unmatched vertices possible.
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

    let size = left
        .checked_add(right)
        .expect("matching matrix size overflow");
    let mut profit = vec![vec![0.0; size]; size];

    let mut max_real_profit: Weight = 0.0;
    for i in 0..left {
        for j in 0..right {
            // Dummy assignments permit every nonpositive or forbidden pair
            // to have zero profit. Reconstruction drops these pairs, exactly
            // as in the independent Lean dummy-assignment reduction.
            let w = weights[i][j].unwrap_or(0.0).max(0.0);
            profit[i][j] = w;
            max_real_profit = max_real_profit.max(w);
        }
    }

    let mut cost = vec![vec![0.0; size]; size];
    for i in 0..size {
        for j in 0..size {
            cost[i][j] = max_real_profit - profit[i][j];
        }
    }

    let assignment = min_cost_assignment_square(&cost);
    let mut pairs = Vec::new();
    let mut weight = 0.0;
    for i in 0..left {
        let j = assignment[i];
        if j < right {
            if let Some(w) = weights[i][j] {
                if w > 0.0 {
                    pairs.push((i, j));
                    weight += w;
                    assert!(weight.is_finite(), "matching total weight overflow");
                }
            }
        }
    }
    pairs.sort_unstable();
    WeightedMatching { pairs, weight }
}

/// Hungarian algorithm for a square minimum-cost assignment problem.
///
/// Returns `assignment[row] = col`. This is the classic 1-indexed potential
/// implementation adapted to Rust vectors.
fn min_cost_assignment_square(cost: &[Vec<Weight>]) -> Vec<usize> {
    let n = cost.len();
    if n == 0 {
        return Vec::new();
    }
    for row in cost {
        assert_eq!(row.len(), n, "assignment matrix must be square");
    }

    let mut u = vec![0.0; n + 1];
    let mut v = vec![0.0; n + 1];
    let mut p = vec![0usize; n + 1];
    let mut way = vec![0usize; n + 1];

    for i in 1..=n {
        p[0] = i;
        let mut j0 = 0usize;
        let mut minv = vec![f64::INFINITY; n + 1];
        let mut used = vec![false; n + 1];
        way.fill(0);

        loop {
            used[j0] = true;
            let i0 = p[j0];
            let mut delta = f64::INFINITY;
            let mut j1 = 0usize;

            for j in 1..=n {
                if !used[j] {
                    let cur = cost[i0 - 1][j - 1] - u[i0] - v[j];
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
            for j in 0..=n {
                if used[j] {
                    u[p[j]] += delta;
                    v[j] -= delta;
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

    let mut assignment = vec![0usize; n];
    for j in 1..=n {
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
