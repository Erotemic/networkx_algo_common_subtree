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

const EPS: Weight = 1.0e-9;
const FORBIDDEN_PROFIT: Weight = -1.0e100;

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
/// Consequently, negative-weight compatible edges are normally ignored unless
/// they are needed only for tie-breaking in a later extension.
///
/// The implementation builds a square assignment instance with dummy rows and
/// columns and solves it with the Hungarian algorithm for minimum cost. The
/// dummy assignments are what make unmatched vertices possible.
pub fn max_weight_bipartite_matching(weights: &[Vec<Option<Weight>>]) -> WeightedMatching {
    let left = weights.len();
    let right = weights.first().map_or(0, Vec::len);
    if left == 0 || right == 0 {
        return WeightedMatching::default();
    }
    for row in weights {
        assert_eq!(
            row.len(),
            right,
            "all rows in a matching weight matrix must have the same length"
        );
    }

    let size = left + right;
    let mut profit = vec![vec![0.0; size]; size];

    let mut max_real_profit = 0.0;
    for i in 0..left {
        for j in 0..right {
            match weights[i][j] {
                Some(w) => {
                    profit[i][j] = w;
                    if w > max_real_profit {
                        max_real_profit = w;
                    }
                }
                None => {
                    profit[i][j] = FORBIDDEN_PROFIT;
                }
            }
        }
    }

    let forbidden_cost = max_real_profit.abs() + 1.0e50;
    let mut cost = vec![vec![0.0; size]; size];
    for i in 0..size {
        for j in 0..size {
            cost[i][j] = if profit[i][j] <= FORBIDDEN_PROFIT / 2.0 {
                forbidden_cost
            } else {
                max_real_profit - profit[i][j]
            };
        }
    }

    let assignment = min_cost_assignment_square(&cost);
    let mut pairs = Vec::new();
    let mut weight = 0.0;
    for i in 0..left {
        let j = assignment[i];
        if j < right {
            if let Some(w) = weights[i][j] {
                if w > EPS {
                    pairs.push((i, j));
                    weight += w;
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
