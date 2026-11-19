use common_subtree_algorithms::{
    max_weight_bipartite_matching, max_weight_bipartite_matching_with_right_deletions,
};

const EPS: f64 = 1.0e-9;

fn assert_close(found: f64, expected: f64) {
    assert!(
        (found - expected).abs() <= EPS,
        "found {found}, expected {expected}"
    );
}

fn brute_force_matching_weight(weights: &[Vec<Option<f64>>]) -> f64 {
    let right = weights.first().map_or(0, Vec::len);
    let mut used = vec![false; right];
    let mut best = 0.0;
    fn rec(
        row: usize,
        weights: &[Vec<Option<f64>>],
        used: &mut [bool],
        current: f64,
        best: &mut f64,
    ) {
        if row == weights.len() {
            if current > *best {
                *best = current;
            }
            return;
        }

        // Leave this left vertex unmatched.
        rec(row + 1, weights, used, current, best);

        for col in 0..used.len() {
            if !used[col] {
                if let Some(weight) = weights[row][col] {
                    used[col] = true;
                    rec(row + 1, weights, used, current + weight, best);
                    used[col] = false;
                }
            }
        }
    }
    rec(0, weights, &mut used, 0.0, &mut best);
    best
}

fn check_against_bruteforce(weights: Vec<Vec<Option<f64>>>) {
    let result = max_weight_bipartite_matching(&weights);
    let expected = brute_force_matching_weight(&weights);
    assert_close(result.weight, expected);

    let mut seen_left = vec![false; weights.len()];
    let right = weights.first().map_or(0, Vec::len);
    let mut seen_right = vec![false; right];
    let mut pair_weight = 0.0;
    for &(i, j) in &result.pairs {
        assert!(i < weights.len());
        assert!(j < right);
        assert!(!seen_left[i], "left vertex {i} matched twice");
        assert!(!seen_right[j], "right vertex {j} matched twice");
        seen_left[i] = true;
        seen_right[j] = true;
        let edge_weight = weights[i][j].expect("reported pair must be compatible");
        assert!(
            edge_weight > 0.0,
            "reported pair should have positive contribution"
        );
        pair_weight += edge_weight;
    }
    assert_close(result.weight, pair_weight);
}

#[test]
fn matching_matches_bruteforce_on_handwritten_cases() {
    let cases: Vec<Vec<Vec<Option<f64>>>> = vec![
        Vec::new(),
        vec![vec![]],
        vec![vec![Some(1.0)]],
        vec![vec![Some(-2.0)]],
        vec![vec![None]],
        vec![vec![Some(1.0), Some(5.0)]],
        vec![vec![Some(1.0)], vec![Some(5.0)]],
        vec![
            vec![Some(4.0), None, Some(1.0)],
            vec![Some(3.0), Some(2.0), None],
        ],
        vec![
            vec![Some(3.0), Some(10.0), None],
            vec![Some(8.0), Some(4.0), Some(1.0)],
            vec![None, Some(9.0), Some(7.0)],
        ],
        vec![vec![Some(-1.0), Some(2.0)], vec![Some(2.0), Some(-1.0)]],
    ];
    for weights in cases {
        check_against_bruteforce(weights);
    }
}

#[test]
fn matching_matches_bruteforce_on_deterministic_small_matrices() {
    let values = [
        None,
        Some(-3.0),
        Some(-0.5),
        Some(0.0),
        Some(1.0),
        Some(2.5),
    ];
    let mut seed = 0x5eed_u64;
    for rows in 0..=4 {
        for cols in 0..=4 {
            for _case_idx in 0..64 {
                let mut matrix = vec![vec![None; cols]; rows];
                for row in &mut matrix {
                    for cell in row {
                        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                        *cell = values[(seed as usize) % values.len()];
                    }
                }
                check_against_bruteforce(matrix);
            }
        }
    }
}

#[test]
fn matching_keeps_positive_weights_below_old_absolute_threshold() {
    let weight = 5.0e-12;
    let result = max_weight_bipartite_matching(&[vec![Some(weight)]]);
    assert_eq!(result.pairs, vec![(0, 0)]);
    assert_eq!(result.weight, weight);
}

#[test]
fn matching_keeps_tiny_profitable_pairs_beside_large_weights() {
    let result = max_weight_bipartite_matching(&[
        vec![Some(1.0e150), None, None],
        vec![None, None, Some(5.0e-200)],
    ]);
    assert_eq!(result.pairs, vec![(0, 0), (1, 2)]);
    assert_eq!(result.weight, 1.0e150); // The total itself rounds in f64.
}

#[test]
fn rectangular_matching_exhaustive_two_by_three_and_transpose() {
    let values = [None, Some(-0.5), Some(0.0), Some(0.125), Some(2.0)];
    for mut code in 0..5usize.pow(6) {
        let mut weights = vec![vec![None; 3]; 2];
        for row in &mut weights {
            for value in row {
                *value = values[code % 5];
                code /= 5;
            }
        }
        let transpose: Vec<Vec<Option<f64>>> = (0..3)
            .map(|j| (0..2).map(|i| weights[i][j]).collect())
            .collect();
        check_deletion_family(&weights);
        check_deletion_family(&transpose);
        check_against_bruteforce(weights);
        check_against_bruteforce(transpose);
    }
}

#[test]
fn matching_handles_large_signed_weights_without_forbidden_sentinels() {
    let weights = vec![
        vec![Some(8.0e150), None, Some(-1.0e250)],
        vec![Some(7.0e150), Some(6.0e150), None],
    ];
    let result = max_weight_bipartite_matching(&weights);
    assert_eq!(result.pairs, vec![(0, 0), (1, 1)]);
    assert!((result.weight / 1.0e150 - 14.0).abs() < 1.0e-12);
}

#[test]
fn matching_rejects_nonfinite_weights_before_augmentation() {
    for weight in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert!(std::panic::catch_unwind(|| {
            max_weight_bipartite_matching(&[vec![Some(weight)]]);
        })
        .is_err());
    }
}

#[test]
#[should_panic(expected = "all rows in a matching weight matrix must have the same length")]
fn matching_rejects_ragged_matrix_even_when_first_row_is_empty() {
    max_weight_bipartite_matching(&[vec![], vec![Some(1.0)]]);
}

#[test]
#[should_panic(expected = "matching total weight overflow")]
fn matching_rejects_an_unrepresentable_total_weight() {
    max_weight_bipartite_matching(&[vec![Some(f64::MAX), None], vec![None, Some(f64::MAX)]]);
}

fn check_deletion_family(weights: &[Vec<Option<f64>>]) {
    let family = max_weight_bipartite_matching_with_right_deletions(weights);
    let right = weights.first().map_or(0, Vec::len);
    assert_eq!(family.right_size(), right);
    assert_close(family.base.weight, brute_force_matching_weight(weights));
    assert!(family.without_right(right).is_none());
    for deleted in 0..right {
        let induced: Vec<Vec<_>> = weights
            .iter()
            .map(|row| {
                row.iter()
                    .enumerate()
                    .filter(|&(j, _)| j != deleted)
                    .map(|(_, &weight)| weight)
                    .collect()
            })
            .collect();
        let found = family.without_right(deleted).unwrap();
        assert_eq!(
            found.weight,
            brute_force_matching_weight(&induced),
            "deleted {deleted} from {weights:?}"
        );
        let mut used_left = vec![false; weights.len()];
        let mut used_right = vec![false; right];
        let mut score = 0.0;
        for &(i, j) in &found.pairs {
            assert!(i < weights.len() && j < right && j != deleted);
            assert!(!used_left[i] && !used_right[j]);
            used_left[i] = true;
            used_right[j] = true;
            let weight = weights[i][j].expect("matching edge must be compatible");
            assert!(weight > 0.0);
            score += weight;
        }
        assert_eq!(found.weight, score);
    }
}

#[test]
fn matching_deletion_families_match_independent_partial_injections() {
    let values = [
        None,
        Some(-3.0),
        Some(0.0),
        Some(0.125),
        Some(1.5),
        Some(4.0),
    ];
    let mut seed = 0x2016_u64;
    for left in 0..=5 {
        for right in 0..=5 {
            for _ in 0..64 {
                let mut weights = vec![vec![None; right]; left];
                for row in &mut weights {
                    for value in row {
                        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                        *value = values[(seed >> 32) as usize % values.len()];
                    }
                }
                check_deletion_family(&weights);
            }
        }
    }
}

#[test]
fn matching_deletion_family_preserves_tiny_edges_and_original_indices() {
    for weights in [
        vec![
            vec![Some(1e150), None, None],
            vec![None, None, Some(5e-200)],
        ],
        vec![
            vec![Some(1e150), None],
            vec![None, None],
            vec![None, Some(5e-200)],
        ],
    ] {
        let family = max_weight_bipartite_matching_with_right_deletions(&weights);
        let last = weights.len() - 1;
        let last_right = weights[0].len() - 1;
        assert_eq!(family.base.pairs, vec![(0, 0), (last, last_right)]);
        let without_big = family.without_right(0).unwrap();
        assert_eq!(without_big.pairs, vec![(last, last_right)]);
        assert_eq!(without_big.weight, 5e-200);
        assert_eq!(
            family,
            max_weight_bipartite_matching_with_right_deletions(&weights)
        );
    }
}

#[test]
fn matching_deletion_family_rejects_invalid_input() {
    for weights in [
        vec![vec![], vec![Some(1.0)]],
        vec![vec![Some(f64::NAN)]],
        vec![vec![Some(f64::INFINITY)]],
    ] {
        assert!(
            std::panic::catch_unwind(|| max_weight_bipartite_matching_with_right_deletions(
                &weights
            ))
            .is_err()
        );
    }
}

#[test]
fn complete_uniform_matchings_attain_cardinality_bounds_with_original_indices() {
    // A complete uniform positive matrix has optimum min(rows, columns) edges.
    // After deletion the bound is min(rows, columns - 1), independently of
    // which optimum the solver chooses. Nonpositive weights select no edges.
    for (left, right) in [(1, 5), (5, 1), (3, 5), (5, 3), (5, 5), (32, 64), (64, 32)] {
        for weight in [-1.0, 0.0, 0.125, 1.0 + 2_f64.powi(-40), 1e-200, 1e150] {
            let matrix = vec![vec![Some(weight); right]; left];
            let check = |matching: &common_subtree_algorithms::WeightedMatching,
                         deleted: Option<usize>| {
                let size = if weight > 0.0 {
                    left.min(right - usize::from(deleted.is_some()))
                } else {
                    0
                };
                assert_eq!(matching.pairs.len(), size);
                assert_eq!(matching.weight, (0..size).fold(0.0, |sum, _| sum + weight));
                let mut seen_left = vec![false; left];
                let mut seen_right = vec![false; right];
                for &(i, j) in &matching.pairs {
                    assert!(i < left && j < right && Some(j) != deleted);
                    assert!(!seen_left[i] && !seen_right[j]);
                    seen_left[i] = true;
                    seen_right[j] = true;
                }
            };
            check(&max_weight_bipartite_matching(&matrix), None);
            let family = max_weight_bipartite_matching_with_right_deletions(&matrix);
            check(&family.base, None);
            for deleted in 0..right {
                check(family.without_right(deleted).unwrap(), Some(deleted));
            }
        }
    }
}

#[test]
fn complete_uniform_matchings_reject_total_overflow() {
    let matrix = vec![vec![Some(f64::MAX); 2]; 2];
    assert!(std::panic::catch_unwind(|| max_weight_bipartite_matching(&matrix)).is_err());
    assert!(
        std::panic::catch_unwind(|| max_weight_bipartite_matching_with_right_deletions(&matrix))
            .is_err()
    );
}
