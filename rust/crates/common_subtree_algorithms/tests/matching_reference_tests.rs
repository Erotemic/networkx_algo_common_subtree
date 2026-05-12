use common_subtree_algorithms::max_weight_bipartite_matching;

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
        assert!(edge_weight > EPS, "reported pair should have positive contribution");
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
        vec![
            vec![Some(-1.0), Some(2.0)],
            vec![Some(2.0), Some(-1.0)],
        ],
    ];
    for weights in cases {
        check_against_bruteforce(weights);
    }
}

#[test]
fn matching_matches_bruteforce_on_deterministic_small_matrices() {
    let values = [None, Some(-3.0), Some(-0.5), Some(0.0), Some(1.0), Some(2.5)];
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
