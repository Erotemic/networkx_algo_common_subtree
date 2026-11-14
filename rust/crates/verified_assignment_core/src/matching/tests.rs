use super::*;

fn independent_maximum(weights: &[Vec<Option<i64>>]) -> i128 {
    fn visit(weights: &[Vec<Option<i64>>], row: usize, used: &mut [bool]) -> i128 {
        if row == weights.len() {
            return 0;
        }
        let mut best = visit(weights, row + 1, used);
        for col in 0..used.len() {
            if !used[col] {
                if let Some(weight) = weights[row][col] {
                    used[col] = true;
                    best = best.max(weight as i128 + visit(weights, row + 1, used));
                    used[col] = false;
                }
            }
        }
        best
    }
    let right = weights.first().map_or(0, Vec::len);
    visit(weights, 0, &mut vec![false; right])
}

fn check(weights: &[Vec<Option<i64>>]) -> PartialMatching {
    let result = max_weight_partial_matching(weights).unwrap();
    let right = weights.first().map_or(0, Vec::len);
    let mut used_left = vec![false; weights.len()];
    let mut used_right = vec![false; right];
    let mut rescored = 0i128;
    let mut previous = None;
    for pair in &result.pairs {
        assert!(pair.left < weights.len());
        assert!(pair.right < right);
        assert!(!used_left[pair.left]);
        assert!(!used_right[pair.right]);
        if let Some(prior) = previous {
            assert!(prior < pair.left);
        }
        previous = Some(pair.left);
        used_left[pair.left] = true;
        used_right[pair.right] = true;
        let weight = weights[pair.left][pair.right].unwrap();
        assert!(weight > 0);
        rescored += weight as i128;
    }
    assert_eq!(result.weight, rescored);
    assert_eq!(result.weight, independent_maximum(weights));
    result
}

#[test]
fn partial_signed_forbidden_empty_and_extreme_cases() {
    check(&[]);
    check(&[vec![], vec![], vec![]]);
    check(&[vec![None]]);
    check(&[vec![Some(i64::MIN)]]);
    check(&[vec![Some(0)]]);
    assert_eq!(check(&[vec![Some(i64::MAX)]]).weight, i64::MAX as i128);
    assert_eq!(
        check(&[
            vec![Some(i64::MAX), Some(i64::MIN)],
            vec![None, Some(i64::MAX)],
        ])
        .weight,
        2 * i64::MAX as i128
    );
    check(&[vec![Some(-3), None, Some(7), Some(7)]]);
    check(&[vec![Some(4)], vec![Some(-9)], vec![None], vec![Some(8)]]);
    assert_eq!(
        max_weight_partial_matching(&[vec![Some(1)], vec![]]),
        Err(MatchingError::NonRectangular)
    );
}

#[test]
fn rectangular_partial_matching_matches_independent_injections() {
    let mut state = 0x75d3_c9a4_9128_ef06u64;
    for left in 0..=6 {
        for right in 0..=6 {
            for _ in 0..12 {
                let mut weights = vec![vec![None; right]; left];
                for row in &mut weights {
                    for value in row {
                        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
                        *value = if state % 5 == 0 {
                            None
                        } else {
                            Some(((state >> 32) % 27) as i64 - 13)
                        };
                    }
                }
                check(&weights);
            }
        }
    }
}
